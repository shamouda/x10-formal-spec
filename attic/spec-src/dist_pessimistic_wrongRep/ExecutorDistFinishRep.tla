------------------------------ MODULE ExecutorDistFinishRep ------------------------------
(****************************************************************************)
(* This specification models a subset of X10 programs to verify the         *) 
(* correctness of the 'finish' construct, which provides a termination      *)
(* detection protocol.                                                      *)
(*                                                                          *)
(* Distributed Finish:                                                      *)
(* --------------------------------                                         *)
(* This module specifies a distributed finish                               *) 
(* implementation that replicates the finish state on two places to allow   *)
(* correct termination when one replica is lost. It implements a buggy      *)
(* replication protocol that was used in X10 release 1.4.2, and was used    *)
(* for proof of concept evaluation in PPoPP14                               *)
(*                                                                          *)
(* PPoPP14 wrong replication:                                               *)
(* --------------------------------                                         *)
(*   Normal path: requester -> master  do();                                *)
(*                master -> backup     do();                                *)
(*                backup -> master     return;                              *)
(*                master -> requester  return;                              *)
(*   If Master died: requestor -> backup do();                              *)
(*                   or                                                     *)
(*                   requestor -> adopter do();   if backup was adopted.    *)
(*   Error: the action do(); may be performed twice on the backup.          *)
(****************************************************************************)
EXTENDS Integers, Sequences, TLC
-----------------------------------------------------------------------------
(****************************************************************************)
(* Constants                                                                *)
(****************************************************************************)
CONSTANTS 
    PLACE,         (* The set of places                                     *)
    PROG_HOME,     (* The home place from which the program starts          *)
    PROG,          (* The input program                                     *)
    MXFINISHES,    (* Maximum finish objects including root and remote      *)
    BACKUP,        (* A function from place to its backup                   *)
    DEPTH          (* Maximum expected depth of the trace                   *)

-----------------------------------------------------------------------------
(****************************************************************************)
(* Variables                                                                *)
(****************************************************************************)
VARIABLES 
    fstates,       (* Array of finish states                                *)
    fmasters,      (* Master finish states                                  *)   
    fbackups,      (* Backup finish states                                  *)
    msgs,          (* The set of inflight messages. We delete a message     *) 
                   (* once received                                         *) 
    pstate,        (* Program state: init -> running -> terminated          *)
    seq,           (* Sequences                                             *)
    thrds,         (* Threads at all places                                 *)
    killed,        (* The set places killed so far                          *)
    pendingAct,    (* Set of activities received at destination place but   *) 
                   (* need permission from the resilient store to run       *)
    runningThrds,  (* Set of running threads in all places                  *)
    blockedThrds,  (* Set of blocked threads in all places                  *)
    waitForMsgs,   (* Messages that blocked threads are waiting for.        *) 
                   (* If the sender dies, we send them with a failed status *)
                   (* to unblock these threads                              *)
    mastersStatus, (* The status of the master stores at each place         *)
    adoptSet,      (* Recovery variable: set of finishes that need adoption *)
    convertSet,    (* Recovery variable: steps to convert dead tasks to 0s  *)
    actionName,    (* Debugging variable: the current action name           *)
    depth          (* Debugging variable: the current depth                 *)
    
Vars == << fstates, msgs, pstate,seq, thrds, 
           killed, pendingAct,  fmasters, fbackups, waitForMsgs, 
           mastersStatus, adoptSet, convertSet,
           blockedThrds, runningThrds, actionName, depth >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Predicate to hide the finish implementation                             *)
(***************************************************************************)
Finish(fid) == INSTANCE DistFinish

C == INSTANCE Commons

GetRootFinishId(fid) ==
   IF fid = C!NoParent THEN C!NotID
   ELSE IF Finish(fid)!IsRoot THEN fid
   ELSE fstates[fid].root

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants  (formulas true in every reachable state.)                   *)
(***************************************************************************)
TypeOK ==
  /\ fstates \in [ C!IDRange ->  C!FinishState] 
  /\ thrds \in  [ PLACE -> [  C!ThreadID ->  C!Thread ] ]
  /\ msgs \subseteq  C!Messages   
  /\ pstate \in { "running", "terminated" }
  /\ PROG \in [ C!BlockID ->  C!Block ]
  /\ PROG_HOME \in PLACE
  /\ seq \in C!Sequences
  /\ killed \subseteq PLACE
  /\ pendingAct \subseteq  C!Activity
  /\ fmasters \in [ C!IDRange -> C!MasterFinish ]
  /\ fbackups \in [ C!IDRange -> C!BackupFinish ]
  /\ BACKUP \in [ PLACE -> PLACE ]
  /\ mastersStatus \in [ PLACE -> C!MasterStatus ]
  /\ adoptSet  \subseteq  C!Adopter
  /\ convertSet \subseteq C!ConvTask
  /\ runningThrds \subseteq C!PlaceThread
  /\ blockedThrds \subseteq C!PlaceThread
  /\ depth \in 0..DEPTH+1
    
StateOK == TRUE
                
MustTerminate ==
  <> ( pstate = "terminated" )
 
-----------------------------------------------------------------------------
(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init == 
  /\ actionName = << "Init" , PROG_HOME >> 
  /\ depth = 0
  /\ fstates = [ r \in  C!IDRange |-> 
                 [ id |->  C!NotID, status |-> "unused", type |->  "NA", 
                   count |-> 0, here |->  C!NotPlace, 
                   parent |->  C!NotID, root |->  C!NotID, isGlobal |-> FALSE,
                   eroot |-> C!NotID ] ]
  /\ fmasters = [ r \in  C!IDRange  |-> 
                        [  id |-> C!NotID,
                    numActive |-> 0,
                         live |-> [ p \in PLACE |-> 0 ],
                      transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                  liveAdopted |-> [ p \in PLACE |-> 0 ],
               transitAdopted |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                     children |-> {},
                  backupPlace |-> C!NotPlace  ,
                   isReleased |-> FALSE ] ]
  /\ fbackups = [ r \in  C!IDRange  |-> 
                        [  id |-> C!NotID,
                         live |-> [ p \in PLACE |-> 0 ],
                      transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                     children |-> {},
                    isAdopted |-> FALSE,
                  adoptedRoot |-> C!NotID,   
                    numActive |-> 0 ] ]
  /\ pstate  = "running"
  /\ mastersStatus = [ p \in PLACE |-> [     status |-> "running", 
                                         lastKilled |-> C!NotPlace ] ] 
  /\ msgs    = {}
  /\ seq     = [ aseq |-> 1, fseq |-> C!FIRST_ID, mseq |-> 1]
  /\ thrds = [ p \in PLACE |->  \*start with one running thread at PROG_HOME
               [ t \in  C!ThreadID |-> 
                   IF p = PROG_HOME /\ t = 0 
                   THEN [ tid |-> t, status |-> "running", 
                          blockingType |-> "NA", 
                          stack |-> <<[  b |-> 0, 
                                         i |-> IF PROG[0].type = "finish" 
                                               THEN C!I_PRE_FIN_ALLOC 
                                               ELSE C!I_START, 
                                       fid |-> C!NoParent ]>> ]
                   ELSE [ tid |-> t, status |-> "idle", 
                          blockingType |-> "NA", 
                          stack |-> <<>> ] ] ]
  /\ runningThrds = { [here |-> PROG_HOME, tid |-> 0 ] }
  /\ blockedThrds = {}
  /\ killed = {}
  /\ pendingAct = {}
  /\ waitForMsgs = {}
  /\ adoptSet = {}
  /\ convertSet = {}
  
-----------------------------------------------------------------------------
(***************************************************************************)
(* Helper Actions                                                          *)
(***************************************************************************)
SetActionNameAndDepth(name) ==
  IF depth = DEPTH THEN TRUE ELSE /\ actionName' = name /\ depth' = depth+1
   
FindPendingActivity(actId) ==
  LET aset == { a \in pendingAct : a.aid  = actId }
  IN IF aset = {} THEN C!NotActivity
     ELSE CHOOSE x \in aset : TRUE
       
FindIdleThread(here) ==
  LET idleThreads == C!PlaceThread \ ( runningThrds \cup blockedThrds )
      tset == { t \in idleThreads : 
                  /\ t.here = here
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "idle" }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE

-----------------------------------------------------------------------------
(***************************************************************************)
(* Program Execution Actions                                               *)
(***************************************************************************)
-----------------------------------------------------------------------------
FindRunningThreadForStartFinish ==
  LET tset == { t \in runningThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "running"
                  /\ LET top == Head(thrds[t.here][t.tid].stack)
                         blk == top.b
                         lstStmt == top.i
                     IN /\ PROG[blk].type = "finish"
                        /\ lstStmt = C!I_PRE_FIN_ALLOC }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE
       
\* Running thread processing the beginning of a finish block
StartFinish == 
  /\ pstate = "running"
  /\ LET pthrd == FindRunningThreadForStartFinish
     IN  /\ pthrd # C!NotPlaceThread
         /\ LET here == pthrd.here
                tid == pthrd.tid
                top == Head(thrds[here][tid].stack)
                tail == Tail(thrds[here][tid].stack)
                lstStmt == top.i
                curStmt == top.i + 1
                blk == top.b
                fid == top.fid
                newFid == seq.fseq
                encRoot ==  C!GetEnclosingRoot(fid, newFid)
            IN /\ SetActionNameAndDepth( << "StartFinish", here >> )
               /\ Finish(seq.fseq)!Alloc(C!ROOT_FINISH, here, fid, newFid)
               /\ C!IncrFSEQ
               /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                                << [ b |-> top.b, 
                                                     i |-> curStmt, 
                                                   fid |-> seq.fseq ]
                                                >> \o tail ]
               /\ IF seq.fseq = C!FIRST_ID
                  THEN /\ fmasters' = fmasters \* will be initialized in transit 
                       /\ fbackups' = fbackups
                  ELSE /\ fmasters' = [fmasters EXCEPT ![encRoot].children = 
                                                                  @ \cup {newFid}]
                       /\ fbackups' = [fbackups EXCEPT ![encRoot].children = 
                                                                  @ \cup {newFid} ]
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, pstate, killed, pendingAct, 
                  msgs, waitForMsgs, runningThrds, blockedThrds>>
                    
-----------------------------------------------------------------------------
FindRunningThreadForScheduleNestedFinish ==
  LET tset == { t \in runningThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "running"
                  /\ LET top == Head(thrds[t.here][t.tid].stack)
                         blk == top.b
                         curStmt == top.i + 1    
                         nested == PROG[blk].stmts[curStmt]     
                     IN  /\ PROG[blk].type \notin { "expr", "kill" }
                         /\ curStmt >= 0  
                         /\ curStmt <= PROG[blk].mxstmt
                         /\ PROG[nested].type = "finish"
                         /\ PROG[nested].dst = t.here  }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE
       
\* Processing a nested finish in the currently running block
ScheduleNestedFinish == 
  /\ pstate = "running"
  /\ LET pthrd == FindRunningThreadForScheduleNestedFinish
     IN   /\ pthrd # C!NotPlaceThread
          /\ LET here == pthrd.here
                 tid == pthrd.tid
                 top == Head(thrds[here][tid].stack)
                 tail == Tail(thrds[here][tid].stack)
                 lstStmt == top.i
                 curStmt == top.i + 1
                 blk == top.b
                 fid == top.fid
                 nested == PROG[blk].stmts[curStmt]
                 newFid == seq.fseq
                 encRoot ==  C!GetEnclosingRoot(fid, newFid)
             IN  /\ SetActionNameAndDepth ( << "ScheduleNestedFinish", here >> )
                 /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                                 << [   b |-> nested, 
                                                        i |-> C!I_START, 
                                                      fid |-> newFid ],
                                                    [   b |-> top.b, 
                                                        i |-> curStmt, 
                                                      fid |-> fid ]
                                                 >> \o tail ]
                 /\ Finish(seq.fseq)!Alloc(C!ROOT_FINISH, here, fid, newFid)
                 /\ C!IncrFSEQ
                 /\ fmasters' = [fmasters EXCEPT ![encRoot].children = 
                                                            @ \cup {newFid}]
                 /\ fbackups' = [fbackups EXCEPT ![encRoot].children = 
                                                            @ \cup {newFid} ]
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, msgs, pstate, waitForMsgs,
                  killed, pendingAct, runningThrds, blockedThrds>>
                    
-----------------------------------------------------------------------------
FindRunningThreadForSpawnLocalAsync ==
  LET tset == { t \in runningThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "running"
                  /\ LET top == Head(thrds[t.here][t.tid].stack)
                         blk == top.b
                         curStmt == top.i + 1      
                         nested == PROG[blk].stmts[curStmt]   
                     IN  /\ PROG[blk].type \notin{ "expr" , "kill" }
                         /\ curStmt >= 0  
                         /\ curStmt <= PROG[blk].mxstmt
                         /\ PROG[nested].type = "async"
                         /\ PROG[nested].dst = t.here
                 }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE
                           
\* Processing a nested local async in the currently running block
SpawnLocalAsync == 
  /\ pstate = "running"
  /\ LET pthrd == FindRunningThreadForSpawnLocalAsync
     IN   /\ pthrd # C!NotPlaceThread
          /\ LET here == pthrd.here
                 tid == pthrd.tid
                 top == Head(thrds[here][tid].stack)
                 tail == Tail(thrds[here][tid].stack)
                 lstStmt == top.i
                 curStmt == top.i + 1
                 blk == top.b
                 fid == top.fid
                 nested == PROG[blk].stmts[curStmt]
                 idle == FindIdleThread(here)
                 act == [ aid |-> seq.aseq, b |-> nested,  fid |-> fid ]
                 stkEntry == [b |-> act.b, i |-> C!I_START , fid |-> act.fid]
             IN  /\ SetActionNameAndDepth ( << "SpawnLocalAsync", here >> )
                 /\ IF act.fid # C!NoParent 
                    THEN Finish(act.fid)!NotifyLocalActivitySpawnAndCreation(here, act)
                    ELSE fstates' = fstates
                 /\ C!IncrASEQ
                 /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                                 <<[   b |-> top.b, 
                                                       i |-> curStmt, 
                                                     fid |-> fid]
                                                 >> \o tail,
                                           ![here][idle.tid].stack = <<stkEntry>>,
                                           ![here][idle.tid].status = "running" ]
                 /\ runningThrds' = runningThrds \cup { [ here |-> here, tid |-> idle.tid] }
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, msgs, pstate, killed, 
                  pendingAct, fmasters, fbackups, waitForMsgs, blockedThrds>>
                    
-----------------------------------------------------------------------------
FindRunningThreadForSpawnRemoteAsync ==
  LET tset == { t \in runningThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "running"
                  /\ LET top == Head(thrds[t.here][t.tid].stack)
                         fid == top.fid
                         blk == top.b
                         curStmt == top.i + 1
                         nested == PROG[blk].stmts[curStmt]
                     IN  /\ PROG[blk].type \notin {"expr", "kill"}
                         /\ fid # C!NoParent
                         /\ curStmt >= 0  
                         /\ curStmt <= PROG[blk].mxstmt
                         /\ PROG[nested].type = "async"
                         /\ PROG[nested].dst # t.here
              }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE
       
\* Processing a nested remote async in the currently running block
SpawnRemoteAsync == 
  /\ pstate = "running"
  /\ LET pthrd == FindRunningThreadForSpawnRemoteAsync
     IN /\ pthrd # C!NotPlaceThread
        /\ LET here == pthrd.here
               tid == pthrd.tid
               top == Head(thrds[here][tid].stack)
               tail == Tail(thrds[here][tid].stack)
               lstStmt == top.i
               curStmt == top.i + 1
               blk == top.b
               fid == top.fid
               root == GetRootFinishId(fid)
               nested == PROG[blk].stmts[curStmt]
               dst == PROG[nested].dst
           IN /\ SetActionNameAndDepth(<< "SpawnRemoteAsync", here, "to", dst >>)
              /\ Finish(fid)!NotifySubActivitySpawn(dst)
              /\ thrds' = [thrds EXCEPT ![here][tid].status = "blocked", 
                                        ![here][tid].blockingType = "AsyncTransit" ]
              /\ blockedThrds' = blockedThrds \cup { [ here |-> here, tid |-> tid ] }
              /\ runningThrds' = runningThrds \ { [ here |-> here, tid |-> tid ] }
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, pstate,killed, pendingAct, 
                  fmasters, fbackups>>
                    
-----------------------------------------------------------------------------
FindRunningThreadForRunExprOrKill ==
  LET tset == { t \in runningThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "running"
                  /\ LET top == Head(thrds[t.here][t.tid].stack)
                         blk == top.b
                         curStmt == top.i + 1
                         nested == PROG[blk].stmts[curStmt]
                     IN  /\ PROG[blk].type \notin { "expr", "kill" }
                         /\ curStmt >= 0  
                         /\ curStmt <= PROG[blk].mxstmt
                         /\ PROG[nested].type \in {"expr", "kill"}  }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE

Kill (dead) ==
  /\ killed' = killed \cup {dead}
  /\ adoptSet' = adoptSet \cup { m \in C!Adopter : 
                                   /\ m.child # C!NotID
                                   /\ m.adopter # C!NotID
                                   /\ m.here # dead
                                   /\ m.here = fstates[m.adopter].here
                                   /\ m.child \in fmasters[m.adopter].children
                                   /\ fbackups[m.child].isAdopted = FALSE
                                   /\ fstates[m.child].here = dead
                                   /\ m.adopter = fstates[m.child].eroot }
  /\ IF adoptSet' = {}
     THEN /\ mastersStatus' = [ mastersStatus EXCEPT ![PROG_HOME].status = "convertDead",
                                                     ![PROG_HOME].lastKilled = dead]
     ELSE /\ mastersStatus' = [ p \in PLACE |-> IF \E m \in adoptSet' : m.here = p 
                                                THEN [     status |-> "seekAdoption", 
                                                       lastKilled |-> dead] 
                                                ELSE [     status |-> "running", 
                                                       lastKilled |-> C!NotPlace] ]
  /\ convertSet' = { t \in C!ConvTask :  
                       /\ t.pl # C!NotPlace
                       /\ t.pl # dead
                       /\ t.pl \notin killed
                       /\ t.fid \in { id \in C!IDRange: 
                                         /\ fmasters[id].id # C!NotID
                                         /\ fstates[id].here # dead }
                       /\ t.here = fstates[t.fid].here } 
  /\ LET delMsgs == { m \in msgs : m.dst = dead  }   \*delete messages going to a dead place  
         wfm == { m \in waitForMsgs: m.dst = dead }  \*delete waitForMsgs to a dead place
      IN /\ msgs' = msgs \ delMsgs            
         /\ waitForMsgs' = waitForMsgs \ wfm

\* Processing a nested expression in the currently running block
RunExprOrKill == 
  /\ pstate = "running"
  /\ LET pthrd == FindRunningThreadForRunExprOrKill
     IN /\ pthrd # C!NotPlaceThread
        /\ LET here == pthrd.here
               tid == pthrd.tid
               top == Head(thrds[here][tid].stack)
               tail == Tail(thrds[here][tid].stack)
               lstStmt == top.i
               curStmt == top.i + 1
               blk == top.b
               fid == top.fid
               nested == PROG[blk].stmts[curStmt]
           IN /\ SetActionNameAndDepth ( << "RunExprOrKill", here, PROG[nested].type >> )
              /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                               << [  b |-> top.b, 
                                                     i |-> curStmt, 
                                                   fid |-> fid ]  
                                               >> \o tail ]
              /\ IF PROG[nested].type = "expr"
                 THEN /\ killed' = killed
                      /\ PROG[nested].dst = here
                      /\ adoptSet' = adoptSet
                      /\ mastersStatus' = mastersStatus
                      /\ convertSet' = convertSet
                      /\ msgs' = msgs
                      /\ waitForMsgs' = waitForMsgs
                 ELSE /\ Kill(PROG[nested].dst)
  /\ UNCHANGED << fstates, pstate, seq, pendingAct, fmasters, fbackups,
                  runningThrds, blockedThrds >>

FindRunningThreadForTerminateAsync ==
  LET tset == { t \in runningThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "running"
                  /\ LET top == Head(thrds[t.here][t.tid].stack)
                         blk == top.b
                         fid == top.fid
                     IN /\ PROG[blk].type = "async"
                        /\ PROG[blk].mxstmt = top.i  }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE
                     
\* Running thread processing the end of an async block
TerminateAsync == 
  /\ pstate = "running"
  /\ LET pthrd == FindRunningThreadForTerminateAsync
     IN /\ pthrd # C!NotPlaceThread
        /\ LET here == pthrd.here
               tid == pthrd.tid
               top == Head(thrds[here][tid].stack)
               blk == top.b
               fid == top.fid
           IN  /\ SetActionNameAndDepth ( << "TerminateAsync", here >> )
               /\ Finish(fid)!NotifyActivityTermination(FALSE)
               /\ thrds' = [thrds EXCEPT ![here][tid].status = "blocked",
                                         ![here][tid].blockingType = "AsyncTerm" ]
               /\ runningThrds' = runningThrds \ { [ here |-> here, tid |-> tid ] }
               /\ blockedThrds' = blockedThrds \cup { [ here |-> here, tid |-> tid ] }
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, pstate,killed, 
                  pendingAct, fmasters, fbackups >>

-----------------------------------------------------------------------------
FindRunningThreadForStopFinish ==
  LET tset == { t \in runningThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "running"
                  /\ LET top == Head(thrds[t.here][t.tid].stack)
                     IN /\ PROG[top.b].type = "finish"
                        /\ PROG[top.b].mxstmt = top.i  }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE
       
\* Running thread processing the end of a finish block and blocking itself
StopFinish == 
  /\ pstate = "running"
  /\ LET pthrd == FindRunningThreadForStopFinish
     IN /\ pthrd # C!NotPlaceThread
        /\ LET here == pthrd.here
               tid == pthrd.tid
               top == Head(thrds[here][tid].stack)
           IN  /\ SetActionNameAndDepth ( << "StopFinish", here >> )
               /\ PROG[top.b].type = "finish"
               /\ PROG[top.b].mxstmt = top.i
               /\ Finish(top.fid)!NotifyActivityTermination(TRUE)
               /\ thrds' = [thrds EXCEPT ![here][tid].status = "blocked",
                                         ![here][tid].blockingType = "FinishEnd" ]
               /\ runningThrds' = runningThrds \ { [ here |-> here, tid |-> tid ] }
               /\ blockedThrds' = blockedThrds \cup { [ here |-> here, tid |-> tid ] }
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, pstate,killed, pendingAct, 
                  fmasters, fbackups>>

--------------------------------------------------------------------------------
RecvAsync == 
  /\ pstate = "running"
  /\ LET msg == C!FindMSG("async")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               pid == msg.fid
               fid == C!GetActiveFID(C!REMOTE_FINISH, here, pid)
               src == msg.src
               blk == msg.b
               newFID == seq.fseq
               activity == [aid |-> seq.aseq, b |-> blk, fid |-> newFID ]
           IN /\ SetActionNameAndDepth ( << "RecvAsync", here >> )
              /\ pid # C!NotID
              /\ fid = C!NotID  \* we don't reuse remote finishes
              /\ src # C!NotPlace
              /\ Finish(activity.fid)!AllocRemoteAndNotifyRemoteActivityCreation(
                                         src, activity, msg, C!REMOTE_FINISH, 
                                         here, (*parent*)pid, (*root*) pid)
              /\ pendingAct' = pendingAct \cup {activity}
              /\ C!IncrAll
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, pstate,thrds, 
                  killed,  fmasters, fbackups, blockedThrds, runningThrds>>

--------------------------------------------------------------------------------
MasterTransitDone ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupTransitDone")
     IN /\ msg # C!NotMessage
        /\ msg.dst \notin killed
        /\ LET here == msg.dst
               mid == msg.mid
               fid == msg.fid
               source == msg.source
               target == msg.target
               src == msg.src
           IN /\ SetActionNameAndDepth ( << "MasterTransitDone", here >> )
              /\ mastersStatus[here].status = "running"
              /\ fstates[fid].here = here
              /\ waitForMsgs' = waitForMsgs \ {[ src |-> src, 
                                                 dst |-> here,  
                                                 fid |-> fid, 
                                              source |-> source,
                                              target |-> target,
                                                type |-> "backupTransitDone"  ]}
              /\ IF source \in killed
                 THEN /\ C!RecvMsg (msg)
                      /\ seq' = seq
                 ELSE /\ C!ReplaceMsg (msg,
                           [   mid |-> seq.mseq, 
                               src |-> here, 
                               dst |-> source,
                            target |-> target,
                               fid |-> fid,
                              type |-> "masterTransitDone",
                         isAdopted |-> FALSE,
                       adoptedRoot |-> C!NotID,
                        adoptedFID |-> C!NotID,
                           success |-> TRUE ]) 
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus,fstates, pstate, 
                  thrds, killed, pendingAct, fmasters, fbackups,
                  blockedThrds, runningThrds >>

MasterLiveDone ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupLiveDone")
     IN /\ msg # C!NotMessage
        /\ msg.dst \notin killed
        /\ LET here == msg.dst 
               mid == msg.mid
               fid == msg.fid
               source == msg.source
               target == msg.target
               src == msg.src
           IN /\ SetActionNameAndDepth ( <<"MasterLiveDone", here>> )
              /\ mastersStatus[here].status = "running"
              /\ fstates[fid].here = here
              /\ IF target \in killed
                 THEN /\ C!RecvMsg (msg)
                      /\ seq' = seq
                 ELSE /\ C!ReplaceMsg (msg,
                                [   mid |-> seq.mseq, 
                                    src |-> here, 
                                    dst |-> target,
                                 target |-> target,
                                    fid |-> fid,
                                    aid |-> msg.aid,
                                   type |-> "masterLiveDone",
                              isAdopted |-> FALSE,
                            adoptedRoot |-> C!NotID,
                                 source |-> source,
                                 submit |-> TRUE,
                                success |-> TRUE ]) 
                      /\ C!IncrMSEQ(1)
              /\ waitForMsgs' = waitForMsgs \ {[ src |-> src, 
                                                 dst |-> here,  
                                                 fid |-> fid, 
                                              source |-> source,
                                              target |-> target,
                                                 aid |-> msg.aid,
                                                type |-> "backupLiveDone"  ]}
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus,
                  fstates, pstate, thrds, killed, pendingAct, fmasters, fbackups,
                  blockedThrds, runningThrds >>

MasterCompletedDone ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupCompletedDone")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
                mid == msg.mid
                fid == msg.fid
             target == msg.target
                src == msg.src
          finishEnd == msg.finishEnd
           IN /\ SetActionNameAndDepth ( << "MasterCompletedDone", here >> )
              /\ mastersStatus[here].status = "running"
              /\ fstates[fid].here = here
              /\ waitForMsgs' = waitForMsgs \ {[ src |-> src, 
                                                 dst |-> here,  
                                                 fid |-> fid, 
                                              target |-> target,
                                           finishEnd |-> finishEnd,
                                                type |-> "backupCompletedDone"  ]}
              /\ IF fmasters[fid].isReleased
                 THEN /\ C!RecvMsg(msg) 
                      /\ seq' = seq 
                      /\ fmasters' = fmasters
                 ELSE /\ IF fmasters[fid].numActive = 0  
                         THEN IF target = here \/ target \in killed
                              THEN /\ C!ReplaceMsg (msg, 
                                               [ mid |-> seq.mseq,
                                                 src |-> here, 
                                                 dst |-> here, 
                                                 fid |-> fid,
                                                type |-> "releaseFinish" ] )
                                   /\ C!IncrMSEQ(1)
                                   /\ fmasters' = [fmasters EXCEPT ![fid].isReleased = TRUE]
                              ELSE /\ C!ReplaceMsgSet (msg, {
                                            [   mid |-> seq.mseq, 
                                                src |-> here, 
                                                dst |-> target,
                                             target |-> target,
                                                fid |-> fid,
                                               type |-> "masterCompletedDone",
                                          finishEnd |-> finishEnd,
                                          isAdopted |-> FALSE,
                                        adoptedRoot |-> C!NotID,
                                          numActive |-> fmasters[fid].numActive,
                                            success |-> TRUE],
                                              [ mid |-> seq.mseq+1,
                                                src |-> here, 
                                                dst |-> here, 
                                                fid |-> fid,
                                               type |-> "releaseFinish" ]}) 
                                   /\ C!IncrMSEQ(2)
                                   /\ fmasters' = [fmasters EXCEPT ![fid].isReleased = TRUE]
                        ELSE IF finishEnd \/ target \in killed
                             THEN /\ C!RecvMsg(msg) 
                                  /\ seq' = seq 
                                  /\ fmasters' = fmasters
                             ELSE /\ C!ReplaceMsg (msg, 
                                         [   mid |-> seq.mseq, 
                                             src |-> here, 
                                             dst |-> target,
                                          target |-> target,
                                             fid |-> fid,
                                       numActive |-> fmasters[fid].numActive,
                                       isAdopted |-> FALSE,
                                     adoptedRoot |-> C!NotID,
                                            type |-> "masterCompletedDone",
                                       finishEnd |-> finishEnd,
                                         success |-> TRUE] )
                                  /\ C!IncrMSEQ(1)
                                  /\ fmasters' = fmasters
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, 
                  fstates, pstate, thrds, killed, pendingAct, fbackups,
                  blockedThrds, runningThrds >>
                  
------------------------------------------------------------------
FindBlockedThreadAsyncTerm ==
  LET tset == { t \in blockedThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "blocked"
                  /\ thrds[t.here][t.tid].blockingType = "AsyncTerm"
                  /\ LET msg == C!FindIncomingMSG(t.here, "masterCompletedDone") 
                         top == Head(thrds[t.here][t.tid].stack) 
                         blk == top.b
                     IN  /\ msg # C!NotMessage
                         /\ PROG[blk].type = "async"
                         /\ PROG[blk].mxstmt = top.i
                         /\ msg.fid = fstates[top.fid].root }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE
       
\* Terminated finish unblocks its thread
UnblockTerminateAsync == 
  /\ pstate = "running"
  /\ LET pthrd == FindBlockedThreadAsyncTerm
     IN /\ pthrd # C!NotPlaceThread
        /\ LET here == pthrd.here
               tid == pthrd.tid
               msg == C!FindIncomingMSG(here, "masterCompletedDone")
               success == msg.success
               top == Head(thrds[here][tid].stack)
               blk == top.b
               fid == top.fid
               root == msg.fid
               rootPlace == C!GetFinishHome(root)
               finishEnd == msg.finishEnd
           IN /\ SetActionNameAndDepth ( << "UnblockTerminateAsync", here >> )
              /\ IF success 
                 THEN /\ waitForMsgs' = waitForMsgs \ {[ src |-> rootPlace, 
                                                         dst |-> here,  
                                                      target |-> here,
                                                         fid |-> root,
                                                   finishEnd |-> finishEnd,
                                                        type |-> "masterCompletedDone"  ]}      
                      /\ IF    Len(thrds[here][tid].stack) = 1
                         THEN  /\ thrds' = [thrds EXCEPT ![here][tid].stack = <<>>,
                                                         ![here][tid].status = "idle" ]
                               /\ blockedThrds' = blockedThrds \ { [ here |-> here, tid |-> tid ] }
                               /\ runningThrds' = runningThrds
                         ELSE  /\ thrds' = [thrds EXCEPT ![here][tid].stack = Tail(@),
                                                         ![here][tid].status = "running" ]
                               /\ blockedThrds' = blockedThrds \ { [ here |-> here, tid |-> tid ] }
                               /\ runningThrds' = runningThrds \cup  { [ here |-> here, tid |-> tid ] }
                      /\ IF  blk = 0
                         THEN pstate' = "terminated"
                         ELSE pstate' = pstate
                      /\ msgs' = msgs
                      /\ seq' = seq
                 ELSE IF msg.isAdopted
                 THEN /\ C!ReplaceMsg ( msg , 
                               [ mid |-> seq.mseq,
                                 src |-> here, 
                                 dst |-> C!GetFinishHome(msg.adoptedRoot), 
                              target |-> here, 
                                 fid |-> msg.adoptedRoot, 
                           finishEnd |-> finishEnd,
                                type |-> "adopterCompleted" ])
                      /\ pstate' = pstate
                      /\ thrds' = thrds
                      /\ waitForMsgs' = waitForMsgs
                      /\ C!IncrMSEQ(1) 
                      /\ blockedThrds' = blockedThrds
                      /\ runningThrds' = runningThrds
                 ELSE /\ C!ReplaceMsg ( msg ,
                               [ mid |-> seq.mseq,
                                 src |-> here, 
                                 dst |-> C!GetBackup(rootPlace), 
                              target |-> msg.target, 
                                 fid |-> root, 
                           finishEnd |-> finishEnd,
                                type |-> "backupCompleted" ])
                      /\ pstate' = pstate
                      /\ thrds' = thrds
                      /\ waitForMsgs' = waitForMsgs
                      /\ C!IncrMSEQ(1) 
                      /\ blockedThrds' = blockedThrds
                      /\ runningThrds' = runningThrds
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, 
                 fstates, killed, pendingAct, fmasters, fbackups>>

--------------------------------------------------------------------------------------
FindBlockedThreadAuthorizeTransitAsync ==
  LET tset == { t \in blockedThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "blocked"
                  /\ thrds[t.here][t.tid].blockingType = "AsyncTransit"
                  /\ C!FindIncomingMSG(t.here, "masterTransitDone") # C!NotMessage  }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE

AuthorizeTransitAsync ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET pthrd == FindBlockedThreadAuthorizeTransitAsync
     IN /\ pthrd # C!NotPlaceThread
        /\ LET here == pthrd.here
               tid == pthrd.tid
               msg == C!FindIncomingMSG(here, "masterTransitDone")
               success == msg.success
               top == Head(thrds[here][tid].stack)
               tail == Tail(thrds[here][tid].stack)
               lstStmt == top.i
               curStmt == top.i + 1
               blk == top.b
               root == msg.fid
               fid == top.fid
               rootPlace == C!GetFinishHome(root)
               nested == PROG[blk].stmts[curStmt]
               asyncDst == PROG[nested].dst
               realFID == IF msg.adoptedFID # C!NotID THEN msg.adoptedFID ELSE root
           IN /\ SetActionNameAndDepth ( << "AuthorizeTransitAsync" , here, "to", 
                                            asyncDst, "success", success >> )
              /\ IF success 
                 THEN /\ msg.src = rootPlace
                      /\ C!ReplaceMsg ( msg ,
                               [ mid |-> seq.mseq,
                                 src |-> here,
                                 dst |-> asyncDst,
                                type |-> "async",
                                 fid |-> realFID,
                                   b |-> nested ])
                      /\ C!IncrMSEQ(1)
                      /\ thrds' = [thrds EXCEPT  ![here][tid].status = "running",
                                                 ![here][tid].stack = 
                                                             <<[  b |-> top.b, 
                                                                  i |-> curStmt, 
                                                                fid |-> fid ]
                                                             >> \o tail ]
                      /\ blockedThrds' = blockedThrds \ { [here |-> here, tid |-> tid] }
                      /\ runningThrds' = runningThrds \cup { [here |-> here, tid |-> tid] }
                      /\ waitForMsgs' = waitForMsgs \ {[ src |-> rootPlace, 
                                                         dst |-> here,  
                                                         fid |-> root,
                                                      target |-> PROG[nested].dst,
                                                        type |-> "masterTransitDone"  ]}
                 ELSE IF msg.isAdopted
                 THEN /\ C!IncrMSEQ(1)
                      /\ thrds' = thrds
                      /\ C!ReplaceMsg ( msg , 
                               [   mid |-> seq.mseq, 
                                   src |-> here, 
                                   dst |-> C!GetFinishHome(msg.adoptedRoot),
                                target |-> msg.target,
                                   fid |-> msg.adoptedRoot,
                            adoptedFID |-> root,
                                  type |-> "adopterTransit" ])
                      /\ waitForMsgs' = waitForMsgs
                      /\ blockedThrds' = blockedThrds
                      /\ runningThrds' = runningThrds
                 ELSE /\ C!IncrMSEQ(1)
                      /\ thrds' = thrds
                      /\ C!ReplaceMsg ( msg ,
                               [   mid |-> seq.mseq, 
                                   src |-> here, 
                                   dst |-> C!GetBackup(rootPlace),
                                source |-> here,
                                target |-> msg.target,
                                   fid |-> fid,
                                  type |-> "backupTransit" ])
                      /\ waitForMsgs' = waitForMsgs
                      /\ blockedThrds' = blockedThrds
                      /\ runningThrds' = runningThrds
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, 
                  killed, pendingAct, fmasters, fbackups>>
                   
AuthorizeReceivedAsync == 
  /\ pstate = "running"
  /\ pendingAct # {}
  /\ msgs # {}
  /\ LET msg == C!FindMSG("masterLiveDone")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               actId == msg.aid
               activity == FindPendingActivity(actId)
               root == msg.fid
               submit == msg.submit
               success == msg.success
               rootPlace == C!GetFinishHome(root)
           IN /\ SetActionNameAndDepth ( << "AuthorizeReceivedAsync", here >> )
              /\ activity # C!NotActivity
              /\ fstates[activity.fid].here = here
              /\ waitForMsgs' = waitForMsgs \ {[ src |-> rootPlace, 
                                                 dst |-> here,  
                                                 fid |-> root,
                                                 aid |-> actId,
                                              source |-> msg.source,
                                                type |-> "masterLiveDone"  ]}
              /\ IF success 
                 THEN  /\ C!RecvMsg ( msg )
                       /\ pendingAct' = pendingAct \ {activity}
                       /\ seq' = seq
                       /\ IF submit
                          THEN LET idleThrd == FindIdleThread(here)
                                   stkEntry == [b |-> activity.b, i |-> -1 , fid |-> activity.fid]
                               IN  /\ thrds' = [thrds EXCEPT ![here][idleThrd.tid].stack = <<stkEntry>>, \*immediate push to an idle thread
                                                             ![here][idleThrd.tid].status = "running" ]
                                   /\ runningThrds' = runningThrds \cup { [ here |-> here, tid |-> idleThrd.tid] }
                          ELSE /\ thrds' = thrds 
                               /\ runningThrds' = runningThrds
                 ELSE IF msg.isAdopted
                 THEN /\ pendingAct' = pendingAct
                      /\ thrds' = thrds 
                      /\ runningThrds' = runningThrds
                      /\ C!ReplaceMsg( msg , 
                               [ mid |-> seq.mseq,
                                 src |-> here,
                              source |-> msg.source,
                              target |-> here, 
                                 dst |-> C!GetFinishHome(msg.adoptedRoot), 
                                 fid |-> msg.adoptedRoot, \* always refer to the root state 
                                 aid |-> actId,
                                type |-> "adopterLive" ] )
                      /\ C!IncrMSEQ(1)
                 ELSE /\ pendingAct' = pendingAct
                      /\ thrds' = thrds 
                      /\ runningThrds' = runningThrds
                      /\ C!ReplaceMsg ( msg , 
                               [   mid |-> seq.mseq, 
                                   src |-> here, 
                                   dst |-> C!GetBackup(rootPlace),
                                source |-> msg.source,
                                target |-> msg.target,
                                   fid |-> msg.fid,
                                   aid |-> actId,
                                  type |-> "backupLive" ])
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus,
                  fstates, pstate, killed, fmasters, fbackups,
                  blockedThrds>>

--------------------------------------------------------------------------------
FindBlockedThreadStopFinish(here, root) ==
  LET tset == { t \in blockedThrds : 
                  /\ here = t.here
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "blocked"
                  /\ thrds[t.here][t.tid].blockingType = "FinishEnd"
                  /\ LET top == Head(thrds[t.here][t.tid].stack)
                         fid == top.fid
                         blk == top.b
                     IN  /\ PROG[blk].type = "finish"
                         /\ PROG[blk].mxstmt = top.i
                         /\ root = fid  }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE
       
\* Terminated finish unblocks its thread
UnblockStopFinish(here, tid, fid, blk) == 
  /\ IF    Len(thrds[here][tid].stack) = 1
     THEN  /\ thrds' = [thrds EXCEPT ![here][tid].stack = <<>>,
                                     ![here][tid].status = "idle" ]
           /\ blockedThrds' = blockedThrds \ { [ here |-> here, tid |-> tid ] }
           /\ runningThrds' = runningThrds
     ELSE  /\ thrds' = [thrds EXCEPT ![here][tid].stack = Tail(@),
                                     ![here][tid].status = "running" ]
           /\ blockedThrds' = blockedThrds \ { [ here |-> here, tid |-> tid ] }
           /\ runningThrds' = runningThrds \cup { [ here |-> here, tid |-> tid ] }
  /\ IF  blk = 0
     THEN pstate' = "terminated"
     ELSE pstate' = pstate 
                   
ReleaseRootFinish == 
  /\ pstate = "running"
  /\ msgs # {}
  /\ blockedThrds # {}
  /\ LET msg == C!FindMSG( "releaseFinish" )
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               root == msg.fid
               pthrd == FindBlockedThreadStopFinish(here, root)
               tid == pthrd.tid
               top == Head(thrds[here][tid].stack)
               blk == top.b
           IN /\ msg # C!NotMessage
              /\ SetActionNameAndDepth ( << "ReleaseRootFinish", here >> )
              /\ C!RecvMsg ( msg )
              /\ fstates' = [fstates EXCEPT ![root].status = "forgotten"]
              /\ waitForMsgs' = waitForMsgs \ {[ src |-> here, 
                                                 dst |-> here,
                                              target |-> here,    
                                                 fid |-> root,
                                                type |-> "masterCompletedDone",
                                           finishEnd |-> TRUE  ],
                                           [ src |-> here, 
                                                 dst |-> here,
                                              target |-> here,    
                                                 fid |-> root,
                                                type |-> "masterCompletedDone",
                                           finishEnd |-> FALSE  ]}
              /\ UnblockStopFinish(here, tid, root, blk)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, seq, 
                  killed, pendingAct,  fmasters, fbackups>>

-------------------------------------------------------------------------------
(***************************************************************************)
(* Finish master replica actions                                           *)
(***************************************************************************)    
MasterTransit ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("masterTransit")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               target == msg.target
               backupPlace == C!GetBackup(here)
           IN /\ SetActionNameAndDepth ( << "MasterTransit", here >> )
              /\ mastersStatus[here].status = "running"
              /\ src # C!NotPlace
              /\ fid # C!NotID
              /\ fstates[fid].here = here
              /\ IF fmasters[fid].id = C!NotID
                 THEN fmasters' = [fmasters EXCEPT ![fid].id = fid,
                                                   ![fid].backupPlace = backupPlace,
                                                   ![fid].transit[src][target] = @ + 1,
                                                   ![fid].numActive  =  @ + 2,
                                                   ![fid].live[here] = 1 ]
                 ELSE fmasters' = [fmasters EXCEPT ![fid].transit[src][target] = @ + 1,
                                                   ![fid].numActive = @ + 1 ]
              /\ C!ReplaceMsg (msg, [   mid |-> seq.mseq, 
                            src |-> here, 
                            dst |-> backupPlace,
                         source |-> src,
                         target |-> target,
                            fid |-> fid,
                           type |-> "backupTransit" ]) 
              /\ C!IncrMSEQ(1)
              /\ waitForMsgs' = waitForMsgs \cup {[ src |-> backupPlace, 
                                               dst |-> here,  
                                               fid |-> fid, 
                                            source |-> src,
                                            target |-> target,
                                              type |-> "backupTransitDone"  ]}
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus,fstates, pstate, 
                  thrds, killed, pendingAct, fbackups, blockedThrds, runningThrds >>
----------------------------------------------------------------------------------                    
MasterLive ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("masterLive")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               backupPlace == C!GetBackup(here)
           IN /\ SetActionNameAndDepth ( << "MasterLive", here >> )
              /\ fid # C!NotID
              /\ backupPlace # C!NotPlace
              /\ fstates[fid].here = here
              /\ mastersStatus[here].status = "running"
              /\ LET source == msg.source
                     target == msg.target
                     submit == ~ (source \in killed \/ target \in killed)
                 IN IF submit
                    THEN /\ fmasters[fid].transit[source][target] > 0
                         /\ fmasters' = [fmasters EXCEPT ![fid].transit[source][target] = @ - 1,
                                                         ![fid].live[target] = @ + 1 ]
                         /\ C!ReplaceMsg (msg,
                                        [   mid |-> seq.mseq, 
                                            src |-> here, 
                                            dst |-> backupPlace,
                                         source |-> source,
                                         target |-> target,
                                            fid |-> fid,
                                            aid |-> msg.aid,
                                           type |-> "backupLive" ]) 
                         /\ C!IncrMSEQ(1)
                         /\ waitForMsgs' = waitForMsgs \cup {[ src |-> backupPlace, 
                                                               dst |-> here,  
                                                               fid |-> fid, 
                                                            source |-> source,
                                                            target |-> target,
                                                               aid |-> msg.aid,
                                                              type |-> "backupLiveDone"  ]}
                    ELSE /\ fmasters' = fmasters
                         /\ waitForMsgs' = waitForMsgs
                         /\ C!ReplaceMsg (msg,
                                        [   mid |-> seq.mseq, 
                                            src |-> here, 
                                            dst |-> target,
                                         source |-> source,
                                         target |-> target,
                                            fid |-> fid,
                                            aid |-> msg.aid,
                                           type |-> "masterLiveDone",
                                      isAdopted |-> FALSE,
                                    adoptedRoot |-> C!NotID,
                                           submit |-> FALSE,
                                           success |-> TRUE ]) 
                         /\ C!IncrMSEQ(1)
   /\ UNCHANGED << convertSet, adoptSet, mastersStatus, 
                   fstates, pstate, thrds, killed, pendingAct, fbackups,
                   blockedThrds, runningThrds >>

----------------------------------------------------------------------------------
MasterCompleted ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("masterCompleted")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               mid == msg.mid
               fid == msg.fid
               src == msg.src
               target == msg.target
               backupPlace == C!GetBackup(here)
               finishEnd == msg.finishEnd
           IN /\ SetActionNameAndDepth ( <<"MasterCompleted", here>> )
              /\ backupPlace # C!NotPlace
              /\ fid # C!NotID
              /\ fstates[fid].here = here
              /\ mastersStatus[here].status = "running"
              /\ fmasters[fid].live[target] > 0
              /\ fmasters[fid].numActive > 0
              /\ fmasters' = [fmasters EXCEPT ![fid].live[target] = @ - 1,
                                              ![fid].numActive    = @ - 1 ]
              /\ C!ReplaceMsg (msg, 
                        [ mid |-> seq.mseq,
                          src |-> here, 
                          dst |-> backupPlace, 
                       target |-> target, 
                          fid |-> fid,
                    finishEnd |-> finishEnd,
                         type |-> "backupCompleted" ]) 
              /\ C!IncrMSEQ(1)
              /\ waitForMsgs' = waitForMsgs \cup {[ src |-> backupPlace, 
                                                    dst |-> here,  
                                                    fid |-> fid, 
                                                 target |-> target,
                                              finishEnd |-> finishEnd,
                                                   type |-> "backupCompletedDone"  ]}
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus,fstates, pstate,  
                  thrds, killed, pendingAct, fbackups, blockedThrds, runningThrds >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Adopting Finish master replica actions                                  *)
(***************************************************************************)
AdopterTransit ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("adopterTransit")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               target == msg.target
               backupPlace == C!GetBackup(here)
           IN /\ SetActionNameAndDepth ( << "AdopterTransit", here >> )
              /\ mastersStatus[here].status = "running"
              /\ fid # C!NotID
              /\ fstates[fid].here = here   \*FIXME: the code doesn't check if src or target at alive!!!!
              /\ fmasters' = [fmasters EXCEPT ![fid].transitAdopter[src][target] = @ + 1,
                                              ![fid].numActive = @ + 1 ]
              /\ C!ReplaceMsg (msg,
                               [   mid |-> seq.mseq, 
                                   src |-> here, 
                                   dst |-> src,
                                target |-> target,
                                   fid |-> fid,
                                  type |-> "masterTransitDone",
                             isAdopted |-> FALSE,
                           adoptedRoot |-> C!NotID,
                           adoptedFID  |-> C!NotID,
                               success |-> TRUE ])  
              /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus,fstates, pstate, 
                   thrds, killed, pendingAct, fbackups,
                   blockedThrds, runningThrds >>

AdopterLive ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("adopterLive")  
     IN /\ msg # C!NotMessage
        /\ msg.dst \notin killed
        /\ LET here == msg.dst
               fid == msg.fid
               backupPlace == C!GetBackup(here)
           IN /\ SetActionNameAndDepth ( << "AdopterLive", here >> )
              /\ fid # C!NotID
              /\ backupPlace # C!NotPlace
              /\ fstates[fid].here = here
              /\ mastersStatus[here].status = "running"
              /\ LET source == msg.source
                     target == msg.target
                     submit == ~ (source \in killed \/ target \in killed)
                 IN /\ IF submit
                       THEN  /\ fmasters[fid].transitAdopted[source][target] > 0
                             /\ fmasters' = [fmasters EXCEPT ![fid].transitAdopted[source][target] = @ - 1,
                                                             ![fid].liveAdopted[target] = @ + 1 ]
                       ELSE fmasters' = fmasters
                    /\ C!ReplaceMsg (msg,
                                    [   mid |-> seq.mseq, 
                                        src |-> here, 
                                        dst |-> target,
                                     source |-> source,
                                     target |-> target,
                                        fid |-> fid,
                                        aid |-> msg.aid,
                                       type |-> "masterLiveDone",
                                  isAdopted |-> FALSE,
                                adoptedRoot |-> C!NotID,
                                     submit |-> submit,
                                    success |-> TRUE ]) 
                    /\ C!IncrMSEQ(1) 
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, waitForMsgs,
                  thrds, killed, pendingAct, fbackups, blockedThrds, runningThrds >>

AdopterCompleted ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("adopterCompleted")
     IN /\ msg # C!NotMessage
        /\ msg.dst \notin killed
        /\ LET here == msg.dst
               mid == msg.mid
               fid == msg.fid
               src == msg.src
               target == msg.target
               backupPlace == C!GetBackup(here)
               finishEnd == msg.finishEnd
           IN /\ SetActionNameAndDepth ( <<"AdopterCompleted", here>> )
              /\ mastersStatus[here].status = "running"
              /\ backupPlace # C!NotPlace
              /\ fid # C!NotID
              /\ fstates[fid].here = here
              /\ fmasters[fid].liveAdopted[target] > 0
              /\ fmasters[fid].numActive > 0
              /\ fmasters' = [fmasters EXCEPT ![fid].liveAdopted[target] = @ - 1,
                                              ![fid].numActive           = @ - 1 ]
              /\ IF fmasters'[fid].numActive = 0  
                 THEN /\ C!ReplaceMsgSet (msg, {
                                [   mid |-> seq.mseq, 
                                    src |-> here, 
                                    dst |-> target,
                                 target |-> target,
                                    fid |-> fid,
                                   type |-> "masterCompletedDone",
                              finishEnd |-> finishEnd,
                              isAdopted |-> FALSE,
                            adoptedRoot |-> C!NotID,
                              numActive |-> fmasters[fid].numActive,
                                success |-> TRUE],
                                  [ mid |-> seq.mseq+1,
                                    src |-> here, 
                                    dst |-> here, 
                                    fid |-> fid,
                                   type |-> "releaseFinish" ]}) 
                      /\ C!IncrMSEQ(2)
                 ELSE /\ C!ReplaceMsg (msg, 
                                [   mid |-> seq.mseq, 
                                    src |-> here, 
                                    dst |-> target,
                                 target |-> target,
                                    fid |-> fid,
                              numActive |-> fmasters[fid].numActive,
                              isAdopted |-> FALSE,
                            adoptedRoot |-> C!NotID,
                                   type |-> "masterCompletedDone",
                              finishEnd |-> finishEnd,
                                success |-> TRUE] )
                      /\ C!IncrMSEQ(1)
   /\ UNCHANGED << convertSet, adoptSet, mastersStatus,
                   fstates, pstate, thrds, killed, pendingAct, fbackups, 
                   waitForMsgs, blockedThrds, runningThrds >>
-------------------------------------------------------------------------------
(***************************************************************************)
(* Finish backup replica actions                                           *)
(***************************************************************************)
BackupTransit ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupTransit")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               source == msg.source
               target == msg.target
               type == IF src = fstates[fid].here 
                       THEN "backupTransitDone" 
                       ELSE "masterTransitDone"
           IN /\ SetActionNameAndDepth ( << "BackupTransit", here >> )
              /\ fmasters[fid].backupPlace = here
              /\ IF fbackups[fid].isAdopted
                 THEN /\ fbackups' = fbackups
                      /\ C!ReplaceMsg ( msg,
                                         [   mid |-> seq.mseq,
                                             src |-> here,
                                             dst |-> src,
                                          target |-> target,
                                          source |-> source,
                                             fid |-> fid,
                                            type |-> type,
                                       isAdopted |-> TRUE,
                                     adoptedRoot |-> fbackups[fid].adoptedRoot,
                                     adoptedFID  |-> fid,
                                         success |-> FALSE ])
                      /\ C!IncrMSEQ(1)
                 ELSE /\ IF fbackups[fid].id = C!NotID
                         THEN fbackups' = [ fbackups EXCEPT ![fid].id = fid,
                                                            ![fid].transit[source][target] = @+1,
                                                            ![fid].live[src] = 1,
                                                            ![fid].numActive  =  @ + 2 ]
                         ELSE fbackups' = [ fbackups EXCEPT ![fid].transit[source][target] = @ + 1,
                                                            ![fid].numActive  =  @ + 1 ]
                      /\ C!ReplaceMsg ( msg,
                                         [   mid |-> seq.mseq,
                                             src |-> here,
                                             dst |-> src,
                                          target |-> target,
                                          source |-> source,
                                             fid |-> fid,
                                            type |-> type,
                                       isAdopted |-> FALSE,
                                     adoptedRoot |-> C!NotID,
                                     adoptedFID  |-> C!NotID,
                                         success |-> TRUE ])
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, 
                  thrds, killed, pendingAct, fmasters, waitForMsgs,
                  blockedThrds, runningThrds >>

BackupLive ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupLive")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               source == msg.source
               target == msg.target
               type == IF src = fstates[fid].here 
                       THEN "backupLiveDone" 
                       ELSE "masterLiveDone"
           IN /\ SetActionNameAndDepth ( << "BackupLive", here >> )
              /\ fmasters[fid].backupPlace = here
              /\ IF fbackups[fid].isAdopted
                 THEN /\ fbackups' = fbackups
                      /\ C!ReplaceMsg ( msg,
                                      [   mid |-> seq.mseq, 
                                          src |-> here,
                                          dst |-> src,
                                       target |-> target,
                                       source |-> source,
                                          fid |-> fid,
                                          aid |-> msg.aid,
                                         type |-> type,
                                    isAdopted |-> TRUE,
                                  adoptedRoot |-> fbackups[fid].adoptedRoot,
                                      success |-> FALSE,
                                       submit |-> FALSE ])
                      /\ C!IncrMSEQ(1) 
                 ELSE /\ fbackups[fid].transit[source][target] > 0
                      /\ fbackups' = [ fbackups EXCEPT ![fid].transit[source][target] = @ - 1,
                                                       ![fid].live[target] = @ + 1 ]
                      /\ C!ReplaceMsg ( msg,
                                      [   mid |-> seq.mseq, 
                                          src |-> here,
                                          dst |-> src,
                                       target |-> target,
                                       source |-> source,
                                          fid |-> fid,
                                          aid |-> msg.aid,
                                         type |-> type,
                                    isAdopted |-> FALSE,
                                  adoptedRoot |-> C!NotID,
                                      success |-> TRUE,
                                       submit |-> TRUE ])
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, fstates, pstate, thrds, pendingAct, fmasters, waitForMsgs,
                   blockedThrds, runningThrds, killed,  adoptSet, mastersStatus>>

BackupCompleted ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupCompleted")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               target == msg.target
               type == IF src = fstates[fid].here
                       THEN "backupCompletedDone"
                       ELSE "masterCompletedDone"
               finishEnd == msg.finishEnd
           IN /\ fmasters[fid].backupPlace = here
              /\ SetActionNameAndDepth ( << "BackupCompleted", here >> )
              /\ IF fbackups[fid].isAdopted
                 THEN /\ fbackups' = fbackups
                      /\ C!ReplaceMsg (msg,
                                 [   mid |-> seq.mseq,
                                     src |-> here,
                                     dst |-> src,
                                  target |-> target,
                               numActive |-> 1000,
                                     fid |-> fid,
                                    type |-> type,
                               isAdopted |-> TRUE,
                             adoptedRoot |-> fbackups[fid].adoptedRoot,
                               finishEnd |-> finishEnd,
                                 success |-> FALSE]) 
                      /\ C!IncrMSEQ(1) 
                 ELSE /\ fbackups[fid].live[target] > 0
                      /\ fbackups[fid].numActive > 0
                      /\ fbackups' = [ fbackups EXCEPT ![fid].live[target] = @ - 1,
                                                       ![fid].numActive    = @ - 1 ]
                      /\ C!ReplaceMsg (msg,
                                 [   mid |-> seq.mseq, 
                                     src |-> here, 
                                     dst |-> src,
                                  target |-> target,
                               numActive |-> 1000,
                                     fid |-> fid,
                                    type |-> type,
                               finishEnd |-> finishEnd,
                                 success |-> TRUE])
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate,
                  thrds, killed, pendingAct, fmasters, waitForMsgs,
                  blockedThrds, runningThrds >>

------------------------------------------------------------------------------
(***************************************************************************)
(* Finish adoption actions for recovery                                    *)
(***************************************************************************)
GetAdoptionSeeker ==
  IF adoptSet = {} THEN C!NotAdopter
  ELSE CHOOSE m \in adoptSet : mastersStatus[m.here].status = "seekAdoption"
    
SeekAdoption ==
  /\ pstate = "running"
  /\ \E p \in PLACE : mastersStatus[p].status = "seekAdoption"
  /\ LET pair == GetAdoptionSeeker
     IN /\ pair # C!NotAdopter
        /\ pair.here \notin killed
        /\ LET here == pair.here
               adopter == pair.adopter
               child == pair.child
           IN /\ SetActionNameAndDepth ( <<"SeekAdoption", here>> )
              /\ fbackups' = [ fbackups EXCEPT ![child].isAdopted = TRUE,
                                               ![child].adoptedRoot = adopter ]
              /\ fmasters' = [ fmasters EXCEPT ![adopter].children = fmasters[adopter].children \ {child},
                                               ![adopter].liveAdopted = 
                                                  [ p \in PLACE |-> fmasters[adopter].liveAdopted[p] 
                                                                   + fbackups[child].live[p] ],
                                               ![adopter].transitAdopted = 
                                                  [ p \in PLACE |-> 
                                                    [ q \in PLACE |-> fmasters[adopter].transitAdopted[p][q] 
                                                                     + fbackups[child].transit[p][q] ] ],
                                               ![adopter].numActive = @ + fbackups[child].numActive ] 
              /\ adoptSet' = adoptSet \ {pair}
              /\ IF \E m \in adoptSet' : m.here = here
                 THEN /\ mastersStatus' = mastersStatus
                 ELSE /\ mastersStatus' = [ mastersStatus EXCEPT ![here].status = "convertDead"]
   /\ UNCHANGED << fstates, msgs, pstate,seq, thrds, killed, pendingAct,  waitForMsgs, 
                   convertSet, blockedThrds, runningThrds >> 

------------------------------------------------------------------------------------------------
GetConvertSeeker ==
  IF convertSet = {} THEN C!NotConvTask
  ELSE CHOOSE m \in convertSet : mastersStatus[m.here].status = "convertDead"
       
ConvertDeadActivities ==
  /\ pstate = "running"
  /\ \E p \in PLACE : mastersStatus[p].status = "convertDead"
  /\ LET convSeeker == GetConvertSeeker
     IN /\ convSeeker # C!NotConvTask
        /\ convSeeker.here \notin killed
        /\ LET here == convSeeker.here
                pl == convSeeker.pl
                fid == convSeeker.fid
                dead == mastersStatus[here].lastKilled 
           IN /\ SetActionNameAndDepth ( << "ConvertDeadActivities", here >> )
              /\ convertSet' = convertSet \ {convSeeker}
              /\ fmasters[fid].transitAdopted[pl][dead] >= 0
              /\ fmasters[fid].transitAdopted[dead][pl] >= 0
              /\ fmasters[fid].liveAdopted[dead] >= 0
              /\ fmasters' = [ fmasters EXCEPT ![fid].numActive = 
                                                   @ - fmasters[fid].transit[pl][dead] 
                                                     - fmasters[fid].transit[dead][pl]
                                                     - fmasters[fid].transitAdopted[pl][dead] 
                                                     - fmasters[fid].transitAdopted[dead][pl]
                                                     - fmasters[fid].live[dead]
                                                     - fmasters[fid].liveAdopted[dead],
                                               ![fid].transit[pl][dead]  = 0,
                                               ![fid].transitAdopted[pl][dead]  = 0,
                                               ![fid].transit[dead][pl]  = 0,
                                               ![fid].transitAdopted[dead][pl]  = 0,
                                               ![fid].live[dead] = 0,
                                               ![fid].liveAdopted[dead] = 0 ]
              /\ IF fmasters'[fid].numActive = 0
                 THEN /\ C!SendMsg ( [ mid |-> seq.mseq,
                                       src |-> here, 
                                       dst |-> here, 
                                       fid |-> fid,
                                      type |-> "releaseFinish" ] )
                      /\ C!IncrMSEQ(1)
                 ELSE /\ msgs' = msgs
                      /\ seq' = seq
              /\ IF  \E m \in convertSet' : m.here = here
                 THEN  mastersStatus' = mastersStatus
                 ELSE  mastersStatus' = [ mastersStatus EXCEPT ![here].status = "running"]
  /\ UNCHANGED << fstates, pstate, thrds, killed, pendingAct,  fbackups, waitForMsgs, 
                   adoptSet,  blockedThrds, runningThrds >>
                   
----------------------------------------------------------------------------------
FindWaitForMSG ==
  LET mset == { m \in waitForMsgs : 
                  /\ m.src  \in killed
                  /\ m.dst  \notin killed
                  /\ m.src \in killed }
  IN IF mset = {} THEN C!NotMessage
     ELSE CHOOSE x \in mset : TRUE
              
SimulateFailedResponse == 
  /\ pstate = "running"
  /\ killed # {}
  /\ waitForMsgs # {}
  /\ LET msg == FindWaitForMSG
     IN   /\ msg # C!NotMessage
          /\ LET dead == msg.src
                 here == msg.dst
                 delMsgs == { m \in msgs : m.dst = dead  }
                 wfm == { m \in waitForMsgs: m.dst = dead }
             IN  /\ SetActionNameAndDepth ( <<"SimulateFailedResponse", here>> )
                 /\ waitForMsgs' = (waitForMsgs \ wfm ) \ { msg }
                 /\ C!IncrMSEQ(1)
                 /\ IF msg.type = "masterLiveDone"
                    THEN IF  ~ (\E m \in msgs: \*message has been sent already
                                     /\ m.type = msg.type /\ m.src = msg.src 
                                     /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                     /\ m.aid = msg.aid /\ m.success )
                         THEN /\ msgs' = (msgs \ delMsgs) \cup {
                                        [   mid |-> seq.mseq, 
                                            src |-> msg.src, 
                                            dst |-> msg.dst,
                                         source |-> msg.source,
                                         target |-> msg.dst,
                                            fid |-> msg.fid,
                                            aid |-> msg.aid,
                                           type |-> "masterLiveDone",
                                      isAdopted |-> FALSE,
                                    adoptedRoot |-> C!NotID,
                                         submit |-> FALSE,
                                        success |-> FALSE ]}
                         ELSE /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "masterCompletedDone"
                    THEN IF  ~ (\E m \in msgs: \*message has been sent already
                                     /\ m.type = msg.type /\ m.src = msg.src 
                                     /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                     /\ m.success )
                         THEN  /\ msgs' = (msgs \ delMsgs) \cup {
                                        [   mid |-> seq.mseq,
                                            src |-> msg.src,
                                            dst |-> msg.dst,
                                         target |-> msg.target,
                                            fid |-> msg.fid,
                                      numActive |-> 1000,
                                      isAdopted |-> FALSE,
                                    adoptedRoot |-> C!NotID,
                                           type |-> "masterCompletedDone",
                                      finishEnd |-> msg.finishEnd,
                                        success |-> FALSE] }
                         ELSE  /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "masterTransitDone"
                    THEN IF ~ (\E m \in msgs: \*message has been sent already
                                    /\ m.type = msg.type /\ m.src = msg.src 
                                    /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                    /\ m.success )
                         THEN  /\ msgs' = (msgs \ delMsgs) \cup {
                                        [   mid |-> seq.mseq,
                                            src |-> msg.src,
                                            dst |-> msg.dst,
                                         target |-> msg.target,
                                            fid |-> msg.fid,
                                           type |-> "masterTransitDone",
                                      isAdopted |-> FALSE,
                                    adoptedRoot |-> C!NotID,
                                    adoptedFID  |-> C!NotID,
                                        success |-> FALSE ] }
                         ELSE  /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "backupCompletedDone"
                    THEN IF ~ (\E m \in msgs: \*message has been sent already 
                                    /\ m.type = msg.type /\ m.src = msg.src 
                                    /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                    /\ m.success )
                         THEN /\ msgs' = (msgs \ delMsgs) \cup {
                                        [   mid |-> seq.mseq,
                                            src |-> msg.src,
                                            dst |-> msg.dst,
                                         target |-> msg.target,
                                      numActive |-> 1000,
                                            fid |-> msg.fid,
                                           type |-> "backupCompletedDone",
                                      finishEnd |-> msg.finishEnd,
                                        success |-> FALSE ] }
                         ELSE /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "backupLiveDone"    
                    THEN IF  ~ (\E m \in msgs: \*message has been sent already
                                     /\ m.type = msg.type /\ m.src = msg.src 
                                     /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                     /\ m.source = msg.source /\ m.success )
                         THEN /\ msgs' = (msgs \ delMsgs) \cup {
                                        [   mid |-> seq.mseq,
                                            src |-> msg.src,
                                            dst |-> msg.dst,
                                         target |-> msg.target,
                                         source |-> msg.source,
                                            fid |-> msg.fid,
                                            aid |-> msg.aid,
                                           type |-> "backupLiveDone",
                                      isAdopted |-> FALSE,
                                    adoptedRoot |-> C!NotID,
                                        success |-> FALSE,
                                         submit |-> FALSE ]}
                         ELSE /\ msgs' = (msgs \ delMsgs)
                    ELSE IF msg.type = "backupTransitDone"
                    THEN IF  ~ (\E m \in msgs: \*message has been sent already
                                     /\ m.type = msg.type /\ m.src = msg.src 
                                     /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                     /\ m.target = msg.target /\ m.success )
                         THEN /\ msgs' = (msgs \ delMsgs) \cup {
                                        [   mid |-> seq.mseq,
                                            src |-> msg.src,
                                            dst |-> msg.dst,
                                         target |-> msg.target,
                                         source |-> msg.source,
                                            fid |-> msg.fid,
                                           type |-> "backupTransitDone",
                                      isAdopted |-> FALSE,
                                    adoptedRoot |-> C!NotID,
                                    adoptedFID  |-> C!NotID,
                                        success |-> FALSE ] }
                         ELSE /\ msgs' = (msgs \ delMsgs)
                    ELSE FALSE
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, 
                  thrds, killed, pendingAct,  fmasters, fbackups, 
                  blockedThrds, runningThrds >>
-------------------------------------------------------------------------------
(***************************************************************************)
(* Predicate enumerating all possible next actions                         *)
(***************************************************************************)    
Next ==
  \/ RecvAsync
  \/ ReleaseRootFinish     
  \/ AuthorizeReceivedAsync
  \/ BackupTransit
  \/ BackupLive 
  \/ BackupCompleted
  \/ MasterTransit
  \/ MasterLive
  \/ MasterCompleted
  \/ MasterTransitDone     
  \/ MasterLiveDone
  \/ MasterCompletedDone
  \/ AdopterTransit
  \/ AdopterLive
  \/ AdopterCompleted
  \/ SeekAdoption
  \/ ConvertDeadActivities
  \/ SimulateFailedResponse
  \/ RunExprOrKill
  \/ ScheduleNestedFinish 
  \/ TerminateAsync
  \/ SpawnRemoteAsync
  \/ SpawnLocalAsync
  \/ StopFinish 
  \/ StartFinish
  \/ AuthorizeTransitAsync
  \/ UnblockTerminateAsync
       
-------------------------------------------------------------------------------
(***************************************************************************)
(* Asserting fairness properties to all actions                            *)
(***************************************************************************)
Liveness ==
  /\ WF_Vars(RecvAsync) 
  /\ WF_Vars(ReleaseRootFinish)
  /\ WF_Vars(AuthorizeReceivedAsync) 
  /\ WF_Vars(StartFinish) 
  /\ WF_Vars(StopFinish)
  /\ WF_Vars(SpawnLocalAsync)
  /\ WF_Vars(SpawnRemoteAsync)
  /\ WF_Vars(TerminateAsync) 
  /\ WF_Vars(ScheduleNestedFinish) 
  /\ WF_Vars(RunExprOrKill)
  /\ WF_Vars(BackupTransit)
  /\ WF_Vars(BackupLive)
  /\ WF_Vars(BackupCompleted)
  /\ WF_Vars(MasterTransit)
  /\ WF_Vars(MasterLive)
  /\ WF_Vars(MasterCompleted)
  /\ WF_Vars(MasterTransitDone)  
  /\ WF_Vars(MasterLiveDone) 
  /\ WF_Vars(MasterCompletedDone) 
  /\ WF_Vars(AdopterTransit)
  /\ WF_Vars(AdopterLive)
  /\ WF_Vars(AdopterCompleted)
  /\ WF_Vars(SeekAdoption)
  /\ WF_Vars(ConvertDeadActivities)
  /\ WF_Vars(SimulateFailedResponse)
  /\ WF_Vars(AuthorizeTransitAsync) 
  /\ WF_Vars(UnblockTerminateAsync)
          
-------------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)          
Spec ==  Init /\ [][Next]_Vars /\ Liveness

THEOREM Spec => []( TypeOK /\ StateOK)
=============================================================================
\* Modification History
\* Last modified Mon Dec 18 10:24:48 AEDT 2017 by u5482878
\* Last modified Tue Dec 05 18:31:58 AEDT 2017 by shamouda
\* Created Wed Sep 13 12:14:43 AEST 2017 by u5482878
