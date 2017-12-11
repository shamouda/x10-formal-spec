--------------------   MODULE ExecutorDistFinishCorrectRep --------------------     
(****************************************************************************)
(* This specification models a subset of X10 programs to verify the         *) 
(* correctness of the 'finish' construct, which provides a termination      *)
(* detection protocol.                                                      *)
(*                                                                          *)
(* Distributed Finish:                                                      *)
(* --------------------------------                                         *)
(* This module specifies a distributed finish                               *) 
(* implementation that replicates the finish state on two places to allow   *)
(* correct termination when one replica is lost                             *)
(*                                                                          *)
(* Fixing PPoPP14 Replication Bug:                                          *)
(* --------------------------------                                         *)                    
(* We corrected a replication bug that was found in the original distributed*)
(* finish implementation, that was published in PPoPP14.                    *)
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
(*                                                                          *)
(* Corrected replication:                                                   *)
(* --------------------------------                                         *)
(*   Normal path:  requestor -> master  do();                               *)
(*                 master -> requestor  return;                             *)
(*                 requestor -> backup  do();                               *)
(*                 backup -> requestor  return;                             *)
(*   If Master died: requestor -> backup getAdopter();                      *)
(*                   requestor -> adopter do();                             *)
(*   The action do(); will be performed once in all cases                   *)   
(****************************************************************************)

EXTENDS Integers, Sequences, TLC
-----------------------------------------------------------------------------
(****************************************************************************)
(* Constants                                                                *)
(****************************************************************************)
CONSTANTS 
    PLACE,         (* The set of places                                     *)
    PROG_HOME,     (* The home place from which the program starts          *)
    PROG,          (* The input program as a sequence of async statements   *)
    MXFINISHES,    (* Maximum finish objects including root and remote      *)
    BACKUP,        (* A function from place to its backup                   *)
    DEPTH          (* Maximum expected depth of the trance                  *)

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

P0 == PROG_HOME
P1 == BACKUP[PROG_HOME]
P2 == BACKUP[BACKUP[PROG_HOME]]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants  (formulas true in every reachable state.)                   *)
(***************************************************************************)
TypeOK ==
  /\ fstates \in [ C!IDRange ->  C!FinishState] 
  /\ thrds \in  [ PLACE -> [  C!ThreadID ->  C!Thread ] ]
  /\ msgs \subseteq  C!Messages   
  /\ pstate \in { "running", "terminated","exceptionThrown" }
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
                   count |-> 0, excs |-> <<>>, here |->  C!NotPlace, 
                   parent |->  C!NotID, root |->  C!NotID, isGlobal |-> FALSE,
                   remActs |-> [ p \in PLACE |-> 0 ], eroot |-> C!NotID ]]
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
                    numActive |-> 0,
                   isReleased |-> FALSE ] ]
  /\ pstate  = "running"
  /\ mastersStatus = [ p \in PLACE |-> [     status |-> "running", 
                                         lastKilled |-> C!NotPlace ] ] 
  /\ msgs    = {}
  /\ seq     = [ aseq |-> 1, fseq |-> C!FIRST_ID, mseq |-> 1]
  /\ thrds = [ p \in PLACE |-> 
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
  /\ killed = {}
  /\ pendingAct = {}
  /\ waitForMsgs = {}
  /\ runningThrds = { [here |-> PROG_HOME, tid |-> 0 ] }
  /\ blockedThrds = {}
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
          /\ convertSet' =  convertSet \cup { t \in C!ConvTask :  
                                                /\ t.pl # C!NotPlace
                                                /\ t.pl # dead
                                                /\ t.pl \notin killed
                                                /\ t.fid = C!FIRST_ID
                                                /\ t.here = PROG_HOME }
     ELSE /\ mastersStatus' = [ p \in PLACE |-> IF \E m \in adoptSet' : m.here = p 
                                                THEN [     status |-> "seekAdoption", 
                                                       lastKilled |-> dead] 
                                                ELSE [     status |-> "running", 
                                                       lastKilled |-> C!NotPlace] ]
          /\ convertSet' =  convertSet
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
FindBlockedThreadMasterTransitDone ==
    LET tset == { t \in blockedThrds : 
                    /\ t.here \notin killed
                    /\ thrds[t.here][t.tid].status = "blocked"
                    /\ thrds[t.here][t.tid].blockingType = "AsyncTransit"
                    /\ C!FindIncomingMSG(t.here, "masterTransitDone") # C!NotMessage  }
    IN IF tset = {} THEN C!NotPlaceThread
       ELSE CHOOSE x \in tset : TRUE
              
MasterTransitDone == 
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET pthrd == FindBlockedThreadMasterTransitDone
     IN /\ pthrd # C!NotPlaceThread
        /\ LET here == pthrd.here
               tid == pthrd.tid
               msg == C!FindIncomingMSG(here, "masterTransitDone")
               success == msg.success
               submit == msg.submit
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
               isAdopter == msg.isAdopter
               backupPlace == msg.backupPlace
               adoptedFID == msg.adoptedFID
               masterWFM == [ src |-> rootPlace, 
                              dst |-> here,  
                              fid |-> root,
                           target |-> asyncDst,
                             type |-> "masterTransitDone"  ]
               backupWFM == [ src |-> backupPlace, 
                              dst |-> here,  
                              fid |-> root, 
                           target |-> asyncDst,
                        isAdopter |-> isAdopter,
                       adoptedFID |-> adoptedFID,
                             type |-> "backupTransitDone"  ]
           IN /\ SetActionNameAndDepth ( << "MasterTransitDone" , here, 
                                            "success", success, 
                                            "submit", submit >> ) 
              /\ IF success /\ submit /\ rootPlace \notin killed
                 THEN /\ C!ReplaceMsg ( msg, [   mid |-> seq.mseq, 
                                                 src |-> here, 
                                                 dst |-> backupPlace,
                                              target |-> asyncDst,
                                                 fid |-> root,
                                           isAdopter |-> isAdopter,
                                          adoptedFID |-> adoptedFID,
                                                type |-> "backupTransit" ])
                      /\ thrds' = thrds 
                      /\ blockedThrds' = blockedThrds 
                      /\ runningThrds' = runningThrds
                      /\ waitForMsgs' = (waitForMsgs \ {masterWFM}) \cup {backupWFM}
                      /\ C!IncrMSEQ(1)
                 ELSE IF success /\ rootPlace \notin killed \*ignore the async, go to the next step
                 THEN /\ C!RecvMsg ( msg )
                      /\ thrds' = [thrds EXCEPT ![here][tid].status = "running",
                                                ![here][tid].stack = 
                                                            <<[  b |-> top.b, 
                                                                 i |-> curStmt, 
                                                               fid |-> fid ]
                                                            >> \o tail ]
                      /\ blockedThrds' = blockedThrds \ { [here |-> here, tid |-> tid] }
                      /\ runningThrds' = runningThrds \cup { [here |-> here, tid |-> tid] }
                      /\ waitForMsgs' = waitForMsgs \ {masterWFM}
                      /\ C!IncrMSEQ(1)
                 ELSE /\ C!ReplaceMsg ( msg , [   mid |-> seq.mseq, 
                                                  src |-> here, 
                                                  dst |-> C!GetBackup(rootPlace),
                                               source |-> here,
                                               target |-> asyncDst,
                                                  fid |-> root,
                                                 type |-> "backupGetAdopter",
                                           actionType |-> "transit",
                                                  aid |-> C!NotActivity.aid,
                                            finishEnd |-> FALSE ])
                      /\ thrds' = thrds 
                      /\ blockedThrds' = blockedThrds 
                      /\ runningThrds' = runningThrds
                      /\ waitForMsgs' = waitForMsgs \ {masterWFM}  
                            \* we don't expect the backup to die
                            \* that is why we don't add 
                            \* backupGetAdopterDone in waitForMsgs
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, killed, pendingAct, 
                  fmasters, fbackups >>
                   

MasterLiveDone == 
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
               isAdopter == msg.isAdopter
               adoptedFID == msg.adoptedFID
               backupPlace == msg.backupPlace
               source == msg.source
               target == msg.target
               masterWFM ==  [ src |-> rootPlace,     
                               dst |-> here,  
                               fid |-> root,
                               aid |-> actId,
                            source |-> source,
                            target |-> target,
                              type |-> "masterLiveDone"  ]
               backupWFM == [  src |-> backupPlace, 
                               dst |-> here,  
                               fid |-> root,
                               aid |-> actId, 
                            source |-> source,
                            target |-> here,
                         isAdopter |-> isAdopter,
                        adoptedFID |-> adoptedFID,
                              type |-> "backupLiveDone"  ]                                           
           IN  /\ SetActionNameAndDepth ( << "MasterLiveDone", here >> )
               /\ activity # C!NotActivity
               /\ fstates[activity.fid].here = here
               /\ IF success /\ submit /\ rootPlace \notin killed
                  THEN /\ C!ReplaceMsg ( msg , [   mid |-> seq.mseq, 
                                               src |-> here, 
                                               dst |-> backupPlace,
                                            source |-> source,
                                            target |-> here,
                                               fid |-> root,
                                               aid |-> actId,
                                              type |-> "backupLive",
                                         isAdopter |-> isAdopter,
                                         adoptedFID |-> adoptedFID ])
                       /\ waitForMsgs' = (waitForMsgs \ {masterWFM}) \cup {backupWFM}
                       /\ C!IncrMSEQ(1)
                       /\ pendingAct' = pendingAct
                  ELSE IF success /\ rootPlace \notin killed
                  THEN /\ C!RecvMsg ( msg )
                       /\ pendingAct' = pendingAct \ {activity}
                       /\ seq' = seq
                       /\ waitForMsgs' = waitForMsgs \ {masterWFM}
                  ELSE /\ C!ReplaceMsg ( msg, [   mid |-> seq.mseq, 
                                               src |-> here, 
                                               dst |-> C!GetBackup(rootPlace),
                                            source |-> source,
                                            target |-> here,
                                               fid |-> root,
                                              type |-> "backupGetAdopter",
                                              aid |-> actId,
                                         finishEnd |-> FALSE,
                                              actionType |-> "live" ])
                       /\ waitForMsgs' = waitForMsgs \ {masterWFM}  
                             \* we don't expect backup to die 
                             \* so we don't add 
                             \* backupGetAdopterDone in waitForMsgs
                       /\ C!IncrMSEQ(1)
                       /\ pendingAct' = pendingAct
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate,   
                  thrds, killed,  fmasters, fbackups, blockedThrds, runningThrds>>

MasterCompletedDone == 
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("masterCompletedDone")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               root == msg.fid
               success == msg.success
               rootPlace == C!GetFinishHome(root)
               isAdopter == msg.isAdopter
               backupPlace == msg.backupPlace
               finishEnd == msg.finishEnd
               masterWFM == [  src |-> rootPlace, 
                               dst |-> here,  
                            target |-> here,
                               fid |-> root,
                         isAdopter |-> isAdopter,
                              type |-> "masterCompletedDone"  ]
               backupWFM == [    src |-> backupPlace, 
                                 dst |-> here,  
                                 fid |-> root, 
                              target |-> here,
                           isAdopter |-> isAdopter,
                                type |-> "backupCompletedDone"  ]
           IN /\ SetActionNameAndDepth ( << "MasterCompletedDone", here >> )
              /\ IF success /\ rootPlace \notin killed
                 THEN /\ C!ReplaceMsg ( msg ,[ mid |-> seq.mseq,
                                               src |-> here, 
                                               dst |-> backupPlace, 
                                            target |-> here, 
                                               fid |-> root, 
                                              type |-> "backupCompleted",
                                         finishEnd |-> finishEnd,
                                         isAdopter |-> isAdopter ])
                      /\ IF finishEnd THEN waitForMsgs' = (waitForMsgs \ {masterWFM}) 
                                      ELSE waitForMsgs' = (waitForMsgs \ {masterWFM}) 
                                                                       \cup {backupWFM}
                      /\ C!IncrMSEQ(1)
                 ELSE /\ C!ReplaceMsg ( msg , [   mid |-> seq.mseq, 
                                                  src |-> here, 
                                                  dst |-> C!GetBackup(rootPlace),
                                               source |-> C!NotPlace,
                                               target |-> here,
                                                  fid |-> root,
                                                 type |-> "backupGetAdopter",
                                                  aid |-> C!NotActivity.aid,
                                            finishEnd |-> FALSE,
                                           actionType |-> "completed" ])
                      /\ waitForMsgs' = waitForMsgs \ {masterWFM} 
                            \* we don't expect backup to die 
                            \* so we don't add backupGetAdopterDone 
                            \* in waitForMsgs
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate,   
                  thrds,pendingAct, killed,  fmasters, fbackups, 
                  blockedThrds, runningThrds >>

-------------------------------------------------------------------------------------
FindBlockedThreadGetAdopterDone ==
  LET tset == { t \in blockedThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "blocked"
                  /\ thrds[t.here][t.tid].blockingType = "AsyncTransit"
                  /\ C!FindIncomingMSG(t.here, "backupGetAdopterDone") # C!NotMessage  }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE
       
GetAdopterDone ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG ("backupGetAdopterDone")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst 
                actionType == msg.actionType
                adoptedRoot == msg.adoptedRoot
                adoptedRootPlace == C!GetFinishHome(msg.adoptedRoot)
                adoptedFID == msg.fid
           IN /\ SetActionNameAndDepth ( << "GetAdopterDone", here >> ) 
              /\ IF actionType = "transit"
                 THEN /\ C!ReplaceMsg(msg, [   mid |-> seq.mseq, 
                                               src |-> here, 
                                               dst |-> adoptedRootPlace,
                                            target |-> msg.target,
                                               fid |-> adoptedRoot,
                                              type |-> "adopterTransit",
                                        adoptedFID |-> adoptedFID ])
                      /\ C!IncrMSEQ(1)
                 ELSE IF actionType = "live"
                 THEN /\ C!ReplaceMsg(msg, [ mid |-> seq.mseq,
                                               src |-> here,
                                               dst |-> adoptedRootPlace, 
                                            source |-> msg.source,
                                            target |-> msg.target, 
                                               fid |-> adoptedRoot,  
                                               aid |-> msg.aid,
                                              type |-> "adopterLive",
                                        adoptedFID |-> adoptedFID ])
                      /\ C!IncrMSEQ(1)
                 ELSE IF actionType = "completed"
                 THEN /\ C!ReplaceMsg(msg, [ mid |-> seq.mseq,
                                               src |-> here, 
                                               dst |-> adoptedRootPlace, 
                                            target |-> msg.target, 
                                               fid |-> adoptedRoot, 
                                         finishEnd |-> msg.finishEnd,
                                              type |-> "adopterCompleted",
                                        adoptedFID |-> adoptedFID ] )
                      /\ C!IncrMSEQ(1)
                 ELSE FALSE
  /\ UNCHANGED << fstates, pstate, thrds, killed, pendingAct,  fmasters, fbackups, waitForMsgs, 
         mastersStatus, adoptSet, convertSet, blockedThrds, runningThrds >>

------------------------------------------------------------------
FindBlockedThreadAsyncTerm ==
  LET tset == { t \in blockedThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "blocked"
                  /\ thrds[t.here][t.tid].blockingType = "AsyncTerm"
                  /\ LET msg == C!FindIncomingMSG(t.here, "backupCompletedDone") 
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
               msg == C!FindIncomingMSG(here, "backupCompletedDone")
               success == msg.success
               top == Head(thrds[here][tid].stack)
               blk == top.b
               fid == top.fid
               root == msg.fid
               rootPlace == C!GetFinishHome(root)
           IN /\ SetActionNameAndDepth ( << "UnblockTerminateAsync", here , 
                                            "success", success >> )
              /\ waitForMsgs' = waitForMsgs \ {[ src |-> rootPlace, 
                                                 dst |-> here,  
                                              target |-> here,
                                                 fid |-> root,
                                                type |-> "backupCompletedDone"  ]}      
              /\ IF    Len(thrds[here][tid].stack) = 1
                 THEN /\ thrds' = [thrds EXCEPT ![here][tid].stack = <<>>,
                                                ![here][tid].status = "idle" ]
                      /\ blockedThrds' = blockedThrds \ { [ here |-> here, tid |-> tid ] }
                      /\ runningThrds' = runningThrds
                 ELSE /\ thrds' = [thrds EXCEPT ![here][tid].stack = Tail(@),
                                                ![here][tid].status = "running" ]
                      /\ blockedThrds' = blockedThrds \ { [ here |-> here, tid |-> tid ] }
                      /\ runningThrds' = runningThrds \cup  { [ here |-> here, tid |-> tid ] }
              /\ IF  blk = 0
                 THEN pstate' = "terminated"
                 ELSE pstate' = pstate
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates,seq, msgs, 
                  killed, pendingAct, fmasters, fbackups>>
                    
--------------------------------------------------------------------------------------
FindBlockedThreadAuthorizeTransitAsync ==
  LET tset == { t \in blockedThrds : 
                  /\ t.here \notin killed
                  /\ thrds[t.here][t.tid].status = "blocked"
                  /\ thrds[t.here][t.tid].blockingType = "AsyncTransit"
                  /\ C!FindIncomingMSG(t.here, "backupTransitDone") # C!NotMessage  }
  IN IF tset = {} THEN C!NotPlaceThread
     ELSE CHOOSE x \in tset : TRUE

AuthorizeTransitAsync ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET pthrd == FindBlockedThreadAuthorizeTransitAsync
     IN /\ pthrd # C!NotPlaceThread
        /\ LET here == pthrd.here
               tid == pthrd.tid
               msg == C!FindIncomingMSG(here, "backupTransitDone")
               success == msg.success
               top == Head(thrds[here][tid].stack)
               tail == Tail(thrds[here][tid].stack)
               lstStmt == top.i
               curStmt == top.i + 1
               blk == top.b
               root == msg.fid
               fid == top.fid
               rootPlace == C!GetFinishHome(root)
               backupPlace == msg.src
               nested == PROG[blk].stmts[curStmt]
               asyncDst == PROG[nested].dst
               realFID == IF msg.adoptedFID # C!NotID THEN msg.adoptedFID ELSE root
           IN /\ SetActionNameAndDepth ( << "AuthorizeTransitAsync" , here, "to", 
                                            asyncDst, "success", success >> )
              /\ C!ReplaceMsg ( msg , [ mid |-> seq.mseq, 
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
              /\ waitForMsgs' = waitForMsgs \ {[ type |-> "backupTransitDone",
                                                  dst |-> msg.dst,
                                                  fid |-> msg.fid,
                                                  src |-> backupPlace,
                                               target |-> asyncDst,
                                            isAdopter |-> msg.isAdopter,
                                           adoptedFID |-> msg.adoptedFID ]}
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, 
                  killed, pendingAct, fmasters, fbackups>>
                   
AuthorizeReceivedAsync == 
  /\ pstate = "running"
  /\ pendingAct # {}
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupLiveDone")
     IN /\ msg # C!NotMessage
        /\ LET backupPlace == msg.src
               here == msg.dst
               actId == msg.aid
               activity == FindPendingActivity(actId)
               root == msg.fid
               success == msg.success
               rootPlace == C!GetFinishHome(root)
           IN /\ SetActionNameAndDepth ( << "AuthorizeReceivedAsync", here, "success", success >> )
              /\ msg # C!NotMessage
              /\ activity # C!NotActivity
              /\ fstates[activity.fid].here = here
              /\ waitForMsgs' = waitForMsgs \ {[ src |-> backupPlace, 
                                                 dst |-> here,  
                                                 fid |-> root,
                                                 aid |-> actId,
                                              source |-> msg.source,
                                              target |-> msg.target,
                                                type |-> "backupLiveDone",
                                           isAdopter |-> msg.isAdopter,
                                          adoptedFID |-> msg.adoptedFID  ]}  
              /\ C!RecvMsg ( msg )
              /\ pendingAct' = pendingAct \ {activity}
              /\ LET idleThrd == FindIdleThread(here)
                     stkEntry == [b |-> activity.b, i |-> C!I_START , fid |-> activity.fid]
                 IN  /\ thrds' = [thrds EXCEPT ![here][idleThrd.tid].stack = <<stkEntry>>, 
                                               ![here][idleThrd.tid].status = "running" ]
                     /\ runningThrds' = runningThrds \cup { [ here |-> here, tid |-> idleThrd.tid] }
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, seq,  
                  killed,  fmasters, fbackups, blockedThrds >>

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
                                                 fid |-> root,
                                                type |-> "releaseFinish"  ]}
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
  /\ LET  msg == C!FindMSG("masterTransit")
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
              /\ LET submit == src \notin killed /\ target \notin killed
                 IN /\ IF submit
                       THEN IF fmasters[fid].id = C!NotID
                            THEN fmasters' = [fmasters EXCEPT ![fid].id = fid,
                                                              ![fid].backupPlace = backupPlace,
                                                              ![fid].transit[src][target] = @ + 1,
                                                              ![fid].numActive  =  @ + 2,
                                                              ![fid].live[here] = 1 ]
                            ELSE fmasters' = [fmasters EXCEPT ![fid].transit[src][target] = @ + 1,
                                                              ![fid].numActive = @ + 1 ]
                       ELSE fmasters' = fmasters
                    /\ IF src \in killed
                       THEN /\ C!RecvMsg (msg)
                            /\ seq' = seq
                       ELSE /\ C!ReplaceMsg (msg,  [   mid |-> seq.mseq, 
                                                       src |-> here, 
                                                       dst |-> src,
                                                    target |-> target,
                                                       fid |-> fid,
                                                      type |-> "masterTransitDone",
                                                    submit |-> submit,
                                                   success |-> TRUE,
                                                 isAdopter |-> FALSE,
                                                adoptedFID |-> C!NotID,
                                               backupPlace |-> backupPlace ]) 
                            /\ C!IncrMSEQ(1)
  /\ UNCHANGED << waitForMsgs, convertSet, adoptSet, mastersStatus, fstates, pstate,
                  thrds, killed, pendingAct,  fbackups,
                  blockedThrds, runningThrds >>

MasterLive ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("masterLive")
     IN /\ msg # C!NotMessage
        /\ LET  here == msg.dst
                fid == msg.fid
                source == msg.source
                target == msg.target \* msg.target = msg.src
                backupPlace == C!GetBackup(here)
           IN /\ SetActionNameAndDepth ( << "MasterLive", here >> )
              /\ fid # C!NotID
              /\ fstates[fid].here = here
              /\ mastersStatus[here].status = "running"
              /\ target = msg.src
              /\ LET submit == source \notin killed /\ target \notin killed
                 IN /\ IF submit
                       THEN  /\ fmasters[fid].transit[source][target] > 0
                             /\ fmasters' = [fmasters EXCEPT ![fid].transit[source][target] = @ - 1,
                                                             ![fid].live[target] = @ + 1 ]
                       ELSE  /\ fmasters' = fmasters
                    /\ IF target \in killed
                       THEN /\ C!RecvMsg (msg)
                            /\ seq' = seq
                       ELSE /\  C!ReplaceMsg (msg, [  mid |-> seq.mseq, 
                                                      src |-> here, 
                                                      dst |-> target,
                                                   source |-> source,
                                                   target |-> target,
                                                      fid |-> fid,
                                                      aid |-> msg.aid,
                                                     type |-> "masterLiveDone",
                                                   submit |-> submit,
                                                  success |-> TRUE,
                                                isAdopter |-> FALSE,
                                               adoptedFID |-> C!NotID,
                                              backupPlace |-> backupPlace ])
                    /\ C!IncrMSEQ(1)
   /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, 
                   thrds,  waitForMsgs, killed, pendingAct,  fbackups,
                   blockedThrds, runningThrds >>

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
               /\ target = src
               /\ mastersStatus[here].status = "running"
               /\ IF ( fmasters[fid].live[target] > 0 /\ fmasters[fid].numActive > 0 )
                  THEN /\ fmasters' = [fmasters EXCEPT ![fid].live[target] = @ - 1,
                                                       ![fid].numActive    = @ - 1,
                                                       ![fid].isReleased   = 
                                                           (fmasters[fid].numActive = 1)]
                  ELSE /\ target \in killed
                       /\ fmasters' = fmasters
               /\ IF ( fmasters'[fid].numActive = 0 /\ src \notin killed )
                  THEN /\ C!ReplaceMsgSet (msg, {[ mid |-> seq.mseq,
                                                   src |-> here, 
                                                   dst |-> src, 
                                                target |-> target, 
                                                   fid |-> fid, 
                                                  type |-> "masterCompletedDone",
                                               success |-> TRUE,
                                             isAdopter |-> FALSE,
                                             finishEnd |-> finishEnd,
                                           backupPlace |-> backupPlace ],
                                            [ mid |-> seq.mseq+1,
                                              src |-> here, 
                                              dst |-> here, 
                                              fid |-> fid,
                                             type |-> "releaseFinish" ]}) 
                       /\ C!IncrMSEQ(2)
                  ELSE IF  fmasters'[fid].numActive = 0 
                  THEN /\ C!ReplaceMsg (msg, [ mid |-> seq.mseq,
                                              src |-> here, 
                                              dst |-> here, 
                                              fid |-> fid,
                                             type |-> "releaseFinish" ]) 
                       /\ C!IncrMSEQ(1)
                  ELSE IF src \notin killed
                  THEN /\ C!ReplaceMsg (msg, [ mid |-> seq.mseq,
                                               src |-> here, 
                                               dst |-> src, 
                                            target |-> target, 
                                               fid |-> fid, 
                                              type |-> "masterCompletedDone",
                                           success |-> TRUE,
                                         isAdopter |-> FALSE,
                                         finishEnd |-> finishEnd,
                                       backupPlace |-> backupPlace ] )
                       /\ C!IncrMSEQ(1)
                  ELSE /\ C!RecvMsg (msg)
                       /\ seq' = seq
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, 
                  thrds, killed, pendingAct,  fbackups, waitForMsgs,
                  blockedThrds, runningThrds >>
                  
-----------------------------------------------------------------------------
(***************************************************************************)
(* Adopting Finish master replica actions                                  *)
(***************************************************************************)
AdopterTransit ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET  msg == C!FindMSG("adopterTransit")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               target == msg.target
               backupPlace == C!GetBackup(here)
               adoptedFID == msg.adoptedFID
           IN /\ SetActionNameAndDepth ( << "AdopterTransit", here >> )
              /\ mastersStatus[here].status = "running"
              /\ fid # C!NotID
              /\ fstates[fid].here = here
              /\ LET submit == src \notin killed  /\  target \notin killed 
                 IN /\ IF submit
                       THEN /\ fmasters' = [fmasters EXCEPT ![fid].transitAdopted[src][target] = @ + 1,
                                                            ![fid].numActive = @ + 1 ]
                       ELSE /\ fmasters' = fmasters
                    /\ C!ReplaceMsg (msg,  [   mid |-> seq.mseq, 
                                               src |-> here, 
                                               dst |-> src,
                                            target |-> target,
                                               fid |-> fid,
                                              type |-> "masterTransitDone",
                                            submit |-> submit,
                                           success |-> TRUE,
                                       backupPlace |-> backupPlace,
                                         isAdopter |-> TRUE,
                                        adoptedFID |-> adoptedFID  ]) 
                    /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, 
                  thrds, killed, pendingAct, fbackups, waitForMsgs,
                  blockedThrds, runningThrds >>
                   
AdopterLive ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET  msg == C!FindMSG("adopterLive")  
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               source == msg.source
               target == msg.target
               backupPlace == C!GetBackup(here)
               adoptedFID == msg.adoptedFID
           IN /\ SetActionNameAndDepth ( << "AdopterLive", here >> )
              /\ fid # C!NotID
              /\ backupPlace # C!NotPlace
              /\ fstates[fid].here = here
              /\ mastersStatus[here].status = "running"
              /\ target = msg.src
              /\ LET submit ==  source \notin killed  /\  target \notin killed 
                 IN /\ IF submit
                       THEN  /\ fmasters[fid].transitAdopted[source][target] > 0
                             /\ fmasters' = [fmasters EXCEPT ![fid].transitAdopted[source][target] = @ - 1,
                                                             ![fid].liveAdopted[target] = @ + 1 ]
                       ELSE fmasters' = fmasters
                    /\ C!ReplaceMsg (msg,  [  mid |-> seq.mseq, 
                                              src |-> here, 
                                              dst |-> target,
                                           source |-> source,
                                           target |-> target,
                                              fid |-> fid,
                                              aid |-> msg.aid,
                                             type |-> "masterLiveDone",
                                           submit |-> submit,
                                          success |-> TRUE,
                                        isAdopter |-> TRUE,
                                       adoptedFID |-> adoptedFID,
                                      backupPlace |-> backupPlace ]) 
                    /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate,waitForMsgs,
                  thrds, waitForMsgs, killed, pendingAct,  fbackups,
                  blockedThrds, runningThrds >>

AdopterCompleted ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET  msg == C!FindMSG("adopterCompleted")
     IN /\ msg # C!NotMessage
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
                                              ![fid].numActive           = @ - 1,
                                              ![fid].isReleased   = (fmasters[fid].numActive = 1)]
              /\ IF fmasters'[fid].numActive = 0 
                 THEN /\ C!ReplaceMsgSet (msg, {[ mid |-> seq.mseq,
                                                  src |-> here, 
                                                  dst |-> src, 
                                               target |-> target, 
                                                  fid |-> fid, 
                                                 type |-> "masterCompletedDone",
                                              success |-> TRUE,
                                            isAdopter |-> TRUE,
                                            finishEnd |-> finishEnd,
                                          backupPlace |-> backupPlace ],
                                                [ mid |-> seq.mseq+1,
                                                  src |-> here, 
                                                  dst |-> here, 
                                                  fid |-> fid,
                                                 type |-> "releaseFinish" ]}) 
                      /\ C!IncrMSEQ(2)
                 ELSE IF finishEnd
                      THEN /\ C!RecvMsg(msg) 
                           /\ seq' = seq
                      ELSE /\ C!ReplaceMsg (msg, [ mid |-> seq.mseq,
                                                   src |-> here, 
                                                   dst |-> src, 
                                                target |-> target, 
                                                   fid |-> fid, 
                                                  type |-> "masterCompletedDone",
                                               success |-> TRUE,
                                             isAdopter |-> TRUE,
                                             finishEnd |-> finishEnd,
                                           backupPlace |-> backupPlace ] )
                           /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate, 
                  thrds, waitForMsgs, killed, pendingAct,  fbackups, waitForMsgs,
                   blockedThrds, runningThrds >>

-------------------------------------------------------------------------------
(***************************************************************************)
(* Finish backup replica actions                                           *)
(***************************************************************************)     
BackupGetAdopter == 
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupGetAdopter")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               actionType == msg.actionType
               source == msg.source
               target == msg.target
           IN /\ SetActionNameAndDepth ( << "BackupGetAdopter", here >> )
              /\ fbackups[fid].isAdopted = TRUE
              /\ IF src \in killed \/ msg.dst \in killed
                 THEN /\ C!RecvMsg (msg)
                      /\ seq' = seq
                 ELSE /\ C!ReplaceMsg (msg, [   mid |-> seq.mseq, 
                                                src |-> here, 
                                                dst |-> src,
                                             source |-> source,
                                             target |-> target,
                                                fid |-> fid,
                                        adoptedRoot |-> fbackups[fid].adoptedRoot,
                                         actionType |-> actionType,
                                                aid |-> msg.aid,
                                          finishEnd |-> msg.finishEnd,
                                               type |-> "backupGetAdopterDone" ])
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << fstates, pstate, thrds, killed, pendingAct,  fmasters, 
                     fbackups, waitForMsgs, mastersStatus, adoptSet, convertSet, 
                     blockedThrds, runningThrds >>

BackupTransit ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupTransit")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               target == msg.target
               isAdopter == msg.isAdopter
               adoptedFID == msg.adoptedFID
           IN /\ SetActionNameAndDepth ( << "BackupTransit", here >> )
              /\ fmasters[fid].backupPlace = here
              /\ IF ~  isAdopter /\ ~ fbackups[fid].isAdopted
                 THEN IF fbackups[fid].id = C!NotID
                      THEN fbackups' = [ fbackups EXCEPT ![fid].id = fid,
                                                         ![fid].transit[src][target] = @+1,
                                                         ![fid].live[src] = 1,
                                                         ![fid].numActive  =  @ + 2 ]
                      ELSE fbackups' = [ fbackups EXCEPT ![fid].transit[src][target] = @ + 1,
                                                         ![fid].numActive  =  @ + 1 ]
                 ELSE fbackups' = fbackups
                      (* We don't have transitAdopted at the backups!!!
                         fbackups' = [ fbackups EXCEPT ![fid].transitAdopted[src][target] = @ + 1,
                                                        ![fid].numActive  =  @ + 1 ] *) 
              /\ IF fbackups[fid].isAdopted \* Change to the path of adopterTransit
                 THEN /\ C!ReplaceMsg (msg, [   mid |-> seq.mseq, 
                                                src |-> here, 
                                                dst |-> src,
                                             target |-> target,
                                                fid |-> fid,
                                               type |-> "masterTransitDone",
                                          isAdopter |-> FALSE,
                                         adoptedFID |-> C!NotID,
                                        backupPlace |-> C!NotPlace,
                                            submit  |-> FALSE,
                                            success |-> FALSE ]  )
                      /\ C!IncrMSEQ(1)
                 ELSE IF src \in killed 
                 THEN /\ C!RecvMsg (msg) 
                      /\ seq' = seq
                 ELSE /\ C!ReplaceMsg (msg, [   mid |-> seq.mseq, 
                                                src |-> here, 
                                                dst |-> src,
                                             target |-> target,
                                                fid |-> fid,
                                               type |-> "backupTransitDone",
                                            success |-> TRUE,
                                          isAdopter |->isAdopter,
                                         adoptedFID |-> adoptedFID])
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
               isAdopter == msg.isAdopter
               adoptedFID == msg.adoptedFID
           IN /\ SetActionNameAndDepth ( << "BackupLive", here >> )
              /\ fmasters[fid].backupPlace = here
              /\ IF ~  isAdopter /\ ~ fbackups[fid].isAdopted
                 THEN /\ fbackups[fid].transit[source][target] > 0
                      /\ fbackups' = [ fbackups EXCEPT ![fid].transit[source][target] = @ - 1,
                                                        ![fid].live[target] = @ + 1 ]
                 ELSE /\ fbackups' = fbackups  
                         (* We don't have transitAdopted at the backups!!!!
                           /\ fbackups[fid].transitAdopted[source][target] > 0
                           /\ fbackups' = [ fbackups EXCEPT ![fid].transitAdopted[source][target] = @ - 1,
                                                            ![fid].liveAdopted[target] = @ + 1 ]*)
              /\ IF fbackups[fid].isAdopted \* Change to the path of adopterLive
                 THEN /\ C!ReplaceMsg (msg, [   mid |-> seq.mseq,  
                                                src |-> here, 
                                                dst |-> src,
                                             source |-> source,
                                             target |-> target,
                                                fid |-> fid,
                                                aid |-> msg.aid,
                                               type |-> "masterLiveDone",
                                             submit |-> FALSE,
                                            success |-> FALSE,
                                          isAdopter |-> FALSE,
                                         adoptedFID |-> C!NotID,
                                        backupPlace |-> C!NotPlace ])
                      /\ C!IncrMSEQ(1) 
                 ELSE IF src \in killed
                 THEN /\ C!RecvMsg ( msg ) 
                      /\ seq' = seq
                 ELSE /\ C!ReplaceMsg (msg, [   mid |-> seq.mseq, 
                                                src |-> here, 
                                                dst |-> src,
                                             target |-> target,
                                             source |-> source,
                                                fid |-> fid,
                                                aid |-> msg.aid,
                                               type |-> "backupLiveDone",
                                            success |-> TRUE,
                                          isAdopter |->isAdopter,
                                         adoptedFID |-> adoptedFID ])
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
               isAdopter == msg.isAdopter
               finishEnd == msg.finishEnd
           IN /\ fmasters[fid].backupPlace = here
              /\ SetActionNameAndDepth ( << "BackupCompleted", here >> )
              /\ IF ~  isAdopter /\ ~ fbackups[fid].isAdopted
                 THEN  /\ fbackups[fid].live[target] > 0
                       /\ fbackups[fid].numActive > 0
                       /\ fbackups' = [ fbackups EXCEPT ![fid].live[target] = @ - 1,
                                                        ![fid].numActive    = @ - 1 ]
                 ELSE  /\ fbackups' = fbackups
              /\ IF fbackups[fid].isAdopted   \* Change to the path of adopterCompleted
                 THEN /\ C!ReplaceMsg ( msg, [   mid |-> seq.mseq,  
                                                 src |-> here, 
                                                 dst |-> src,
                                              target |-> target,
                                                 fid |-> fid,
                                                type |-> "masterCompletedDone",
                                             success |-> FALSE,
                                           isAdopter |-> FALSE,
                                           finishEnd |-> FALSE,
                                         backupPlace |-> C!NotPlace ])
                      /\ C!IncrMSEQ(1) 
                 ELSE IF src \in killed \/ finishEnd
                 THEN /\ C!RecvMsg ( msg ) 
                      /\ seq' = seq
                 ELSE /\ C!ReplaceMsg ( msg,  [   mid |-> seq.mseq, 
                                                  src |-> here, 
                                                  dst |-> src,
                                               target |-> target,
                                                  fid |-> fid,
                                            isAdopter |-> isAdopter, 
                                                 type |-> "backupCompletedDone",
                                              success |-> TRUE] )
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convertSet, adoptSet, mastersStatus, fstates, pstate,
                  thrds, killed, pendingAct,  fmasters, waitForMsgs,
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
              /\ convertSet' =  convertSet \cup { t \in C!ConvTask :  
                                                    /\ t.pl # C!NotPlace
                                                    /\ t.pl \notin killed
                                                    /\ t.fid = adopter
                                                    /\ t.here = here }
              /\ IF \E m \in adoptSet' : m.here = here
                 THEN /\ mastersStatus' = mastersStatus
                 ELSE /\ mastersStatus' = [ mastersStatus EXCEPT ![here].status = "convertDead"]
   /\ UNCHANGED << fstates, msgs, pstate,seq, thrds, killed, pendingAct,  waitForMsgs, 
                   blockedThrds, runningThrds >> 

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
                         THEN /\ msgs' = (msgs \ delMsgs) \cup {[   mid |-> seq.mseq, 
                                            src |-> msg.src, 
                                            dst |-> msg.dst,
                                         source |-> msg.source,
                                         target |-> msg.target,
                                            fid |-> msg.fid,
                                            aid |-> msg.aid,
                                           type |-> "masterLiveDone",
                                         submit |-> FALSE,
                                        success |-> FALSE,
                                      isAdopter |-> FALSE,
                                      adoptedFID |-> C!NotID,
                                    backupPlace |-> C!NotPlace ]} 
                         ELSE /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "masterCompletedDone"
                    THEN IF  ~ (\E m \in msgs: \*message has been sent already
                                     /\ m.type = msg.type /\ m.src = msg.src 
                                     /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                     /\ m.isAdopter = msg.isAdopter 
                                     /\ m.success )
                         THEN  /\ msgs' = (msgs \ delMsgs) \cup {[   mid |-> seq.mseq,  
                                                src |-> msg.src, 
                                                dst |-> msg.dst,
                                             target |-> msg.target,
                                                fid |-> msg.fid,
                                               type |-> "masterCompletedDone",
                                            success |-> FALSE,
                                          isAdopter |-> FALSE,
                                          finishEnd |-> FALSE,
                                        backupPlace |-> C!NotPlace ] }
                         ELSE  /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "masterTransitDone"    
                    THEN IF ~ (\E m \in msgs: \*message has been sent already
                                    /\ m.type = msg.type /\ m.src = msg.src 
                                    /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                    /\ m.success )
                         THEN  /\ msgs' = (msgs \ delMsgs) \cup {[   mid |-> seq.mseq, 
                                                src |-> msg.src, 
                                                dst |-> msg.dst,
                                             target |-> msg.target,
                                                fid |-> msg.fid,
                                               type |-> "masterTransitDone",
                                          isAdopter |-> FALSE,
                                          adoptedFID |-> C!NotID,
                                        backupPlace |-> C!NotPlace,
                                            submit  |-> FALSE,
                                            success |-> FALSE ] }
                         ELSE  /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "backupCompletedDone"
                    THEN IF ~ (\E m \in msgs: \*message has been sent already 
                                    /\ m.type = msg.type /\ m.src = msg.src 
                                    /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                    /\ m.isAdopter = msg.isAdopter /\ m.success )
                         THEN /\ msgs' = (msgs \ delMsgs) \cup {[   mid |-> seq.mseq,
                                                                    src |-> msg.src, 
                                                                    dst |-> msg.dst,
                                                                 target |-> msg.target,
                                                                    fid |-> msg.fid,
                                                                   type |-> "backupCompletedDone",
                                                              isAdopter |-> msg.isAdopter,
                                                                success |-> FALSE ] }
                         ELSE /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "backupLiveDone"    
                    THEN IF  ~ (\E m \in msgs: \*message has been sent already
                                     /\ m.type = msg.type /\ m.src = msg.src 
                                     /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                     /\ m.source = msg.source /\ m.success )
                         THEN /\ msgs' = (msgs \ delMsgs) \cup {[   mid |-> seq.mseq,
                                                                    src |-> msg.src,
                                                                    dst |-> msg.dst,
                                                                 target |-> msg.target,
                                                                 source |-> msg.source,
                                                                    fid |-> msg.fid,
                                                                    aid |-> msg.aid,
                                                                   type |-> "backupLiveDone",
                                                              isAdopter |-> msg.isAdopter,
                                                             adoptedFID |-> msg.adoptedFID,
                                                                success |-> FALSE ]}
                         ELSE /\ msgs' = (msgs \ delMsgs)
                    ELSE IF msg.type = "backupTransitDone"
                    THEN IF  ~ (\E m \in msgs: \*message has been sent already
                                     /\ m.type = msg.type /\ m.src = msg.src 
                                     /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                     /\ m.target = msg.target /\ m.success )
                         THEN /\ msgs' = (msgs \ delMsgs) \cup {[   mid |-> seq.mseq,
                                                              src |-> msg.src, 
                                                              dst |-> msg.dst,
                                                           target |-> msg.target,
                                                              fid |-> msg.fid,
                                                             type |-> "backupTransitDone",
                                                        isAdopter |-> msg.isAdopter,
                                                       adoptedFID |-> msg.adoptedFID,
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
  \/ BackupGetAdopter
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
  \/ GetAdopterDone
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
    /\ WF_Vars(GetAdopterDone)
    /\ WF_Vars(BackupGetAdopter)
    /\ WF_Vars(AuthorizeTransitAsync) 
    /\ WF_Vars(UnblockTerminateAsync)
          
-------------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)          
Spec ==  Init /\ [][Next]_Vars /\ Liveness

THEOREM Spec => []( TypeOK /\ StateOK)
(*
-metadir /media/u5482878/DATAPART1/tla_ws/states -checkpoint 0
-metadir /Users/shamouda/tla_states -checkpoint 0
***)
=============================================================================
\* Modification History
\* Last modified Mon Dec 11 20:55:15 AEDT 2017 by u5482878
\* Last modified Sun Dec 10 18:15:04 AEDT 2017 by shamouda
\* Created Wed Sep 13 12:14:43 AEST 2017 by u5482878
