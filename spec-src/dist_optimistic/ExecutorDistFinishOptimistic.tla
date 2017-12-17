--------------------   MODULE ExecutorDistFinishOptimistic --------------------   
(****************************************************************************)
(* This specification models a subset of X10 programs to verify the         *) 
(* correctness of the 'finish' construct, which provides a termination      *)
(* detection protocol.                                                      *)
(*                                                                          *)
(* Distributed Finish:                                                      *)
(* --------------------------------                                         *)
(* This module specifies a distributed finish                               *) 
(* implementation that replicates the finish state on two places to allow   *)
(* correct termination when one replica is lost. Unlike the pessimistic     *)
(* finish protocol proposed in PPoPP14, we are specifying a new optimistic  *)
(* protocol that reduces communication during normal execution, at the      *)
(* expense of more complex recovery                                         *)
(*                                                                          *)
(* Assumptions:                                                             *)
(* ---------------------                                                    *)
(* - A root finish will have at most one remote finish at any other place   *)
(* - Remote finish objects must be cleaned after root finish is released    *)
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
    fstates,       (* All finish states (root and remote)                   *)
    fmasters,      (* Root finishes master states                           *)   
    fbackups,      (* Root finishes backup states                           *)
    msgs,          (* The set of inflight messages. We delete a message     *) 
                   (* once received                                         *) 
    pstate,        (* Program state: init -> running -> terminated          *)
    seq,           (* Sequences                                             *)
    thrds,         (* Threads at all places                                 *)
    killed,        (* The set places killed so far                          *)
    runningThrds,  (* Set of running threads in all places                  *)
    blockedThrds,  (* Set of blocked threads in all places                  *)
    waitForMsgs,   (* Messages that blocked threads are waiting for.        *) 
                   (* If the sender dies, we send them with a failed status *)
                   (* to unblock these threads                              *)
    mastersStatus, (* The status of the master stores at each place         *)
    convFromDead,  (* Recovery variable: set of finishes having transit     *)
                   (* tasks from a dead place                               *)
    convToDead,    (* Recovery variable: set of finishes having transit     *)
                   (* tasks to a dead place                                 *)
    actionName,    (* Debugging variable: the current action name           *)
    depth          (* Debugging variable: the current depth                 *)
    
Vars == << fstates, msgs, pstate,seq, thrds, 
           killed, fmasters, fbackups, waitForMsgs, 
           mastersStatus, convFromDead, convToDead,
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
  /\ fmasters \in [ C!IDRange -> C!MasterFinish ]
  /\ fbackups \in [ C!IDRange -> C!BackupFinish ]
  /\ BACKUP \in [ PLACE -> PLACE ]
  /\ mastersStatus \in [ PLACE -> C!MasterStatus ]
  /\ convFromDead  \subseteq  C!ConvTask
  /\ convToDead \subseteq C!ConvTask
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
                   eroot |-> C!NotID, deny |-> {}, newMaster |-> C!NotPlace,
                   newBackup |-> C!NotPlace, src |-> C!NotPlace,
                   received |-> [ p \in PLACE |-> 0 ] ] ]
  /\ fmasters = [ r \in  C!IDRange  |-> 
                        [  id |-> C!NotID,
                          src |-> C!NotPlace,
                         home |-> C!NotPlace,
                    numActive |-> 0,
                      transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
              adoptedChildren |-> {},
                    newBackup |-> C!NotPlace,
                    isAdopted |-> FALSE,
                   isReleased |-> FALSE,
                 adopterPlace |-> C!NotPlace,
                         _src |-> C!NotPlace,
                        _home |-> C!NotPlace,
                   _numActive |-> 0,
                     _transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
             _adoptedChildren |-> {},
                   _newBackup |-> C!NotPlace,
                   _isAdopted |-> FALSE,
                  _isReleased |-> FALSE,
                  _adopterPlace |-> C!NotPlace
                    ] ]
  /\ fbackups = [ r \in  C!IDRange  |-> 
                        [  id |-> C!NotID,
                          src |-> C!NotPlace,
                         home |-> C!NotPlace,
                    numActive |-> 0,
                      transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
              adoptedChildren |-> {},
                    newMaster |-> C!NotPlace,
                    isAdopted |-> FALSE,
                   isReleased |-> FALSE,
                 adopterPlace |-> C!NotPlace,
                         _src |-> C!NotPlace,
                        _home |-> C!NotPlace,
                   _numActive |-> 0,
                     _transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
             _adoptedChildren |-> {},
                   _newMaster |-> C!NotPlace,
                   _isAdopted |-> FALSE,
                  _isReleased |-> FALSE,
                  _adopterPlace |-> C!NotPlace
                    ] ]
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
                                       fid |-> C!NoParent,
                                       src |-> PROG_HOME ]>> ]
                   ELSE [ tid |-> t, status |-> "idle", 
                          blockingType |-> "NA", 
                          stack |-> <<>> ] ] ]
  /\ runningThrds = { [here |-> PROG_HOME, tid |-> 0 ] }
  /\ blockedThrds = {}
  /\ killed = {}
  /\ waitForMsgs = {}
  /\ convFromDead = {}
  /\ convToDead = {}
  
-----------------------------------------------------------------------------
(***************************************************************************)
(* Helper Actions                                                          *)
(***************************************************************************)
SetActionNameAndDepth(name) ==
  IF depth = DEPTH THEN TRUE ELSE /\ actionName' = name /\ depth' = depth+1
   
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
               /\ Finish(seq.fseq)!Alloc(C!ROOT_FINISH, here, fid, newFid, top.src)
               /\ C!IncrFSEQ
               /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                                << [ b |-> top.b, 
                                                     i |-> curStmt, 
                                                   fid |-> seq.fseq,
                                                   src |-> top.src ]
                                                >> \o tail ]
               /\ IF seq.fseq = C!FIRST_ID
                  THEN /\ fmasters' = fmasters \* will be initialized in transit 
                       /\ fbackups' = fbackups
                  ELSE /\ fmasters' = [fmasters EXCEPT ![encRoot].children = 
                                                                  @ \cup {newFid}]
                       /\ fbackups' = [fbackups EXCEPT ![encRoot].children = 
                                                                  @ \cup {newFid} ]
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, pstate, killed, 
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
                                                      fid |-> newFid,
                                                      src |-> top.src ],
                                                    [   b |-> top.b, 
                                                        i |-> curStmt, 
                                                      fid |-> fid,
                                                      src |-> top.src ]
                                                 >> \o tail ]
                 /\ Finish(seq.fseq)!Alloc(C!ROOT_FINISH, here, fid, newFid, top.src)
                 /\ C!IncrFSEQ
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, msgs, pstate, waitForMsgs,
                  killed, runningThrds, blockedThrds, fmasters, fbackups>>
                    
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
                 act == [ aid |-> seq.aseq, b |-> nested,  fid |-> fid , src |-> top.src ]
                 stkEntry == [b |-> act.b, i |-> C!I_START , fid |-> act.fid, src |-> top.src ]
             IN  /\ SetActionNameAndDepth ( << "SpawnLocalAsync", here >> )
                 /\ IF act.fid # C!NoParent 
                    THEN Finish(act.fid)!NotifyLocalActivitySpawnAndCreation(here, act)
                    ELSE fstates' = fstates
                 /\ C!IncrASEQ
                 /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                                 <<[   b |-> top.b, 
                                                       i |-> curStmt, 
                                                     fid |-> fid,
                                                     src |-> top.src ]
                                                 >> \o tail,
                                           ![here][idle.tid].stack = <<stkEntry>>,
                                           ![here][idle.tid].status = "running" ]
                 /\ runningThrds' = runningThrds \cup { [ here |-> here, tid |-> idle.tid] }
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, msgs, pstate, killed, 
                  fmasters, fbackups, waitForMsgs, blockedThrds>>
                    
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
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, pstate,killed, 
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
  /\ mastersStatus' = [ p \in PLACE |-> IF p # dead
                                        THEN [     status |-> "preConvert", 
                                             lastKilled |-> dead ]
                                        ELSE mastersStatus[p] ]
  /\ LET delMsgs == { m \in msgs : m.dst = dead  }   \*delete messages going to a dead place  
         wfm == { m \in waitForMsgs: m.dst = dead }  \*delete waitForMsgs to a dead place
      IN /\ msgs' = msgs \ delMsgs            
         /\ waitForMsgs' = waitForMsgs \ wfm
  /\ LET mastersWObackups == { id \in C!IDRange : 
                                  /\ fmasters[id].id # C!NotID
                                  /\ fmasters[id].newBackup = C!NotPlace
                                  /\ BACKUP[fstates[id].here] = dead
                                  /\ fstates[id].type = "distroot" }
         backupsWOmasters == { id \in C!IDRange : 
                                  /\ fbackups[id].id # C!NotID
                                  /\ fstates[id].here = dead
                                  /\ fbackups[id].newMaster = C!NotPlace
                                  /\ fstates[id].type = "distroot" }
     IN /\ SetActionNameAndDepth ( << "RunExprOrKill", mastersWObackups, backupsWOmasters  >> )
        /\ fmasters' = [ r \in  C!IDRange  |-> 
                         IF r \in mastersWObackups
                         THEN [ fmasters[r] EXCEPT !.newBackup = BACKUP[dead] ] 
                         ELSE IF r \in backupsWOmasters
                         THEN [ fmasters[r] EXCEPT !.src = fbackups[r].src,
                                                   !.home = fbackups[r].home,
                                                   !.numActive = fbackups[r].numActive,
                                                   !.transit = fbackups[r].transit,
                                                   !.adoptedChildren = fbackups[r].adoptedChildren,
                                                   !.newBackup = BACKUP[fstates[r].here], \*fixme, do I need to change
                                                   !.isAdopted = fbackups[r].isAdopted,
                                                   !.adopterPlace = fbackups[r].adopterPlace,
                                                   !.isReleased = fbackups[r].isReleased,
                                                   !._src = fmasters[r].src,
                                                   !._home = fmasters[r].home,
                                                   !._numActive = fmasters[r].numActive,
                                                   !._transit = fmasters[r].transit,
                                                   !._adoptedChildren = fmasters[r].adoptedChildren,
                                                   !._newBackup = fmasters[r].newBackup,
                                                   !._isAdopted = fmasters[r].isAdopted,
                                                   !._adopterPlace = fmasters[r].adopterPlace,
                                                   !._isReleased = fmasters[r].isReleased ]
                         ELSE fmasters[r] ]
        (*/\ fstates' = [ r \in C!IDRange |-> 
                        IF r \in backupsWOmasters
                        THEN [ fstates[r] EXCEPT !.newMaster = PROG_HOME ]
                        ELSE fstates[r] ] *)
        /\ fbackups' = [ r \in  C!IDRange  |-> 
                         IF r \in mastersWObackups
                         THEN [ fbackups[r] EXCEPT !.src = fmasters[r].src,
                                                   !.home = fmasters[r].home,
                                                   !.numActive = fmasters[r].numActive,
                                                   !.transit = fmasters[r].transit,
                                                   !.adoptedChildren = fmasters[r].adoptedChildren,
                                                   !.newMaster = fbackups[r].newMaster,
                                                   !.isAdopted = fmasters[r].isAdopted,
                                                   !.adopterPlace = fmasters[r].adopterPlace,
                                                   !.isReleased = fmasters[r].isReleased,
                                                   !._src = fbackups[r].src,
                                                   !._home = fbackups[r].home,
                                                   !._numActive = fbackups[r].numActive,
                                                   !._transit = fbackups[r].transit,
                                                   !._adoptedChildren = fbackups[r].adoptedChildren,
                                                   !._newMaster = fbackups[r].newMaster,
                                                   !._isAdopted = fbackups[r].isAdopted,
                                                   !._adopterPlace = fbackups[r].adopterPlace,
                                                   !._isReleased = fbackups[r].isReleased ]
                         ELSE IF r \in backupsWOmasters
                         THEN [ fbackups[r] EXCEPT !.newMaster = PROG_HOME ] 
                         ELSE fbackups[r]  ]

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
           IN /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                               << [  b |-> top.b, 
                                                     i |-> curStmt, 
                                                   fid |-> fid,
                                                   src |-> top.src ]  
                                               >> \o tail ]
              /\ IF PROG[nested].type = "expr"
                 THEN /\ killed' = killed
                      /\ PROG[nested].dst = here
                      /\ mastersStatus' = mastersStatus
                      /\ msgs' = msgs
                      /\ waitForMsgs' = waitForMsgs
                      /\ fmasters' = fmasters
                      /\ fbackups' = fbackups
                      /\ SetActionNameAndDepth ( << "RunExprOrKill", here, PROG[nested].type >> )
                 ELSE /\ Kill(PROG[nested].dst)
  /\ UNCHANGED << fstates, pstate, seq, runningThrds, blockedThrds,
                  convFromDead, convToDead >>
                  
----------------------------------------------------------------------------------
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
               /\ Finish(fid)!NotifyActivityTermination(top.src, FALSE)
               /\ thrds' = [thrds EXCEPT ![here][tid].status = "blocked",
                                         ![here][tid].blockingType = "AsyncTerm" ]
               /\ runningThrds' = runningThrds \ { [ here |-> here, tid |-> tid ] }
               /\ blockedThrds' = blockedThrds \cup { [ here |-> here, tid |-> tid ] }
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, pstate,killed, 
                  fmasters, fbackups >>

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
               /\ Finish(top.fid)!NotifyActivityTermination(top.src, TRUE)
               /\ thrds' = [thrds EXCEPT ![here][tid].status = "blocked",
                                         ![here][tid].blockingType = "FinishEnd" ]
               /\ runningThrds' = runningThrds \ { [ here |-> here, tid |-> tid ] }
               /\ blockedThrds' = blockedThrds \cup { [ here |-> here, tid |-> tid ] }
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, pstate,killed, 
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
               newFID == IF fid = C!NotID THEN seq.fseq ELSE fid
               activity == [aid |-> seq.aseq, b |-> blk, fid |-> newFID, src |-> src ]
               denyList == IF fid = C!NotID THEN {} ELSE fstates[fid]
               accept == \/ ( fid # C!NotID /\ src \notin denyList )
                         \/ ( fid = C!NotID /\ src \notin killed )
           IN /\ SetActionNameAndDepth ( << "RecvAsync", here, "accept", accept >> )
              /\ pid # C!NotID
              /\ src # C!NotPlace
              /\ IF ( fid # C!NotID /\ src \notin denyList )
                 THEN Finish(activity.fid)!NotifyRemoteActivityCreation(
                                                src, activity, msg, C!REMOTE_FINISH, 
                                                here, pid, pid, activity.src )
                 ELSE IF ( fid = C!NotID /\ src \notin killed )
                 THEN Finish(activity.fid)!AllocRemoteAndNotifyRemoteActivityCreation(
                                                src, activity, msg, C!REMOTE_FINISH, 
                                                here, pid, pid, activity.src )
                 ELSE /\ fstates' = fstates
                      /\ C!RecvMsg (msg)
              /\ IF ( ~ accept  )
                 THEN /\ thrds' = thrds
                      /\ runningThrds' = runningThrds
                 ELSE LET idleThrd == FindIdleThread(here)
                          stkEntry == [b |-> activity.b, i |-> C!I_START , 
                                     fid |-> activity.fid, src |-> activity.src ]
                      IN /\ thrds' = [thrds EXCEPT ![here][idleThrd.tid].stack = <<stkEntry>>, 
                                                   ![here][idleThrd.tid].status = "running" ]
                         /\ runningThrds' = runningThrds \cup { [ here |-> here, tid |-> idleThrd.tid] }
              /\ C!IncrAll
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, pstate, 
                  killed, fmasters, fbackups, blockedThrds, waitForMsgs >>

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
               backupPlace == msg.backupPlace
               finishSrc == msg.finishSrc
               masterWFM == [ src |-> rootPlace, 
                              dst |-> here,  
                              fid |-> root,
                           target |-> asyncDst,
                        finishSrc |-> finishSrc,  
                          taskFID |-> msg.taskFID,
                             type |-> "masterTransitDone"  ]
               backupWFM == [ src |-> backupPlace, 
                              dst |-> here,  
                              fid |-> root, 
                           target |-> asyncDst,
                        finishSrc |-> finishSrc,
                             type |-> "backupTransitDone"  ]
           IN /\ SetActionNameAndDepth ( << "MasterTransitDone" , here, 
                                            "success", success, 
                                            "submit", submit >> ) 
              /\ fid = msg.taskFID
              \* Technically, we should check the condition rootPlace \notin killed
              \* if success is true. we should communicate with the backup normally.
              \* the backup then should reject the request and notify the requester
              \* that the master has changed, so that we redirect the call to the
              \* new master.
              /\ IF success /\ submit
                 THEN /\ C!ReplaceMsg ( msg, [   mid |-> seq.mseq, 
                                                 src |-> here, 
                                                 dst |-> backupPlace,
                                              target |-> asyncDst,
                                                 fid |-> root,
                                           finishSrc |-> finishSrc,
                                         knownMaster |-> msg.src,
                                             taskFID |-> fid,
                                                type |-> "backupTransit" ])
                      /\ thrds' = thrds 
                      /\ blockedThrds' = blockedThrds 
                      /\ runningThrds' = runningThrds
                      /\ waitForMsgs' = (waitForMsgs \ {masterWFM}) \cup {backupWFM}
                      /\ C!IncrMSEQ(1)
                 ELSE IF success \*ignore the async, go to the next step
                 THEN /\ C!RecvMsg ( msg )
                      /\ thrds' = [thrds EXCEPT ![here][tid].status = "running",
                                                ![here][tid].stack = 
                                                            <<[  b |-> top.b, 
                                                                 i |-> curStmt, 
                                                               fid |-> fid,
                                                               src |-> top.src ]
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
                                            finishSrc |-> finishSrc,
                                                 type |-> "backupGetNewMaster",
                                              taskFID |-> msg.taskFID,
                                           actionType |-> "transit",
                                            finishEnd |-> FALSE ])
                      /\ thrds' = thrds 
                      /\ blockedThrds' = blockedThrds 
                      /\ runningThrds' = runningThrds
                      /\ waitForMsgs' = waitForMsgs \ {masterWFM}  
                            \* we don't expect the backup to die
                            \* that is why we don't add 
                            \* backupGetAdopterDone in waitForMsgs
                      /\ C!IncrMSEQ(1)
              /\ IF backupPlace = BACKUP[fstates[root].here]
                 THEN fstates' = fstates
                 ELSE fstates' = [fstates EXCEPT ![fid].newBackup = backupPlace ]
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, pstate, killed, 
                  fmasters, fbackups >>

MasterCompletedDone == 
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("masterCompletedDone")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               taskFID == msg.taskFID
               root == msg.fid
               success == msg.success
               rootPlace == C!GetFinishHome(root)
               backupPlace == msg.backupPlace
               finishEnd == msg.finishEnd
               source == msg.source
               masterWFM == [  src |-> rootPlace, 
                               dst |-> here,  
                            source |-> source,
                            target |-> here,
                               fid |-> root,
                           taskFID |-> msg.taskFID,
                              type |-> "masterCompletedDone"  ]
               backupWFM == [    src |-> backupPlace, 
                                 dst |-> here,
                              source |-> source,
                              target |-> here,  
                                 fid |-> root, 
                                type |-> "backupCompletedDone"  ]
           IN /\ SetActionNameAndDepth ( << "MasterCompletedDone", here >> )
              \* Technically, we should check the condition rootPlace \notin killed
              \* if success is true. we should communicate with the backup normally.
              \* the backup then should reject the request and notify the requester
              \* that the master has changed, so that we redirect the call to the
              \* new master.
              /\ IF success
                 THEN /\ C!ReplaceMsg ( msg ,[ mid |-> seq.mseq,
                                               src |-> here, 
                                               dst |-> backupPlace, 
                                            source |-> source,
                                            target |-> here, 
                                               fid |-> root,
                                       knownMaster |-> msg.src,
                                           taskFID |-> taskFID,
                                              type |-> "backupCompleted",
                                         finishEnd |-> finishEnd])
                      /\ IF finishEnd THEN waitForMsgs' = (waitForMsgs \ {masterWFM}) 
                                      ELSE waitForMsgs' = (waitForMsgs \ {masterWFM}) 
                                                                       \cup {backupWFM}
                      /\ C!IncrMSEQ(1)
                 ELSE /\ C!ReplaceMsg ( msg , [   mid |-> seq.mseq, 
                                                  src |-> here, 
                                                  dst |-> C!GetBackup(rootPlace),
                                               source |-> msg.source,
                                               target |-> here,
                                                  fid |-> root,
                                              taskFID |-> msg.taskFID,
                                                 type |-> "backupGetNewMaster",
                                            finishEnd |-> FALSE,
                                            finishSrc |-> C!NotPlace,
                                           actionType |-> "completed" ])
                      /\ waitForMsgs' = waitForMsgs \ {masterWFM} 
                            \* we don't expect backup to die 
                            \* so we don't add backupGetAdopterDone 
                            \* in waitForMsgs
                      /\ C!IncrMSEQ(1)
              /\ IF backupPlace = BACKUP[fstates[root].here]
                 THEN fstates' = fstates
                 ELSE fstates' = [fstates EXCEPT ![taskFID].newBackup = backupPlace ]
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, pstate,   
                  thrds,killed,  fmasters, fbackups, 
                  blockedThrds, runningThrds >>

-------------------------------------------------------------------------------------
BackupGetNewMasterDone ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG ("backupGetNewMasterDone")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst 
                actionType == msg.actionType
                newMaster == msg.newMaster
           IN /\ SetActionNameAndDepth ( << "BackupGetNewMasterDone", here >> ) 
              /\ IF actionType = "transit"
                 THEN /\ C!ReplaceMsg(msg, [ mid |-> seq.mseq,
                                             src |-> here, 
                                             dst |-> newMaster, 
                                          target |-> msg.target, 
                                             fid |-> msg.fid, 
                                       finishSrc |-> msg.finishSrc,
                                         taskFID |-> msg.taskFID,
                                            type |-> "masterTransit" ])
                      /\ C!IncrMSEQ(1)
                      /\ fstates' = [ fstates EXCEPT ![msg.fid].newMaster = newMaster ]
                 ELSE IF actionType = "completed"
                 THEN /\ C!ReplaceMsg(msg, [ mid |-> seq.mseq,
                                             src |-> here, 
                                             dst |-> newMaster, 
                                          source |-> msg.source,
                                          target |-> msg.target, 
                                             fid |-> msg.fid,
                                       finishEnd |-> msg.finishEnd,
                                         taskFID |-> msg.taskFID,
                                            type |-> "masterCompleted" ] )
                      /\ C!IncrMSEQ(1)
                      /\ fstates' = [ fstates EXCEPT ![msg.fid].newMaster = newMaster ]
                 ELSE FALSE
  /\ UNCHANGED << pstate, thrds, killed,  fmasters, fbackups, waitForMsgs, 
                  convFromDead, convToDead, mastersStatus, blockedThrds, runningThrds >>
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
              /\ C!RecvMsg (msg)
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, fstates, seq, 
                  killed, fmasters, fbackups>>
                    
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
               realFID == root
           IN /\ SetActionNameAndDepth ( << "AuthorizeTransitAsync" , here, "to", 
                                            asyncDst, "success", success >> )
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
                                                        fid |-> fid,
                                                        src |-> top.src ]
                                                     >> \o tail ]
              /\ blockedThrds' = blockedThrds \ { [here |-> here, tid |-> tid] }
              /\ runningThrds' = runningThrds \cup { [here |-> here, tid |-> tid] }
              /\ waitForMsgs' = waitForMsgs \ {[ type |-> "backupTransitDone",
                                                  dst |-> msg.dst,
                                                  fid |-> msg.fid,
                                                  src |-> backupPlace,
                                            finishSrc |-> msg.finishSrc,
                                               target |-> asyncDst ]}
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, fstates, pstate, 
                  killed, fmasters, fbackups>>

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
           IN /\ SetActionNameAndDepth ( << "ReleaseRootFinish", here >> )
              /\ C!RecvMsg ( msg )
              /\ fstates' = [fstates EXCEPT ![root].status = "forgotten"]
              /\ waitForMsgs' = waitForMsgs \ {[ src |-> here, 
                                                 dst |-> here,  
                                                 fid |-> root,
                                                type |-> "releaseFinish"  ]}
              /\ UnblockStopFinish(here, tid, root, blk)
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, seq, 
                  killed,  fmasters, fbackups>>

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
               finishSrc == msg.finishSrc
               finishHome == IF fmasters[fid].home = C!NotPlace
                             THEN here
                             ELSE fmasters[fid].home
               backupPlace == IF fmasters[fid].newBackup = C!NotPlace
                              THEN BACKUP[finishHome]
                              ELSE fmasters[fid].newBackup
           IN /\ SetActionNameAndDepth ( << "MasterTransit", here >> )
              /\ mastersStatus[here].status = "running"
              /\ src # C!NotPlace
              /\ fid # C!NotID
              /\ LET submit == src \notin killed /\ target \notin killed
                 IN /\ IF submit
                       THEN IF fmasters[fid].id = C!NotID
                            THEN fmasters' = [fmasters EXCEPT ![fid].id = fid,
                                                              ![fid].transit[src][target] = @ + 1,
                                                              ![fid].transit[here][here] = 1,
                                                              ![fid].numActive  =  @ + 2,
                                                              ![fid].src = finishSrc,
                                                              ![fid].home = src ]
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
                                                   taskFID |-> msg.taskFID,
                                                      type |-> "masterTransitDone",
                                                    submit |-> submit,
                                                   success |-> TRUE,
                                                 finishSrc |-> finishSrc,
                                               backupPlace |-> backupPlace ]) 
                            /\ C!IncrMSEQ(1)
  /\ UNCHANGED << waitForMsgs, convFromDead, convToDead, mastersStatus, 
                  fstates, pstate, thrds, killed, fbackups,
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
                source == msg.source
                target == msg.target
                finishEnd == msg.finishEnd
                finishHome == IF fmasters[fid].home = C!NotPlace
                             THEN here
                             ELSE fmasters[fid].home
                backupPlace == IF fmasters[fid].newBackup = C!NotPlace
                               THEN BACKUP[finishHome]
                               ELSE fmasters[fid].newBackup
                releaseMSG == [ mid |-> seq.mseq,
                                src |-> here, 
                                dst |-> here, 
                                fid |-> fid,
                               type |-> "releaseFinish" ]
                completedDone == [ mid |-> seq.mseq+1,
                                   src |-> here, 
                                   dst |-> src, 
                                source |-> source,
                                target |-> target, 
                                   fid |-> fid, 
                               taskFID |-> msg.taskFID,
                                  type |-> "masterCompletedDone",
                               success |-> TRUE,
                             finishEnd |-> finishEnd,
                           backupPlace |-> backupPlace ]
                adopterCompleted == [ mid |-> seq.mseq+2,
                                      src |-> here, 
                                      dst |-> fmasters[fid].adopterPlace, 
                                   source |-> fmasters[fid].src,
                                   target |-> fmasters[fid].home,
                                      fid |-> fstates[fid].eroot,
                                  taskFID |-> fstates[fid].eroot,
                                finishEnd |-> FALSE,
                                     type |-> "masterCompleted" ]
            IN /\ SetActionNameAndDepth ( << "MasterCompleted", here, "fid", fid, "home", finishHome >> )
               /\ backupPlace # C!NotPlace
               /\ fid # C!NotID
               \*/\ target = src  we cannot check this because the src can be the newMaster of a lost finish
               /\ mastersStatus[here].status = "running"
               /\ IF ( fmasters[fid].transit[source][target] > 0 )
                  THEN /\ fmasters' = [fmasters EXCEPT ![fid].transit[source][target] = @ - 1,
                                                       ![fid].numActive    = @ - 1,
                                                       ![fid].isReleased   = 
                                                           (fmasters[fid].numActive = 1)]
                  ELSE /\ target \in killed
                       /\ fmasters' = fmasters
               /\ IF ( fmasters'[fid].numActive = 0 /\ src \notin killed )
                  THEN /\ IF fmasters[fid].isAdopted
                          THEN /\ C!ReplaceMsgSet (msg, {completedDone, adopterCompleted })
                          ELSE /\ C!ReplaceMsgSet (msg, {releaseMSG, completedDone })
                       /\ C!IncrMSEQ(3)
                  ELSE IF  fmasters'[fid].numActive = 0 
                  THEN /\ IF fmasters[fid].isAdopted
                          THEN /\ C!ReplaceMsg (msg, adopterCompleted)
                          ELSE /\ C!ReplaceMsg (msg, releaseMSG ) 
                       /\ C!IncrMSEQ(3)
                  ELSE IF src \notin killed
                  THEN /\ C!ReplaceMsg (msg, completedDone )
                       /\ C!IncrMSEQ(3)
                  ELSE /\ C!RecvMsg (msg)
                       /\ seq' = seq
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, fstates, pstate, 
                  thrds, killed,  fbackups, waitForMsgs,
                  blockedThrds, runningThrds >>

-------------------------------------------------------------------------------
(***************************************************************************)
(* Finish backup replica actions                                           *)
(***************************************************************************)
BackupGetNewMaster == 
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupGetNewMaster")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               actionType == msg.actionType
               source == msg.source
               target == msg.target
           IN /\ SetActionNameAndDepth ( << "backupGetNewMaster", here >> )
              /\ fbackups[fid].newMaster # C!NotPlace
              /\ IF src \in killed \/ msg.dst \in killed
                 THEN /\ C!RecvMsg (msg)
                      /\ seq' = seq
                 ELSE /\ C!ReplaceMsg (msg, [   mid |-> seq.mseq, 
                                                src |-> here, 
                                                dst |-> src,
                                             source |-> source,
                                             target |-> target,
                                                fid |-> fid,
                                          newMaster |-> fbackups[fid].newMaster,
                                         actionType |-> actionType,
                                          finishEnd |-> msg.finishEnd,
                                          finishSrc |-> msg.finishSrc,
                                          taskFID   |-> msg.taskFID,
                                               type |-> "backupGetNewMasterDone" ])
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << fstates, pstate, thrds, killed,  fmasters, 
                     fbackups, waitForMsgs, mastersStatus, convFromDead, convToDead,
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
               finishSrc == msg.finishSrc
               knownMaster == msg.knownMaster
               correctBackup == IF fmasters[fid].newBackup # C!NotPlace
                                THEN fmasters[fid].newBackup
                                ELSE BACKUP[fstates[fid].here]
               backupKnownMaster == IF fbackups[fid].newMaster # C!NotPlace
                                   THEN fbackups[fid].newMaster
                                   ELSE fstates[fid].here
               masterChanged ==  backupKnownMaster # knownMaster
           IN /\ SetActionNameAndDepth ( << "BackupTransit", here >> )
              /\ correctBackup = here
              /\ IF masterChanged
                 THEN fbackups' = fbackups
                 ELSE IF fbackups[fid].id = C!NotID 
                 THEN fbackups' = [ fbackups EXCEPT ![fid].id = fid,
                                                    ![fid].transit[src][target] = @+1,
                                                    ![fid].transit[src][src] = 1,
                                                    ![fid].numActive  =  @ + 2,
                                                    ![fid].src = finishSrc,
                                                    ![fid].home = src ]
                 ELSE fbackups' = [ fbackups EXCEPT ![fid].transit[src][target] = @ + 1,
                                                    ![fid].numActive  =  @ + 1 ] 
              /\ IF src \in killed 
                 THEN /\ C!RecvMsg (msg) 
                      /\ seq' = seq
                 ELSE IF masterChanged
                 THEN /\ C!ReplaceMsg (msg, [   mid |-> seq.mseq, 
                                                src |-> here, 
                                                dst |-> src,
                                             target |-> target,
                                                fid |-> fid,
                                            taskFID |-> msg.taskFID,
                                               type |-> "masterTransitDone",
                                             submit |-> FALSE,
                                            success |-> FALSE,
                                          finishSrc |-> finishSrc,
                                        backupPlace |-> here ])
                      /\ C!IncrMSEQ(1)
                 ELSE /\ C!ReplaceMsg (msg, [   mid |-> seq.mseq, 
                                                src |-> here, 
                                                dst |-> src,
                                             target |-> target,
                                                fid |-> fid,
                                          finishSrc |-> finishSrc,
                                               type |-> "backupTransitDone",
                                            success |-> TRUE ])
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, fstates, pstate, 
                  thrds, killed, fmasters, waitForMsgs,
                  blockedThrds, runningThrds >>

BackupCompleted ==
  /\ pstate = "running"
  /\ msgs # {}
  /\ LET msg == C!FindMSG("backupCompleted")
     IN /\ msg # C!NotMessage
        /\ LET here == msg.dst
               fid == msg.fid
               src == msg.src
               source == msg.source
               target == msg.target
               finishEnd == msg.finishEnd
               knownMaster == msg.knownMaster
               correctBackup == IF fmasters[fid].newBackup # C!NotPlace
                                THEN fmasters[fid].newBackup
                                ELSE BACKUP[fstates[fid].here]
               backupKnownMaster == IF fbackups[fid].newMaster # C!NotPlace
                                   THEN fbackups[fid].newMaster
                                   ELSE fstates[fid].here
               masterChanged ==  backupKnownMaster # knownMaster 
           IN /\ SetActionNameAndDepth ( << "BackupCompleted", here >> )
              /\ correctBackup = here
              /\ fbackups[fid].transit[source][target] > 0
              /\ fbackups[fid].numActive > 0
              /\ IF masterChanged
                 THEN fbackups' = fbackups
                 ELSE fbackups' = [ fbackups EXCEPT ![fid].transit[source][target] = @ - 1,
                                                   ![fid].numActive    = @ - 1 ]
              /\ IF src \in killed \/ finishEnd
                 THEN /\ C!RecvMsg ( msg ) 
                      /\ seq' = seq
                 ELSE IF masterChanged
                 THEN /\ C!ReplaceMsg ( msg,  [ mid |-> seq.mseq,
                                                src |-> here, 
                                                dst |-> src, 
                                             source |-> source,
                                             target |-> target, 
                                                fid |-> fid, 
                                            taskFID |-> msg.taskFID,
                                               type |-> "masterCompletedDone",
                                            success |-> FALSE,
                                          finishEnd |-> finishEnd,
                                        backupPlace |-> here ] )
                      /\ C!IncrMSEQ(1)
                 ELSE /\ C!ReplaceMsg ( msg,  [   mid |-> seq.mseq, 
                                                  src |-> here, 
                                                  dst |-> src,
                                               target |-> target,
                                                  fid |-> fid,
                                                 type |-> "backupCompletedDone",
                                              success |-> TRUE] )
                      /\ C!IncrMSEQ(1)
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, fstates, pstate,
                  thrds, killed, fmasters, waitForMsgs,
                  blockedThrds, runningThrds >>

------------------------------------------------------------------------------
(***************************************************************************)
(* Recovery actions                                                        *)
(***************************************************************************)
PrepareConvertTasks == 
  /\ pstate = "running"
  /\ \E p \in PLACE : mastersStatus[p].status = "preConvert"
  /\ LET pset == { p \in PLACE : 
                     /\ mastersStatus[p].status = "preConvert"
                     /\ p \notin killed }
         here == IF pset = {} THEN C!NotPlace ELSE CHOOSE p \in pset : TRUE
         dead == mastersStatus[here].lastKilled
     IN /\ SetActionNameAndDepth ( << "PrepareConvertTasks", here >> )
        /\ here # C!NotPlace
        /\ convFromDead' = convFromDead \cup { t \in C!ConvTask :  
                                                 /\ t.to_pl # C!NotPlace
                                                 /\ t.to_pl # dead
                                                 /\ t.to_pl \notin killed
                                                 /\ t.from_pl = dead
                                                 /\ t.fid \in { id \in C!IDRange: 
                                                                   /\ fmasters[id].id # C!NotID
                                                                   /\ \/ fstates[id].here = here
                                                                      \/ /\ fstates[id].here = dead
                                                                         /\ fbackups[id].newMaster = here 
                                                                   /\ fmasters[id].transit[t.from_pl][t.to_pl] > 0 }
                                                 /\ t.here = IF   fstates[t.fid].here # dead 
                                                             THEN fstates[t.fid].here
                                                             ELSE fbackups[t.fid].newMaster }
        /\ convToDead' = convToDead \cup { t \in C!ConvTask :  
                                             /\ t.from_pl # C!NotPlace
                                             /\ t.to_pl = dead
                                             /\ t.fid \in { id \in C!IDRange: 
                                                      /\ fmasters[id].id # C!NotID
                                                      /\ \/ fstates[id].here = here
                                                         \/ /\ fstates[id].here = dead
                                                            /\ fbackups[id].newMaster = here  
                                                      /\ fmasters[id].transit[t.from_pl][t.to_pl] > 0 }
                                             /\ t.here = IF   fstates[t.fid].here # dead 
                                                         THEN fstates[t.fid].here
                                                         ELSE fbackups[t.fid].newMaster }
        /\ mastersStatus' = [ mastersStatus EXCEPT ![here].status = 
                                                IF \E m \in convToDead' : m.here = here 
                                                THEN "convertToDead"
                                                ELSE IF \E m \in convFromDead' : m.here = here  
                                                THEN "convertFromDead"
                                                ELSE "running" ]
  /\ UNCHANGED << fstates, msgs, pstate,seq, thrds, killed, fmasters, fbackups, waitForMsgs, 
                  blockedThrds, runningThrds >>
           
------------------------------------------------------------------------------------------------
GetConvertToDeadSeeker ==
  IF convToDead = {} THEN C!NotConvTask
  ELSE CHOOSE m \in convToDead : mastersStatus[m.here].status = "convertToDead"
       
ConvertToDead ==
  /\ pstate = "running"
  /\ \E p \in PLACE : mastersStatus[p].status = "convertToDead"
  /\ LET convSeeker == GetConvertToDeadSeeker
     IN /\ convSeeker # C!NotConvTask
        /\ convSeeker.here \notin killed
        /\ LET here == convSeeker.here
               source == convSeeker.from_pl
               fid == convSeeker.fid
               target == convSeeker.to_pl \* dead place
               backups == [ r \in  C!IDRange  |-> IF /\ fbackups[r].src = source 
                                                     /\ fstates[r].eroot = fid 
                                                     /\ fbackups[r].home = target
                                                  THEN 1
                                                  ELSE 0 ]
               adoptedChildren == { f \in C!IDRange : backups[f] = 1 }
               t1 == fmasters[fid].transit[source][target] 
               \* a workaround to get the set size assuming it doesn't exceed 5
               t2 == CHOOSE x \in 0..5 : x = backups[1] + backups[2] + backups[3] +
                                                     backups[4] + backups[5]
               releaseMSG == [ mid |-> seq.mseq,
                               src |-> here, 
                               dst |-> here, 
                               fid |-> fid,
                              type |-> "releaseFinish" ]
               adopterCompleted == [ mid |-> seq.mseq+1,
                                     src |-> here, 
                                     dst |-> fmasters'[fid].adopterPlace, 
                                  source |-> fmasters[fid].src,
                                  target |-> fmasters[fid].home,
                                     fid |-> fstates[fid].eroot,
                                 taskFID |-> fstates[fid].eroot,
                               finishEnd |-> FALSE,
                                    type |-> "masterCompleted" ]                                    
           IN /\ SetActionNameAndDepth ( << "ConvertToDead", here, "t1", t1, "t2", t2 >> )
              /\ convToDead' = convToDead \ {convSeeker}
              /\ target = mastersStatus[here].lastKilled
              /\ t1 >= t2
              /\ t1 > 0
              /\ fmasters' = [ r \in  C!IDRange  |-> 
                               IF r = fid
                               THEN [ fmasters[r] EXCEPT !.numActive = @ - (t1 - t2),
                                                         !.transit = [ @ EXCEPT ![source][target] = t2 ],
                                                         !.adoptedChildren = adoptedChildren ]
                               ELSE IF r \in adoptedChildren
                               THEN [ fmasters[r] EXCEPT !.isAdopted = TRUE,
                                                         !.adopterPlace = here ] 
                               ELSE fmasters[r] ]
              /\ fbackups' = [ r \in  C!IDRange  |-> 
                               IF r \in adoptedChildren
                               THEN [ fbackups[r] EXCEPT !.isAdopted = TRUE,
                                                         !.adopterPlace = here ] 
                               ELSE fbackups[r]  ]
              /\ IF fmasters'[fid].numActive = 0
                 THEN IF fmasters'[fid].isAdopted
                      THEN /\ C!SendMsg ( adopterCompleted )
                           /\ C!IncrMSEQ(1)
                      ELSE /\ C!SendMsg ( releaseMSG )
                           /\ C!IncrMSEQ(1)
                 ELSE /\ msgs' = msgs
                      /\ seq' = seq
              /\ IF  \E m \in convToDead' : m.here = here
                 THEN  mastersStatus' = mastersStatus
                 ELSE IF \E m \in convFromDead : m.here = here
                 THEN mastersStatus' = [ mastersStatus EXCEPT ![here].status = "convertFromDead"]
                 ELSE mastersStatus' = [ mastersStatus EXCEPT ![here].status = "running"]
  /\ UNCHANGED << fstates, pstate, thrds, killed, waitForMsgs, convFromDead,
                  blockedThrds, runningThrds >>

              
------------------------------------------------------------------------------------------------
GetConvertFromDeadSeeker ==
  IF convFromDead = {} THEN C!NotConvTask
  ELSE CHOOSE m \in convFromDead : mastersStatus[m.here].status = "convertFromDead"
         
ConvertFromDead ==
  /\ pstate = "running"
  /\ \E p \in PLACE : mastersStatus[p].status = "convertFromDead"
  /\ LET convSeeker == GetConvertFromDeadSeeker
     IN /\ convSeeker # C!NotConvTask
        /\ convSeeker.here \notin killed
        /\ LET here == convSeeker.here
               source == convSeeker.from_pl \* dead place
               fid == convSeeker.fid
               target == convSeeker.to_pl 
               remotes == {f \in C!IDRange:
                             /\ fstates[f].type = "distremote"
                             /\ fstates[f].root = fid
                             /\ fstates[f].here = target }
               remFID == IF remotes = {} 
                         THEN C!NotID 
                         ELSE CHOOSE r \in remotes: TRUE
               t1 == fmasters[fid].transit[source][target]
               t2 == IF remFID = C!NotID
                     THEN 0
                     ELSE fstates[remFID].received[source]
               releaseMSG == [ mid |-> seq.mseq,
                               src |-> here, 
                               dst |-> here, 
                               fid |-> fid,
                              type |-> "releaseFinish" ]
               adopterCompleted == [ mid |-> seq.mseq+1,
                                     src |-> here, 
                                     dst |-> fmasters[fid].adopterPlace, 
                                  source |-> fmasters[fid].src,
                                  target |-> fmasters[fid].home,
                                     fid |-> fstates[fid].eroot,
                                 taskFID |-> fstates[fid].eroot,
                               finishEnd |-> FALSE,
                                    type |-> "masterCompleted" ]
           IN /\ SetActionNameAndDepth ( << "ConvertFromDead", here, "remFID", remFID, "t1", t1, "t2", t2 >> )
              /\ convFromDead' = convFromDead \ {convSeeker}
              /\ t1 >= t2
              /\ t1 > 0
              /\ fmasters' = [ fmasters EXCEPT ![fid].numActive = @ - (t1 - t2) ,
                                               ![fid].transit[source][target] = t2 ]
              /\ IF remFID # C!NotID
                 THEN fstates' = [ fstates EXCEPT ![remFID].deny = @ \cup {source} ]
                 ELSE fstates' = fstates
              /\ IF fmasters'[fid].numActive = 0
                 THEN IF fmasters[fid].isAdopted
                      THEN /\ C!SendMsg ( adopterCompleted )
                           /\ C!IncrMSEQ(1)
                      ELSE /\ C!SendMsg ( releaseMSG )
                           /\ C!IncrMSEQ(1)
                 ELSE /\ msgs' = msgs
                      /\ seq' = seq
              /\ IF  \E m \in convFromDead' : m.here = here
                 THEN  mastersStatus' = mastersStatus
                 ELSE  mastersStatus' = [ mastersStatus EXCEPT ![here].status = "running"]
  /\ UNCHANGED << pstate, thrds, killed,  fbackups, waitForMsgs, convToDead,
                  blockedThrds, runningThrds >>
                       
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
                 /\ IF msg.type = "masterCompletedDone"
                    THEN IF  ~ (\E m \in msgs: \*message has been sent already
                                     /\ m.type = msg.type /\ m.src = msg.src 
                                     /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                     /\ m.source = msg.source
                                     /\ m.target = msg.target
                                     /\ m.taskFID = msg.taskFID
                                     /\ m.success )
                         THEN  /\ msgs' = (msgs \ delMsgs) \cup {
                                        [   mid |-> seq.mseq,
                                            src |-> msg.src,
                                            dst |-> msg.dst,
                                         source |-> msg.source,
                                         target |-> msg.target,
                                            fid |-> msg.fid,
                                        taskFID |-> msg.taskFID,
                                           type |-> "masterCompletedDone",
                                        success |-> FALSE,
                                      finishEnd |-> FALSE,
                                    backupPlace |-> C!NotPlace ] }
                         ELSE  /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "masterTransitDone"
                    THEN IF ~ (\E m \in msgs: \*message has been sent already
                                    /\ m.type = msg.type /\ m.src = msg.src 
                                    /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                    /\ m.taskFID = msg.taskFID
                                    /\ m.success )
                         THEN  /\ msgs' = (msgs \ delMsgs) \cup {
                                        [   mid |-> seq.mseq,
                                            src |-> msg.src,
                                            dst |-> msg.dst,
                                         target |-> msg.target,
                                            fid |-> msg.fid,
                                        taskFID |-> msg.taskFID,
                                      finishSrc |-> msg.finishSrc,
                                           type |-> "masterTransitDone",
                                    backupPlace |-> C!NotPlace,
                                        submit  |-> FALSE,
                                        success |-> FALSE ] }
                         ELSE  /\ msgs' = (msgs \ delMsgs) 
                    ELSE IF msg.type = "backupCompletedDone"
                    THEN IF ~ (\E m \in msgs: \*message has been sent already 
                                    /\ m.type = msg.type /\ m.src = msg.src 
                                    /\ m.dst = msg.dst /\ m.fid = msg.fid 
                                    /\ m.isAdopter = msg.isAdopter /\ m.success )
                         THEN /\ msgs' = (msgs \ delMsgs) \cup {
                                        [   mid |-> seq.mseq,
                                            src |-> msg.src,
                                            dst |-> msg.dst,
                                         target |-> msg.target,
                                            fid |-> msg.fid,
                                           type |-> "backupCompletedDone",
                                        success |-> FALSE ] }                                        
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
                                      finishSrc |-> msg.finishSrc,
                                            fid |-> msg.fid,
                                           type |-> "backupTransitDone",
                                        success |-> FALSE ] }
                         ELSE /\ msgs' = (msgs \ delMsgs)
                    ELSE FALSE
  /\ UNCHANGED << convFromDead, convToDead, mastersStatus, fstates, pstate, 
                  thrds, killed, fmasters, fbackups, 
                  blockedThrds, runningThrds >>
-------------------------------------------------------------------------------
(***************************************************************************)
(* Predicate enumerating all possible next actions                         *)
(***************************************************************************)    
Next ==
  \/ RecvAsync
  \/ ReleaseRootFinish     
  \/ BackupTransit
  \/ BackupCompleted
  \/ BackupGetNewMaster
  \/ BackupGetNewMasterDone
  \/ MasterTransit
  \/ MasterCompleted
  \/ MasterTransitDone     
  \/ MasterCompletedDone
  \/ PrepareConvertTasks
  \/ ConvertFromDead
  \/ ConvertToDead
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
  /\ WF_Vars(StartFinish) 
  /\ WF_Vars(StopFinish)
  /\ WF_Vars(SpawnLocalAsync)
  /\ WF_Vars(SpawnRemoteAsync)
  /\ WF_Vars(TerminateAsync) 
  /\ WF_Vars(ScheduleNestedFinish) 
  /\ WF_Vars(RunExprOrKill)
  /\ WF_Vars(BackupTransit)
  /\ WF_Vars(BackupCompleted)
  /\ WF_Vars(MasterTransit)
  /\ WF_Vars(MasterCompleted)
  /\ WF_Vars(MasterTransitDone)  
  /\ WF_Vars(MasterCompletedDone) 
  /\ WF_Vars(PrepareConvertTasks)
  /\ WF_Vars(ConvertToDead)
  /\ WF_Vars(ConvertFromDead)
  /\ WF_Vars(SimulateFailedResponse)
  /\ WF_Vars(BackupGetNewMaster)
  /\ WF_Vars(BackupGetNewMasterDone)
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
\* Last modified Sun Dec 17 13:42:52 AEDT 2017 by u5482878
\* Last modified Wed Dec 13 23:25:41 AEDT 2017 by shamouda
\* Created Wed Sep 13 12:14:43 AEST 2017 by u5482878
