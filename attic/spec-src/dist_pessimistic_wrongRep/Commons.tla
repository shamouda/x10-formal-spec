------------------------------ MODULE Commons ------------------------------
EXTENDS Integers, Sequences
VARIABLES msgs, fstates, thrds, waitForMsgs, killed, seq
CONSTANTS PLACE, MXFINISHES, PROG_HOME, BACKUP
----------------------------------------------------------------------------
ROOT_FINISH == "distroot"

REMOTE_FINISH == "distremote"

MXTHREADS == 2
MXACTIVITIES == 20
MXMESSAGES == 200

MXFID == MXFINISHES +1

NotID == -1

NoParent == 0

FIRST_ID == 1

PIDRange == NoParent..MXFID

IDRange == FIRST_ID..MXFID

NotPlace == CHOOSE v : v \notin PLACE

ThreadID == 0..MXTHREADS-1

NotThreadID == -5050

EMPTY_BLOCK == -1

BlockID == 0..25\*NBLOCKS-1 

NotBlockID == -1000

StmtID == 0..5\*MXSTMTS-1

I_START == -1

I_PRE_FIN_ALLOC == -2

------------------------------------------------------------------------------
(***************************************************************************)
(* Record Types                                                            *)
(***************************************************************************)
Sequences == [ aseq: 1..MXACTIVITIES, mseq: 1..MXMESSAGES, fseq:IDRange]

\* Each thread has a stack, and this is the stack entry
StackEntry == [ b:BlockID,
                i:StmtID \cup {I_START, I_PRE_FIN_ALLOC},
                fid:PIDRange ]

\* the processing unit of program instructions
Thread ==  [ tid:ThreadID, 
             status:{"idle","running","blocked"},
             blockingType:{"NA","FinishEnd", "AsyncTransit", "FinishAlloc", "AsyncTerm"},
             stack:Seq(StackEntry) ]

\* the activities that are pushed to scheduler's ready queue, 
\* and will eventually be fetched by threads
Activity ==  [ aid:Nat, 
               b:BlockID, 
               fid:IDRange]

NotActivity == [ aid |-> -1, b |-> NotBlockID, fid |-> NotID]

\* Input Program: Block    error used to simulate exceptions
Block == [ b:BlockID \cup {NotBlockID} , 
           type:{"NA", "async", "expr", "finish", "error","kill"}, 
           dst:PLACE \cup {NotPlace}, 
           mxstmt:Nat, 
           stmts:[ StmtID -> BlockID \cup {EMPTY_BLOCK, NotBlockID}],
           ran:BOOLEAN ]

PlaceThread == [ here:PLACE, tid:ThreadID ]

NotPlaceThread == [  here |-> NotPlace,  tid |-> NotThreadID ]

MasterStatus == [ status:{ "running", "seekAdoption", "convertDead" }, 
                  lastKilled:PLACE \cup {NotPlace}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Finish Types                                                            *)
(***************************************************************************)
FinishState == [ id:IDRange \cup {NotID},
                 status:{"unused","waiting","pendingRelease","forgotten"}, 
                 type:{"distroot", "distremote", "NA"}, 
                 count:Nat,
                 here:PLACE \cup {NotPlace}, 
                 parent:PIDRange \cup {NotID}, \* used only in RESILIENT mode
                 root:PIDRange \cup {NotID},  \*root is the same as id for root finishes
                 isGlobal:BOOLEAN, (* used by P0Finish*)
                 eroot:PIDRange \cup {NotID} \* root of the enclosing finish (used in PPoPP14 dist finish)
               ]
                 
MasterFinish == [
    id:IDRange \cup {NotID},
    numActive:Nat,
    live:[ PLACE -> Nat ],
    transit:[ PLACE -> [ PLACE -> Nat ] ],
    liveAdopted:[ PLACE -> Nat ],
    transitAdopted:[ PLACE -> [ PLACE -> Nat ] ],
    children:SUBSET IDRange,
    backupPlace:PLACE \cup {NotPlace},
    isReleased:BOOLEAN
]

BackupFinish == [
    id:IDRange \cup {NotID},
    live:[ PLACE -> Nat ],
    transit:[ PLACE -> [ PLACE -> Nat ] ],
    children:SUBSET IDRange,
    isAdopted:BOOLEAN,
    adoptedRoot:IDRange \cup {NotID},
    numActive:Nat
]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Message Types and Utilities                                             *)
(***************************************************************************)
NotMessage == [fid |-> NotID, src |-> NotPlace]

RemoteAsyncMessages ==  [ mid:Nat, 
               src:PLACE, 
               dst:PLACE, 
               type:{"async"}, 
               b:BlockID, 
               fid:IDRange ]  


ReleaseFinishMessages == [ mid:Nat,
                          src:PLACE, 
                          dst:PLACE, 
                          fid:IDRange,
                          type:{"releaseFinish"} ]

MasterTransitMessages == [ mid |-> Nat,
                           src |-> PLACE, 
                           dst |-> PLACE, 
                        target |-> PLACE, 
                           fid |-> IDRange, 
                    adoptedFID |-> IDRange,
                          type |-> { "masterTransit", "adopterTransit" } ]

MasterLiveMessages ==   [ mid |-> Nat,
                          src |-> PLACE,
                       source |-> PLACE,
                       target |-> PLACE, 
                          dst |-> PLACE, 
                          fid |-> IDRange,  
                          aid |-> Nat,
                         type |-> { "masterLive", "adopterLive" } ]
                         
MasterCompletedMessages == [ mid |-> Nat,
                             src |-> PLACE, 
                             dst |-> PLACE, 
                          target |-> PLACE, 
                             fid |-> IDRange, 
                       finishEnd |-> BOOLEAN,
                            type |-> {"masterCompleted", "adopterCompleted"} ]

                           
BackupTransit == [   mid |-> Nat, 
                     src |-> PLACE, 
                     dst |-> PLACE,
                  source |-> PLACE,
                  target |-> PLACE,
                     fid |-> IDRange,
                    type |-> "backupTransit" ]

MasterORBackupTransitDone == [   mid |-> Nat, 
                         src |-> PLACE, 
                         dst |-> PLACE,
                      target |-> PLACE,
                         fid |-> IDRange,
                        type |-> {"masterTransitDone", "backupTransitDone"},
                   isAdopted |-> BOOLEAN,
                 adoptedRoot |-> IDRange \cup {NotID},
                 adoptedFID  |-> IDRange \cup {NotID},
                     success |-> BOOLEAN ]

BackupLive == [   mid |-> Nat, 
                  src |-> PLACE, 
                  dst |-> PLACE,
               source |-> PLACE,
               target |-> PLACE,
                  fid |-> IDRange,
                  aid |-> Nat,
                 type |-> "backupLive" ]
                 
MasterOrBackupLiveDone == [   mid |-> Nat, 
                      src |-> PLACE, 
                      dst |-> PLACE,
                   target |-> PLACE,
                   source |-> PLACE,
                      fid |-> IDRange,
                      aid |-> Nat,
                     type |-> {"masterLiveDone", "backupLiveDone"},
                isAdopted |-> BOOLEAN,
              adoptedRoot |-> IDRange \cup {NotID},
                   submit |-> BOOLEAN,
                  success |-> BOOLEAN ]
                                                      
BackupCompleted ==  [ mid |-> Nat,
                      src |-> PLACE, 
                      dst |-> PLACE, 
                   target |-> PLACE, 
                      fid |-> IDRange,
                finishEnd |-> BOOLEAN, 
                     type |-> "backupCompleted" ]

MasterOrBackupCompletedDone == [ mid |-> Nat,
                        src |-> PLACE, 
                        dst |-> PLACE, 
                     target |-> PLACE, 
                        fid |-> IDRange, 
                       type |-> { "masterCompletedDone", "backupCompletedDone"},
                  isAdopted |-> BOOLEAN,
                adoptedRoot |-> IDRange \cup {NotID},
                  numActive |-> Nat, 
                    success |-> BOOLEAN,
                 finishEnd  |-> BOOLEAN,
                    release |-> BOOLEAN ]
                     
Messages ==  RemoteAsyncMessages
            \cup MasterTransitMessages
            \cup MasterLiveMessages
            \cup MasterCompletedMessages
            \cup BackupTransit
            \cup MasterORBackupTransitDone
            \cup BackupLive
            \cup MasterOrBackupLiveDone
            \cup BackupCompleted
            \cup MasterOrBackupCompletedDone
            \cup ReleaseFinishMessages

SendMsg(m) == 
    msgs' = msgs \cup {m}

RecvMsg(m) == 
    msgs' = msgs \ {m}

ReplaceMsg(toRemove, toAdd) ==
    msgs' =  (msgs \ {toRemove}) \cup {toAdd}

ReplaceMsgSet(toRemove, toAddSet) ==
    msgs' =  (msgs \ {toRemove}) \cup toAddSet
-------------------------------------------------------------------------------
(***************************************************************************)
(* Predicates to extract the finish id from messages and fstates           *)
(***************************************************************************)
ExtractFIDFromMSG(src, dst, type) ==
    LET mset == { m \in msgs : /\ m.src = src
                               /\ m.dst  = dst
                               /\ m.type = type
                               /\ m.fid \in IDRange
                }
    IN IF mset = {} THEN NotID
       ELSE ( CHOOSE x \in mset : TRUE ).fid

FindIncomingMSG(here, type) ==
    LET mset == { m \in msgs : /\ m.dst  = here
                               /\ m.type = type
                               /\ m.dst \notin killed
                }
    IN IF mset = {} THEN NotMessage
       ELSE CHOOSE x \in mset : TRUE

FindMSG(type) ==
    LET mset == { m \in msgs : /\ m.type = type
                               /\ m.dst \notin killed
                }
    IN IF mset = {} THEN NotMessage
       ELSE CHOOSE x \in mset : TRUE

GetActiveFID(type, here, pid) == 
    LET mset == { id \in IDRange : /\ fstates[id].here = here
                                   /\ fstates[id].root = pid
                                   /\ fstates[id].type = type
                                   /\ fstates[id].status = "waiting"
                }
    IN IF mset = {} THEN NotID
       ELSE ( CHOOSE x \in mset : TRUE )

GetFinishHome(fid) ==
   IF fid = NoParent THEN PROG_HOME ELSE fstates[fid].here

GetEnclosingRoot(parent, me) == 
   IF parent = NoParent THEN NoParent ELSE fstates[parent].root
   
------------------------------------------------------------------------------
(***************************************************************************)
(* Predicate to extract thread ids with a specific status                  *)
(***************************************************************************)
FindThread(here, status) ==
    LET tset == { t \in ThreadID : thrds[here][t].status = status}
    IN IF tset = {} THEN NotThreadID
       ELSE CHOOSE x \in tset : TRUE

FindThread2(here, statusSet) ==
    LET tset == { t \in ThreadID : thrds[here][t].status \in statusSet}
    IN IF tset = {} THEN NotThreadID
       ELSE CHOOSE x \in tset : TRUE
       
------------------------------------------------------------------------------
(***************************************************************************)
(* Resilient Store Types and Utilities                                     *)
(***************************************************************************)
Adopter == [ here:PLACE, child:IDRange \cup {NotID}, adopter:IDRange \cup {NotID} ]

NotAdopter ==  [ here |-> NotPlace, child |-> NotID, adopter |-> NotID ]

ConvTask == [ here:PLACE, fid:IDRange \cup {NotID}, pl:PLACE \cup {NotPlace} ]

NotConvTask == [ here |-> NotPlace, fid |-> NotID, pl |-> NotPlace ]

GetBackup(p) == BACKUP[p]

-----------------------------------------------------------------------------
(****************************************************************************)
(* Utilities to increment sequences used to give unique ids to finish (fseq)*) 
(* messages (mseq), and activities (aseq)                                   *)
(****************************************************************************)
IncrFSEQ ==
  seq' = [ aseq |-> seq.aseq, fseq |-> seq.fseq+1, mseq |-> seq.mseq ]

IncrMSEQ(c) ==
  seq' = [ aseq |-> seq.aseq, fseq |-> seq.fseq, mseq |-> seq.mseq+c ]
  
IncrASEQ ==
  seq' = [ aseq |-> seq.aseq+1, fseq |-> seq.fseq, mseq |-> seq.mseq ]  
  
IncrAll ==
  seq' = [ aseq |-> seq.aseq+1, fseq |-> seq.fseq+1, mseq |-> seq.mseq+1 ]
  
=============================================================================
\* Modification History
\* Last modified Wed Dec 13 15:21:40 AEDT 2017 by u5482878
\* Last modified Tue Dec 05 18:28:01 AEDT 2017 by shamouda
\* Created Wed Sep 27 09:26:18 AEST 2017 by u5482878
