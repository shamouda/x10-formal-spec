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
StackEntry == [ b:BlockID,               \*BlockID == 0..NBLOCKS-1  
                i:StmtID \cup {-1,-2},   \*StmtID == 0..MXSTMTS-1
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
                 
ResilientFinishState == [
    id:IDRange \cup {NotID},
    parent:PIDRange \cup {NotID},
    gfsRoot:PIDRange \cup {NotID},
    gfsRootPlace:PLACE \cup {NotPlace},
    numActive:Nat,
    live:[ PLACE -> Nat ],
    transit:[ PLACE -> [ PLACE -> Nat ] ],
    liveAdopted:[ PLACE -> Nat ],
    transitAdopted:[ PLACE -> [ PLACE -> Nat ] ],
    adopterId:IDRange \cup {NotID},
    isReleased:BOOLEAN
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
    numActive:Nat,
    isReleased:BOOLEAN
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


ReleaseFinishMessages == [ mid:0..100,
                          src:PLACE, 
                          dst:PLACE, 
                          fid:IDRange,
                          type:{"releaseFinish"} ]

AddChildMessages ==  [ mid |-> Nat,
                       src |-> PLACE, 
                       dst |-> PLACE,  
                     eroot |-> IDRange,
                     fid   |-> IDRange, 
                      type |-> "addChild" ] 

MasterTransitMessages == [ mid |-> Nat,
                           src |-> PLACE, 
                           dst |-> PLACE, 
                        target |-> PLACE, 
                           fid |-> IDRange, 
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
                            type |-> { "masterCompleted", "adopterCompleted" } ]

BackupAddChild ==  [   mid |-> Nat, 
                       src |-> PLACE, 
                       dst |-> PLACE,
                     eroot |-> IDRange,
                       fid |-> IDRange,
                      type |-> "backupAddChild" ]

AddChildDone == [   mid |-> Nat, 
                    src |-> PLACE, 
                    dst |-> PLACE,
                  eroot |-> IDRange,
                    fid |-> IDRange,
                   type |-> {"addChildDone", "backupAddChildDone"},
                success |-> BOOLEAN ]

                           

BackupGetAdopter == [   mid |-> Nat, 
                     src |-> PLACE, 
                     dst |-> PLACE,
                     fid |-> IDRange,
              actionType |-> {"transit", "completed", "live"},
                     aid |-> Nat,
               finishEnd |-> BOOLEAN,
                    type |-> "backupGetAdopter" ]

GetAdopterDone == [   mid |-> Nat, 
                      src |-> PLACE, 
                      dst |-> PLACE,
                   source |-> PLACE,
                   target |-> PLACE,
                      fid |-> IDRange,
              adoptedRoot |-> IDRange,
               actionType |-> {"transit", "completed", "live"},
                      aid |-> Nat,
                finishEnd |-> BOOLEAN,
                     type |-> "backupGetAdopterDone" ]

MasterTransitDone == [   mid |-> Nat, 
                         src |-> PLACE, 
                         dst |-> PLACE,
                      target |-> PLACE,
                         fid |-> IDRange,
                        type |-> "masterTransitDone",
                   isAdopter |-> BOOLEAN,
                      submit |-> BOOLEAN,
                     success |-> BOOLEAN,
                     backupPlace |-> PLACE ]

BackupTransit == [   mid |-> Nat, 
                     src |-> PLACE, 
                     dst |-> PLACE,
                  target |-> PLACE,
                     fid |-> IDRange,
               isAdopter |-> BOOLEAN, 
               adoptedFID |-> IDRange \cup {NotID},
                    type |-> "backupTransit" ]
                                         
BackupTransitDone == [   mid |-> Nat, 
                         src |-> PLACE, 
                         dst |-> PLACE,
                      target |-> PLACE,
                         fid |-> IDRange,
                        type |-> "backupTransitDone",
                     success |-> BOOLEAN,
                   isAdopter |-> BOOLEAN, 
                  adoptedFID |-> IDRange \cup {NotID} ]

BackupLive == [   mid |-> Nat, 
                  src |-> PLACE, 
                  dst |-> PLACE,
               source |-> PLACE,
               target |-> PLACE,
                  fid |-> IDRange,
                  aid |-> Nat,
                 type |-> "backupLive",
            isAdopter |-> BOOLEAN,
            adoptedFID |-> IDRange \cup {NotID} ]

BackupLiveDone == [   mid |-> Nat, 
                      src |-> PLACE, 
                      dst |-> PLACE,
                   target |-> PLACE,
                   source |-> PLACE,
                      fid |-> IDRange,
                      aid |-> Nat,
                     type |-> "backupLiveDone",
                  success |-> BOOLEAN,
                isAdopter |-> BOOLEAN,
               adoptedFID |-> IDRange \cup {NotID} ]
               
MasterLiveDone == [   mid |-> Nat, 
                      src |-> PLACE, 
                      dst |-> PLACE,
                   target |-> PLACE,
                   source |-> PLACE,
                      fid |-> IDRange,
                      aid |-> Nat,
                     type |-> "masterLiveDone",
                   submit |-> BOOLEAN,
                  success |-> BOOLEAN,
                isAdopter |-> BOOLEAN,
                backupPlace |-> PLACE ]
                                          
                                                           

                                                      
BackupCompleted ==  [ mid |-> Nat,
                      src |-> PLACE, 
                      dst |-> PLACE, 
                   target |-> PLACE, 
                      fid |-> IDRange, 
                     type |-> "backupCompleted",
                     isAdopter |-> BOOLEAN,
                     finishEnd |-> BOOLEAN ]

MasterCompletedDone == [ mid |-> Nat,
                        src |-> PLACE, 
                        dst |-> PLACE, 
                     target |-> PLACE, 
                        fid |-> IDRange, 
                       type |-> "masterCompletedDone",
                    success |-> BOOLEAN,
                  isAdopter |-> BOOLEAN,
                backupPlace |-> PLACE]

BackupCompletedDone == [ mid |-> Nat,
                        src |-> PLACE, 
                        dst |-> PLACE, 
                     target |-> PLACE, 
                        fid |-> IDRange, 
                       type |-> "backupCompletedDone",
                  isAdopter |-> BOOLEAN,
                    success |-> BOOLEAN ]
                                                                            
DistFinishMessages == AddChildMessages
                     \cup MasterTransitMessages
                     \cup MasterLiveMessages
                     \cup MasterCompletedMessages
                     \cup BackupAddChild
                     \cup AddChildDone
                     \cup BackupGetAdopter
                     \cup GetAdopterDone
                     \cup BackupTransit
                     \cup MasterTransitDone
                     \cup BackupTransitDone
                     \cup BackupLive
                     \cup MasterLiveDone
                     \cup BackupLiveDone
                     \cup BackupCompleted
                     \cup MasterCompletedDone
                     \cup BackupCompletedDone
                     \cup ReleaseFinishMessages
                     
Messages ==  RemoteAsyncMessages
            \cup DistFinishMessages

BackupMessages == BackupAddChild
                  \cup BackupTransit                           
                  \cup BackupLive                           
                  \cup BackupCompleted
                  \cup BackupGetAdopter

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
\* Last modified Mon Dec 11 20:59:18 AEDT 2017 by u5482878
\* Last modified Sun Dec 10 16:09:57 AEDT 2017 by shamouda
\* Created Wed Sep 27 09:26:18 AEST 2017 by u5482878
