------------------------------ MODULE Commons ------------------------------
EXTENDS Integers, Sequences
VARIABLES msgs, fstates, thrds
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS
----------------------------------------------------------------------------
MXFID == MXFINISHES +1

NotID == -1

NoParent == 0

FIRST_ID == 1

PIDRange == NoParent..MXFID

IDRange == FIRST_ID..MXFID

FinishType == {"SPMDroot", "SPMDremote", "root", "remote", "p0root", "p0remote"}

NotPlace == CHOOSE v : v \notin PLACE

NotType == CHOOSE v : v \notin FinishType

ThreadID == 0..MXTHREADS-1

NotThreadID == -5050

EMPTY_BLOCK == -1

BlockID == 0..NBLOCKS-1 

NotBlockID == -1000

StmtID == 0..MXSTMTS-1

------------------------------------------------------------------------------
(***************************************************************************)
(* Record Types                                                            *)
(***************************************************************************)
Exception ==  [ err:{"DPE", "ErrorStmt", "SpawnRemoteAsync"}, 
                from:PLACE ]

SPMDTermMessages == [ mid:Nat, 
                      src:PLACE, 
                      dst:PLACE, 
                      type:{"asyncTerm"}, 
                      fid:IDRange, 
                      excs:Seq(Exception) ]

\* remActs allows negative values for the tasks count, 
\* because default finish allow so
DefTermMessages == [ mid:Nat, 
                     src:PLACE, 
                     dst:PLACE, 
                     type:{"asyncTerm"}, 
                     fid:IDRange, 
                     remActs:[ PLACE -> Int ], excs:Seq(Exception) ] 

RemoteAsyncMessages ==  [ mid:Nat, 
               src:PLACE, 
               dst:PLACE, 
               type:{"async"}, 
               b:BlockID, 
               fid:IDRange ]  

\* Each thread has a stack, and this is the stack entry
StackEntry == [ b:BlockID, 
                i:StmtID \cup {-1,-2}, 
                fid:PIDRange ]

\* the processing unit of program instructions
Thread ==  [ tid:ThreadID, 
             status:{"NA","idle","running","blockedFinish", "blockedAsync"}, 
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

\* remActs allows negative values for the tasks count, 
\* because default finish allows so
FinishState == [ id:IDRange \cup {NotID},
                 status:{"unused","waiting","finished","p0finished","forgotten"}, 
                 type:FinishType \cup {NotType}, 
                 count:Nat,
                 excs:Seq(Exception), 
                 here:PLACE \cup {NotPlace}, 
                 parent:PIDRange \cup {NotID}, \* used only in RESILIENT mode
                 root:PIDRange \cup {NotID},
                 remActs:[ PLACE -> Int ], (* used by default finish *)
                 isGlobal:BOOLEAN (* used by P0Finish*) ]

NotMessage == [fid |-> NotID, src |-> NotPlace]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Resilient Finish Definitions                                            *)
(***************************************************************************)
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
    excs:Seq(Exception),
    adopterId:IDRange \cup {NotID},
    isReleased:BOOLEAN
]

TransitMessages == [ mid:Nat,
                     src:PLACE,
                     dst:PLACE,
                     target:PLACE,
                     fid:IDRange,
                     pfid:PIDRange,
                     rfid:PIDRange,
                     rpl:PLACE,
                     type:{"transit"}]
                     
                     
TransitDoneMessages == [ mid:Nat, 
                         src:PLACE,
                         dst:PLACE,
                         fid:IDRange,
                        type:{"transitDone"}]

LiveMessages == [ mid:Nat,
                src:PLACE, 
                dst:PLACE, 
             target:PLACE, 
                fid:IDRange, 
                aid:Nat,
               type:{"live"} ]


LiveDoneMessages == [ mid:Nat,
                      src:PLACE, 
                      dst:PLACE, 
                      aid:Nat,
                      submit:BOOLEAN,
                      type:{"liveDone"} ]

CompletedMessages == [ mid:Nat,
                       src:PLACE, 
                       dst:PLACE, 
                    target:PLACE, 
                       fid:IDRange, 
                      type:{"completed"} ]

ReleaseFinishMessages == [ mid:0..100,
                          src:PLACE, 
                          dst:PLACE, 
                          fid:IDRange,
                          type:{"releaseFinish"} ]

Adopter == [ child:IDRange \cup {NotID}, adopter:IDRange \cup {NotID}, a:SUBSET IDRange ]

NotAdoptor ==  [ child |-> NotID, adopter |-> NotID, a |-> {} ]

ConvTask == [ fid:IDRange \cup {NotID}, pl:PLACE \cup {NotPlace} ]

NotConvTask == [ fid |-> NotID, pl |-> NotPlace ]

-------------------------------------------------------------------------------
(***************************************************************************)
(* Messaging utilities                                                     *)
(***************************************************************************)
Messages ==   RemoteAsyncMessages
              \cup SPMDTermMessages 
              \cup DefTermMessages
              \cup TransitMessages
              \cup TransitDoneMessages
              \cup LiveMessages
              \cup LiveDoneMessages
              \cup CompletedMessages
              \cup ReleaseFinishMessages

SendMsg(m) == 
    msgs' = msgs \cup {m}
         
RecvMsg(m) == 
    msgs' = msgs \ {m}
    
ReplaceMsg(toRemove, toAdd) ==
    msgs' =  (msgs \ {toRemove}) \cup {toAdd}

\*ReplaceMsg(toRemove, toAdd) == SendMsg(toRemove)
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

------------------------------------------------------------------------------
(***************************************************************************)
(* Predicate to extract thread ids with a specific status                  *)
(***************************************************************************)
FindThread(here, status) ==
    LET tset == { t \in ThreadID : thrds[here][t].status = status}
    IN IF tset = {} THEN NotThreadID
       ELSE CHOOSE x \in tset : TRUE

Ancestors[fid \in IDRange] == 
    IF fid = FIRST_ID THEN {FIRST_ID}
    ELSE {fstates[fid].parent} \cup Ancestors[fstates[fid].parent]

Maximum(S) == 
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n \geq m

LiveAncestors(fid, dead) ==
  { m \in Ancestors[fid] : \/ fstates[m].here # dead
                           (*\/ ~ isDead[PROG_HOME][fstates[m].here] *)}
  
GetAdopter(fid, dead) ==
  Maximum (LiveAncestors(fid, dead))

=============================================================================
\* Modification History
\* Last modified Mon Nov 06 15:52:05 AEDT 2017 by u5482878
\* Last modified Mon Nov 06 00:08:15 AEDT 2017 by shamouda
\* Created Wed Sep 27 09:26:18 AEST 2017 by u5482878
