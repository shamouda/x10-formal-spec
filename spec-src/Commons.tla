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

FinishType == {"SPMDroot", "SPMDremote", "root", "remote"}

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
 
Messages ==  [ mid:Nat, 
               src:PLACE, 
               dst:PLACE, 
               type:{"async"}, 
               b:BlockID, 
               fid:IDRange ]
              \cup SPMDTermMessages 
              \cup DefTermMessages

\* Each thread has a stack, and this is the stack entry
StackEntry == [ b:BlockID, 
                i:StmtID \cup {-1,-2}, 
                fid:PIDRange ]

\* the processing unit of program instructions
Thread ==  [ tid:ThreadID, 
             status:{"NA","idle","running","blocked"}, 
             stack:Seq(StackEntry) ]

\* the activities that are pushed to scheduler's ready queue, 
\* and will eventually be fetched by threads
Activity ==  [ aid:Nat, 
               b:BlockID, 
               fid:IDRange]

\* Input Program: Block    error used to simulate exceptions
Block == [ b:BlockID \cup {NotBlockID} , 
           type:{"NA", "async", "expr", "finish", "error"}, 
           dst:PLACE \cup {NotPlace}, 
           mxstmt:Nat, 
           stmts:[ StmtID -> BlockID \cup {EMPTY_BLOCK, NotBlockID}],
           ran:{0,1}]

\* remActs allows negative values for the tasks count, 
\* because default finish allows so
FinishState == [ id:IDRange \cup {NotID},
                 status:{"unused","waiting","finished","forgotten"}, 
                 type:FinishType \cup {NotType}, 
                 count:Nat,
                 excs:Seq(Exception), 
                 here:PLACE \cup {NotPlace}, 
                 root:PIDRange \cup {NotID},
                 remActs:[ PLACE -> Int ] ]

NotMessage == [fid |-> NotID, src |-> NotPlace]

-------------------------------------------------------------------------------
(***************************************************************************)
(* Messaging utilities                                                     *)
(***************************************************************************)
SendMsg(m) == 
    msgs' = msgs \cup {m}
         
RecvMsg(m) == 
    msgs' = msgs \ {m}
    
ReplaceMsg(toRemove, toAdd) ==
    msgs' = {msgs \ {toRemove}} \cup {toAdd}

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
   
=============================================================================
\* Modification History
\* Last modified Fri Oct 13 11:16:17 AEDT 2017 by u5482878
\* Created Wed Sep 27 09:26:18 AEST 2017 by u5482878
