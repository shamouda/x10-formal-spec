------------------------------ MODULE Parse ------------------------------
EXTENDS Integers, Sequences, TLC

(* Commons *)
VARIABLES msgs, fstates, thrds, waitForMsgs, killed, seq
CONSTANTS PLACE, MXFINISHES, PROG_HOME, BACKUP
(* Self *) 
VARIABLES pstate, program, ppcurStmt, ppProgram
CONSTANTS PROG , NBLOCKS, MXSTMTS

Vars == <<msgs, fstates, thrds, waitForMsgs, killed, seq,
         pstate, program, ppcurStmt, ppProgram>>  
C == INSTANCE Commons

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants  (formulas true in every reachable state.)                   *)
(***************************************************************************)
TypeOK ==
    /\ pstate \in { "init", "running", "terminated","exceptionThrown" }
    /\ program \in [ C!BlockID ->  C!Block ]
    /\ ppcurStmt \in Nat
    
Init == 
    /\ pstate  = "init"
    /\ program = [ b \in  C!BlockID |-> 
                   [ b |->  C!NotBlockID, type  |-> "NA", dst |->  C!NotPlace, 
                      mxstmt |-> 0, stmts |-> [ s \in  C!StmtID |->  C!NotBlockID],
                      ran |-> FALSE ]]
    /\ ppProgram  = PROG
    /\ ppcurStmt  = 0
    /\ msgs = {} 
    /\ fstates = [a |-> 0] 
    /\ thrds = [a |-> 0] 
    /\ waitForMsgs = {} 
    /\ killed = {} 
    /\ seq = [a |-> 1]

ParseInputProgram ==
    /\ pstate = "init"
    /\ Len(ppProgram) > 0
    /\ LET curBlk == Head(ppProgram)
           body == curBlk.body
           t == curBlk.type
           d == curBlk.dst
           b == curBlk.b
           h == IF body = <<>> THEN C!EMPTY_BLOCK ELSE Head(body) 
       IN  /\ IF ( (Len(body) = 0 /\ ppcurStmt = 0) \/ Len(body) = 1)
              THEN /\ ppcurStmt' = 0
                   /\ ppProgram' = Tail(ppProgram)
              ELSE /\ ppcurStmt' = ppcurStmt + 1
                   /\ ppProgram' = << [type |-> t, 
                                       dst |-> d, 
                                       b |-> b, 
                                       body |-> Tail(body),
                                       err |-> "" ] 
                                   >> \o Tail(ppProgram)
           /\ IF  Len(ppProgram') = 0
              THEN  /\ pstate' = "running"
                    /\ program' = [program EXCEPT ![b].b = b,
                                      ![b].type = t,
                                      ![b].dst = d,
                                      ![b].mxstmt = ppcurStmt,
                                      ![b].ran = FALSE,
                                      ![0].ran = TRUE,
                                      ![b].stmts[ppcurStmt] = h ] 
              ELSE  /\ pstate' = pstate
                    /\ program' = [program EXCEPT ![b].b = b,
                                      ![b].type = t,
                                      ![b].dst = d,
                                      ![b].mxstmt = ppcurStmt,
                                      ![b].ran = FALSE,
                                      ![b].stmts[ppcurStmt] = h] 
    /\ UNCHANGED <<msgs, fstates, thrds, waitForMsgs, killed, seq>>

Next == ParseInputProgram 
          
-------------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)          
Spec ==  Init /\ [][Next]_Vars

=============================================================================
\* Modification History
\* Last modified Mon Dec 11 11:43:23 AEDT 2017 by shamouda
\* Last modified Fri Dec 08 22:42:04 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:14:43 AEST 2017 by u5482878
