------------------------------ MODULE Executor ------------------------------
(***************************************************************************)
(* This specification models a subset of X10 programs that use finish,     *) 
(* async at (place), simple expression statements, or error statements that*) 
(* raise exceptions.                                                       *)
(* The following is a sample program that this specification can validate  *)
(*                                                                         *)
(* finish {                                                                *)
(*   expr;                                                                 *)
(*   async at (p1) {                                                       *)
(*     expr;                                                               *)
(*     async at (p2) {                                                     *)
(*       expr;                                                             *)
(*       error;                                                            *)
(*       expr;                                                             *)
(*     }                                                                   *)
(*   }                                                                     *)
(*   async at (p3) {                                                       *)
(*     expr;                                                               *)
(*   }                                                                     *)
(* }                                                                       *)
(* Our goal is to ensure that the finish construct correctly detects       *) 
(* termination and never causes a deadlock                                 *)
(***************************************************************************)
EXTENDS Integers, Sequences
-----------------------------------------------------------------------------
(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANTS 
    PLACE,         (* The set of places                                    *)
    PROG_HOME,     (* The home place from which the program starts         *)
    PROG,          (* The input program as a sequence of async statements  *)
    MXFINISHES,    (* Maximum finish objects including root and remote     *)
    ROOT_FINISH,   (* The selected finish implementation for root          *)
    REMOTE_FINISH, (* The selected finish implementation for remote        *)
    NTHREADS,      (* Minimum number of threads, more threads can be added *) 
                   (* up to MXTHREADS when running threads blocks          *)
    MXTHREADS,     (* Maximum number of threads per place                  *)
    NBLOCKS,       (* Number of blocks in input program                    *)
    MXSTMTS,       (* Maximum number of statements within a block          *)
    MUST_NOT_RUN,  (* Validation constant: blocks that must not run, for   *) 
                   (* example were not executed because of an execption    *)
    MXDEAD         (* Maximum number of places to kill                     *)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Variables common to all finish implementations                          *)
(***************************************************************************)
VARIABLES 
    fstates,       (* Array of finish states                               *)
    msgs,          (* The set of inflight messages. We delete a message    *) 
                   (* once received                                        *) 
    pstate,        (* Program state: init -> running -> terminated         *)
    program,       (* Finish body as a sequence of statements              *)
    aseq,          (* Sequence to generate activity ids                    *)
    fseq,          (* Sequence to generate finish ids                      *)
    mseq,          (* Sequence to generate msg ids                         *)
    readyQ,        (* Queue of ready activities at each place              *)
    thrds,         (* Threads at all places                                *)
    incPar,        (* Increase parallelism requests                        *)
    decPar,        (* Decrease parallelism requests                        *)
    ppProgram,     (* Preprocessing temporary variable: program            *)
    ppcurStmt,     (* Preprocessing temporary variable: current statement  *)
    killed,        (* The set places killed so far                         *)
    killedCnt,     (* Current number of killed places                      *)
    pendingAct,    (* Set of activities received at destination place but  *) 
                   (* need permission from the resilient store to run      *)
    isDead         (* the dead places recognized at each place              *)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Variables used by Place0 resilient store (P0ResStore module)            *)
(***************************************************************************)
VARIABLES
    p0state,       (* The state of place0 resilient store                  *)   
    p0fstates,     (* Place0 resilient finish states                       *)
    p0dead,        (* Last reported dead place                             *)
    p0adoptSet,    (* set used in adoption phase 1: seek adoption          *)
    p0convSet      (* set used in adoption phase 2: convert dead tasks     *)

Vars == << fstates, msgs, pstate, program, aseq, fseq, mseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Predicate to hide the finish implementation                             *)
(***************************************************************************)
Finish(fid) == INSTANCE AbstractFinish

INSTANCE P0ResStore

GetRootFinishId(fid) ==
   IF fid = NoParent THEN NotID
   ELSE IF Finish(fid)!IsRoot THEN fid
   ELSE fstates[fid].root
    
-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants  (formulas true in every reachable state.)                   *)
(***************************************************************************)
TypeOK ==
    /\ fstates \in [IDRange -> FinishState] 
    /\ readyQ \in [ PLACE -> Seq(Activity) ]
    /\ thrds \in  [ PLACE -> [ ThreadID -> Thread ] ]
    /\ msgs \subseteq Messages   
    /\ pstate \in { "init", "running", "terminated","exceptionThrown" }
    /\ program \in [ BlockID -> Block ]
    /\ PROG_HOME \in PLACE
    /\ aseq \in Nat
    /\ mseq \in Nat
    /\ fseq \in IDRange
    /\ ppcurStmt \in Nat
    /\ incPar \in [ PLACE -> Nat ]
    /\ decPar \in [ PLACE -> Nat ]
    /\ MUST_NOT_RUN \subseteq BlockID
    /\ MXDEAD \in Nat
    /\ IF ROOT_FINISH \in {"SPMDroot", "SPMDremote", "root", "remote"} 
       THEN MXDEAD = 0 ELSE TRUE \* don't kill places in non-resilient mode 
    /\ killed \subseteq PLACE
    /\ killedCnt \in Nat
    /\ p0fstates \in [IDRange -> ResilientFinishState] 
    /\ pendingAct \subseteq Activity
    /\ isDead \in [ PLACE -> [ PLACE -> BOOLEAN ] ]
    /\ p0dead \in PLACE \cup {NotPlace}
    /\ p0adoptSet  \subseteq Adopter
    /\ p0convSet \subseteq ConvTask
    /\ p0state \in {"running", "seekAdoption", "convertDead", "release"}
      
StateOK ==
    \/  /\ pstate \in { "init", "running" }
    \/  /\ pstate \in { "terminated", "exceptionThrown" }
        /\ ppProgram = <<>>
        /\ msgs = {}
        /\ \A p \in PLACE : 
            /\ readyQ[p] = <<>>
            /\ \A t \in ThreadID : thrds[p][t].stack = <<>>
        /\ \A fid \in IDRange : 
            /\ fstates[fid].status \in {"unused", "forgotten"}
        /\ IF pstate = "terminated" 
           THEN /\ fstates[FIRST_ID].excs = <<>>  
                /\ \A b \in BlockID : program[b].ran = TRUE \/ program[b].b = NotBlockID
           ELSE /\ fstates[FIRST_ID].excs # <<>>  
                /\ \A b \in BlockID : IF b \in MUST_NOT_RUN 
                                      THEN program[b].ran = FALSE 
                                      ELSE program[b].ran = TRUE  
           
MustTerminate ==
   <> ( pstate \in { "terminated", "exceptionThrown"} )

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init == 
    /\ fstates = [ r \in IDRange |-> 
                   [ id |-> NotID, status |-> "unused", type |-> NotType, 
                     count |-> 0, excs |-> <<>>, here |-> NotPlace, 
                     parent |-> NotID, root |-> NotID, isGlobal |-> FALSE,
                     remActs |-> [ p \in PLACE |-> 0 ] ]]
    /\ readyQ  = [ p \in PLACE |-> <<>> ] 
    /\ msgs    = {}
    /\ pstate  = "init"
    /\ program = [ b \in BlockID |-> 
                   [ b |-> NotBlockID, type  |-> "NA", dst |-> NotPlace, 
                      mxstmt |-> 0, stmts |-> [ s \in StmtID |-> NotBlockID],
                      ran |-> FALSE ]]
    /\ aseq    = 1
    /\ fseq    = FIRST_ID
    /\ mseq    = 0
    /\ ppProgram  = PROG
    /\ ppcurStmt  = 0
    /\ incPar     = [ p \in PLACE |-> 0 ] 
    /\ decPar     = [ p \in PLACE |-> 0 ] 
    /\ thrds      = [ p \in PLACE |-> 
                      [ t \in ThreadID |-> 
                        IF t < NTHREADS 
                        THEN [tid |-> t, status |-> "idle", stack |-> <<>> ]
                        ELSE [tid |-> t, status |-> "NA", stack |-> <<>> ]]]
    /\ killed = {}
    /\ killedCnt = 0
    /\ pendingAct = {}
    /\ isDead = [ p \in PLACE |-> [ z \in PLACE |-> FALSE ]  ]
    /\ p0fstates = [ r \in IDRange |-> [   id |-> NotID,
                                       parent |-> NotID,
                                      gfsRoot |-> NotID,
                                 gfsRootPlace |-> NotPlace,
                                    numActive |-> 0,
                                         live |-> [ p \in PLACE |-> 0 ],
                                      transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                                  liveAdopted |-> [ p \in PLACE |-> 0 ],
                               transitAdopted |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                                         excs |-> <<>>,
                                    adopterId |-> NotID,
                                    isReleased|-> FALSE
                                       ]
                   ] 
    /\ p0dead = NotPlace
    /\ p0adoptSet = {}
    /\ p0convSet = {}
    /\ p0state = "running"
    
(***************************************************************************)
(* Parsing the input program into another format for easier processing     *)
(***************************************************************************)
ParseInputProgram ==
    /\ pstate = "init"
    /\ Len(ppProgram) > 0
    /\ LET curBlk == Head(ppProgram)
           body == curBlk.body
           t == curBlk.type
           d == curBlk.dst
           b == curBlk.b
           h == IF body = <<>> THEN EMPTY_BLOCK ELSE Head(body) 
       IN  /\ program' = [program EXCEPT ![b].b = b,
                                      ![b].type = t,
                                      ![b].dst = d,
                                      ![b].mxstmt = ppcurStmt,
                                      ![b].ran = FALSE,
                                      ![b].stmts[ppcurStmt] = h]
           /\ IF ( (Len(body) = 0 /\ ppcurStmt = 0) \/ Len(body) = 1)
              THEN /\ ppcurStmt' = 0
                   /\ ppProgram' = Tail(ppProgram)
              ELSE /\ ppcurStmt' = ppcurStmt + 1
                   /\ ppProgram' = << [type |-> t, 
                                       dst |-> d, 
                                       b |-> b, 
                                       body |-> Tail(body),
                                       err |-> "" ] 
                                   >> \o Tail(ppProgram)
    /\ UNCHANGED <<fstates, pstate, msgs, aseq, fseq, mseq, readyQ, 
                   thrds, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

(***************************************************************************)
(* Start program execution (i.e. simulate X10's main method )              *)
(***************************************************************************)
Run ==
    /\ pstate = "init"
    /\ Len(ppProgram) = 0
    /\ pstate' = "running"
    /\ LET curStmt == IF program[0].type = "finish" THEN -2 ELSE -1
       IN  thrds' = [ thrds EXCEPT ![PROG_HOME][0].stack = 
                                              <<[  b |-> 0, 
                                                   i |-> curStmt, 
                                                 fid |-> NoParent ]
                                              >>,
                                  ![PROG_HOME][0].status = "running" ]
    /\ program' = [program EXCEPT ![0].ran = TRUE] 
    /\ UNCHANGED <<fstates, msgs, aseq, fseq, mseq, readyQ, ppProgram, 
                   ppcurStmt, incPar, decPar,p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Helper Actions                                                          *)
(***************************************************************************)
\* Push activity to the ready queue
PushReadyFIFO(here, activity) ==
    /\ readyQ' = [readyQ EXCEPT![here] = Append (@, activity)]

\* poll activity from the ready queue    
PollReadyFIFO(here) ==
    /\ readyQ[here] # <<>>
    /\ readyQ' = [readyQ EXCEPT![here] = Tail (readyQ[here])]

\* record activity pending approval from the resilient store
AddPendingActivity(activity) ==
    /\ pendingAct' = pendingAct \cup {activity}

\* search for a pending activity given its id
FindPendingActivity(actId) ==
    LET aset == { a \in pendingAct : a.aid  = actId }
    IN IF aset = {} THEN NotActivity
       ELSE CHOOSE x \in aset : TRUE
       
\* Push an activity received from another place
RecvAndSubmitRemoteActivity(here, src, act, msg) == 
    /\ Finish(act.fid)!NotifyRemoteActivityCreation(src, act, msg)
    /\ IF Finish(act.fid)!IsResilient 
       THEN /\ AddPendingActivity(act)
            /\ readyQ' = readyQ
       ELSE /\ PushReadyFIFO(here, act)
            /\ pendingAct' = pendingAct
            /\ mseq' = mseq

\* Push a local activity
SubmitLocalActivity(here, act) ==     
    /\ IF act.fid # NoParent 
       THEN Finish(act.fid)!NotifyLocalActivitySpawnAndCreation(here, act)
       ELSE fstates' = fstates
    /\ PushReadyFIFO(here, act)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Increase/decrease parallelism actions                                   *)
(***************************************************************************)
\* Increase the number of worker threads 
IncreaseParallelism(here) ==
   /\ here \notin killed
   /\ pstate = "running" 
   /\ incPar[here] > 0
   /\ LET tid == FindThread(here, "NA")
      IN /\ tid # NotThreadID
         /\ incPar' = [incPar EXCEPT ![here] = @-1]
         /\ thrds' = [thrds EXCEPT ![here][tid].status = "idle"]
   /\ UNCHANGED <<fstates, msgs, pstate, program, aseq, fseq, mseq, readyQ, 
                  ppProgram, ppcurStmt, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                  killed, killedCnt, p0fstates, pendingAct, isDead>>
           
\* Decrease the number of worker threads
DecreaseParallelism(here) ==
   /\ here \notin killed
   /\ pstate = "running" 
   /\ decPar[here] > 0
   /\ LET tid == FindThread(here, "idle")
      IN /\ tid # NotThreadID
         /\ decPar' = [decPar EXCEPT ![here] = @-1]
         /\ thrds' = [thrds EXCEPT ![here][tid].status = "NA"]
   /\ UNCHANGED <<fstates, msgs, pstate, program, aseq, fseq, mseq, readyQ, 
                  ppProgram, ppcurStmt, incPar, p0dead,p0adoptSet, p0state,p0convSet,
                  killed, killedCnt, p0fstates, pendingAct, isDead>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Program Execution Actions                                               *)
(***************************************************************************)
\* Idle thread fetching a ready activity
IThreadFetchActivity(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "idle"
    /\ PollReadyFIFO(here)
    /\ LET  act == Head(readyQ[here])
            stkEntry == [b |-> act.b, i |-> -1 , fid |-> act.fid]
       IN   /\ thrds' = [thrds EXCEPT ![here][tid].stack = <<stkEntry>>,
                                   ![here][tid].status = "running" ]
            /\ program' = [program EXCEPT ![act.b].ran = TRUE ] 
    /\ UNCHANGED <<fstates, msgs, pstate, aseq, fseq, mseq, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Running thread processing an expression
RThreadRunExpr(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           blk == top.b
       IN  /\ program[blk].type = "expr"
           /\ IF    Len(thrds[here][tid].stack) = 1         
              THEN  thrds' = [thrds EXCEPT ![here][tid].stack = <<>>,
                                           ![here][tid].status = "idle" ]
              ELSE  thrds' = [thrds EXCEPT ![here][tid].stack = Tail(@) ]
    /\ UNCHANGED <<fstates, msgs, pstate, program, aseq, fseq, mseq, readyQ, 
                   ppProgram, ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Running thread processing a kill statement
RThreadRunKill(here, tid) ==
    /\ here \notin killed
    /\ here # PROG_HOME  
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           blk == top.b
       IN  /\ program[blk].type = "kill"
           /\ killed' = killed \cup {here}
           /\ killedCnt' = killedCnt + 1 
    /\ UNCHANGED << fstates, msgs, pstate, program, aseq, fseq, mseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar, p0convSet,
           p0fstates, pendingAct, isDead,p0adoptSet,p0state >>

\* Running thread processing the end of an async block
RThreadRunAsyncEnd(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           blk == top.b
           fid == top.fid
       IN  /\ program[blk].type = "async"
           /\ program[blk].mxstmt = top.i
           /\ Finish(fid)!NotifyActivityTermination
           /\ IF    Len(thrds[here][tid].stack) = 1
              THEN  thrds' = [thrds EXCEPT ![here][tid].stack = <<>>,
                                           ![here][tid].status = "idle" ]
              ELSE  thrds' = [thrds EXCEPT ![here][tid].stack = Tail(@) ]
           /\ IF  blk = 0
              THEN pstate' = "terminated"
              ELSE pstate' = pstate
    /\ UNCHANGED <<msgs, pstate, program, aseq, fseq, mseq, readyQ, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Running thread processing the end of a finish block and blocking itself
RThreadRunFinishEnd(here, tid) == 
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
       IN  /\ program[top.b].type = "finish"
           /\ program[top.b].mxstmt = top.i
           /\ Finish(top.fid)!NotifyActivityTermination
           /\ thrds' = [thrds EXCEPT ![here][tid].status = "blockedFinish"]
           /\ incPar' = [incPar EXCEPT ![here] = @+1]   
    /\ UNCHANGED <<msgs, pstate, program, aseq, fseq, mseq, readyQ, ppProgram, 
                   ppcurStmt, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Terminated finish unblocks its thread
BThreadUnblockFinish(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "blockedFinish"
    /\ LET top == Head(thrds[here][tid].stack)
           blk == top.b
           fid == top.fid
       IN  /\ program[blk].type = "finish"
           /\ program[blk].mxstmt = top.i
           /\ Finish(fid)!Terminated
           /\ decPar' = [decPar EXCEPT ![here] = @+1]   
           /\ IF    Len(thrds[here][tid].stack) = 1
              THEN  thrds' = [thrds EXCEPT ![here][tid].stack = <<>>,
                                           ![here][tid].status = "idle" ]
              ELSE  thrds' = [thrds EXCEPT ![here][tid].stack = Tail(@),
                                           ![here][tid].status = "running" ]
           /\ IF  blk = 0 /\ Finish(fid)!HasExceptions 
              THEN pstate' = "exceptionThrown"
              ELSE IF blk = 0 /\ ~ Finish(fid)!HasExceptions 
              THEN pstate' = "terminated"
              ELSE pstate' = pstate
    /\ UNCHANGED <<fstates, msgs, program, aseq, fseq, mseq, readyQ, 
                   ppProgram, ppcurStmt, incPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>


\* Running thread processing the beginning of a finish block
RThreadRunFinishFirstStmt(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
       IN  /\ program[blk].type = "finish"
           /\ lstStmt = -2
           /\ Finish(fseq)!Alloc(ROOT_FINISH, here, fid, fseq)
           /\ thrds' = [thrds EXCEPT ![here][tid].stack = << [ b |-> top.b, 
                                                               i |-> curStmt, 
                                                             fid |-> fseq ]
                                                          >> \o tail ]
           /\ fseq' = fseq + 1
    /\ UNCHANGED <<msgs, pstate, program, aseq, mseq, readyQ, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Processing a nested local async in the currently running block
RThreadRunNestedLocalAsync(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           nested == program[blk].stmts[curStmt]
       IN  /\ program[blk].type \notin{ "expr" , "kill" }
           /\ curStmt >= 0  
           /\ curStmt <= program[blk].mxstmt
           /\ program[nested].type = "async"
           /\ program[nested].dst = here
           /\ SubmitLocalActivity(here, [ aid |-> aseq, 
                                            b |-> nested, 
                                          fid |-> fid ] )
           /\ aseq' = aseq + 1
           /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                           <<[   b |-> top.b, 
                                                 i |-> curStmt, 
                                               fid |-> fid]
                                           >> \o tail ]
    /\ UNCHANGED <<msgs, pstate, program, fseq, mseq, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Processing a nested remote async in the currently running block
RThreadRunNestedRemoteAsync(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           root == GetRootFinishId(fid)
           nested == program[blk].stmts[curStmt]
       IN  /\ program[blk].type \notin {"expr", "kill"}
           /\ fid # NoParent
           /\ curStmt >= 0  
           /\ curStmt <= program[blk].mxstmt
           /\ program[nested].type = "async"
           /\ program[nested].dst # here
           /\ IF    Finish(fid)!IsResilient
              THEN  /\ Finish(fid)!NotifySubActivitySpawn(program[nested].dst)
                    /\ thrds' = [thrds EXCEPT ![here][tid].status = "blockedAsync"]
                    /\ incPar' = [incPar EXCEPT ![here] = @+1]
              ELSE  \/  /\ Finish(fid)!NotifySubActivitySpawn(program[nested].dst)
                        /\ SendMsg ([ mid |-> mseq, 
                                      src |-> here, 
                                      dst |-> program[nested].dst, 
                                     type |-> "async", 
                                      fid |-> root, 
                                        b |-> nested ])
                        /\ mseq' = mseq + 1
                        /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                                         <<[  b |-> top.b, 
                                                              i |-> curStmt, 
                                                            fid |-> fid ]
                                                         >> \o tail ]
                        /\ incPar' = incPar
                    \/  /\ Finish(fid)!NotifySubActivitySpawnError(program[nested].dst) 
                        /\ msgs' = msgs
                        /\ mseq' = mseq
                        /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                                         <<[ b |-> top.b, 
                                                             i |-> program[blk].mxstmt, 
                                                           fid |-> fid ]
                                                         >> \o tail ]
                        /\ incPar' = incPar
    /\ UNCHANGED <<pstate, program, aseq, fseq, readyQ, ppProgram, 
                   ppcurStmt, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Processing a nested finish in the currently running block
RThreadRunNestedFinish(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           nested == program[blk].stmts[curStmt]
       IN  /\ program[blk].type \notin { "expr", "kill" }
           /\ curStmt >= 0  
           /\ curStmt <= program[blk].mxstmt
           /\ program[nested].type = "finish"
           /\ program[nested].dst = here
           /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                           << [   b |-> nested, 
                                                  i |-> -2, 
                                                fid |-> fid ],
                                              [   b |-> top.b, 
                                                  i |-> curStmt, 
                                                fid |-> fid ]
                                           >> \o tail ]
           /\ program' = [program EXCEPT ![nested].ran = TRUE ] 
    /\ UNCHANGED <<fstates, msgs, pstate, aseq, fseq, mseq, readyQ, 
                   ppProgram, ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Processing a nested expression in the currently running block
RThreadRunNestedExprORKill(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           nested == program[blk].stmts[curStmt]
       IN  /\ program[blk].type \notin { "expr", "kill" }
           /\ curStmt >= 0  
           /\ curStmt <= program[blk].mxstmt
           /\ program[nested].type \in {"expr", "kill"}
           /\ program[nested].dst = here
           /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                           << [  b |-> nested, 
                                                 i |-> -1, 
                                               fid |-> fid ],
                                              [  b |-> top.b, 
                                                 i |-> curStmt, 
                                               fid |-> fid ]  
                                           >> \o tail ]
           /\ program' = [program EXCEPT ![nested].ran = TRUE ] 
    /\ UNCHANGED <<fstates, msgs, pstate, aseq, fseq, mseq, readyQ, 
                   ppProgram, ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Processing a nested error in the currently running block
RThreadRunNestedError(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           nested == program[blk].stmts[curStmt]
       IN  /\ program[blk].type \notin { "expr" , "error", "kill" }
           /\ curStmt >= 0  
           /\ curStmt <= program[blk].mxstmt
           /\ program[nested].type = "error"
           /\ program[nested].dst = here
           /\ thrds' = [thrds EXCEPT ![here][tid].stack = \* jump to the end of 
                                                          \* the current block
                                           << [  b |-> top.b, 
                                                 i |-> program[blk].mxstmt,  
                                               fid |-> fid ]  
                                           >> \o tail ]
           /\ program' = [program EXCEPT ![nested].ran = TRUE ] 
           /\ Finish(fid)!PushException([err |-> "ErrorStmt", from |-> here])
    /\ UNCHANGED <<msgs, pstate, aseq, fseq, mseq, readyQ,p0adoptSet, p0state,p0convSet, 
                   ppProgram, ppcurStmt, incPar, decPar, p0dead,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Parsing an incoming async and creating its RemoteFinish object
CreateRemoteFinish(here) == 
    /\ here \notin killed
    /\ pstate = "running" 
    /\ LET msg == FindIncomingMSG(here, "async")
           pid == msg.fid
           fid == GetActiveFID(REMOTE_FINISH, here, pid)
       IN /\ pid # NotID
          /\ fid = NotID
          /\ Finish(fseq)!Alloc(REMOTE_FINISH, here, pid, pid)
          /\ fseq' = fseq + 1
    /\ UNCHANGED <<msgs, pstate, program, aseq, mseq, readyQ, thrds, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* Pushing an incoming async to the ready queue
RecvAsync (here) == 
    /\ here \notin killed
    /\ pstate = "running"
    /\ LET msg == FindIncomingMSG(here, "async")
           pid == msg.fid
           fid == GetActiveFID(REMOTE_FINISH, here, pid)
           src == msg.src
           blk == msg.b
       IN /\ pid # NotID
          /\ fid # NotID
          /\ src # NotPlace
          /\ RecvAndSubmitRemoteActivity(here, src, [aid |-> aseq, b |-> blk, fid |-> fid ],
                                              [  mid |-> msg.mid, 
                                                 src |-> msg.src, 
                                                 dst |-> here, 
                                                type |-> "async", 
                                                   b |-> blk, 
                                                 fid |-> pid])
          /\ aseq' = aseq + 1
    /\ UNCHANGED <<pstate, program, fseq, thrds, ppProgram, ppcurStmt, 
                   p0dead, p0adoptSet, p0state,p0convSet,
                   incPar, decPar, killed, killedCnt, p0fstates, isDead>>

\* Enclosing finish receiving a termination signal from a remote task 
RecvAsyncTerm(here) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ LET msg == FindIncomingMSG(here, "asyncTerm")
           fid == msg.fid
           src == msg.src
       IN  /\ fid # NotID
           /\ src # NotPlace
           /\ Finish(fid)!ProcessChildTermMsg(msg)
    /\ UNCHANGED <<pstate, program, aseq, fseq, mseq, readyQ, thrds, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

\* RemoteFinish notifying its RootFinish that it terminated
NotifyParentFinish(fid) ==
    /\ fstates[fid].here \notin killed 
    /\ pstate = "running"
    /\ fstates[fid].status = "finished"
    /\ LET type == fstates[fid].type
           pid == fstates[fid].root           
       IN  /\ Finish(fid)!SendTermMsg
    /\ UNCHANGED <<program, pstate, aseq, fseq, readyQ, thrds, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead>>

------------------------------------------------------------------------------
(***************************************************************************)
(* Simulating place failure                                                *)
(***************************************************************************)
Kill(here) ==
    /\ pstate = "running"
    /\ here # PROG_HOME 
    /\ here \notin killed
    /\ killedCnt < MXDEAD
    /\ killed' = killed \cup {here}
    /\ killedCnt' = killedCnt + 1
    /\ UNCHANGED << fstates, msgs, pstate, program, aseq, fseq, mseq, 
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar, p0adoptSet, p0state,p0convSet,
           p0fstates, pendingAct, isDead, p0dead>>       

\* When a place detects that another place has died for the first time
NotifyPlaceDeath(here) == 
    /\ here \notin killed
    /\ pstate = "running"
    /\ LET allNewDead == { p \in killed : ~ isDead[here][p] }
           oneNewDead == IF allNewDead = {} THEN NotPlace ELSE CHOOSE p \in allNewDead : TRUE
       IN  /\ oneNewDead # NotPlace
           /\ isDead[here][oneNewDead] = FALSE
           /\ isDead' = [isDead EXCEPT ![here][oneNewDead] = TRUE]
           /\ IF here = PROG_HOME
              THEN P0NotifyPlaceDeath(oneNewDead)
              ELSE p0dead' = p0dead /\ p0adoptSet' = p0adoptSet /\ p0state' = p0state
    /\ UNCHANGED <<fstates, msgs, pstate, program, aseq, fseq, mseq, 
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar, p0convSet,
           killed, killedCnt, p0fstates, pendingAct >>

\* resilient store has changed the transit counters
BThreadUnblockResilientAsync(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "blockedAsync"
    /\ msgs # {}
    /\ LET msg == FindIncomingMSG(here, "transitDone")
           top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           root == GetRootFinishId(fid)
           nested == program[blk].stmts[curStmt]
       IN  /\ msg # NotMessage
           /\ decPar' = [decPar EXCEPT ![here] = @+1]
           /\ ReplaceMsg ( [ mid |-> msg.mid,
                             src |-> PROG_HOME,
                             dst |-> here,
                             fid |-> msg.fid,
                            type |-> "transitDone"] ,  
                           [ mid |-> mseq, 
                               src |-> here, 
                               dst |-> program[nested].dst, 
                              type |-> "async", 
                               fid |-> root, 
                                 b |-> nested ])
           /\ mseq' = mseq + 1
           /\ thrds' = [thrds EXCEPT  ![here][tid].status = "running",
                                      ![here][tid].stack = 
                                                 <<[  b |-> top.b, 
                                                      i |-> curStmt, 
                                                    fid |-> fid ]
                                                 >> \o tail ]
    /\ UNCHANGED << fstates, pstate, program, aseq, fseq,
           readyQ, ppProgram, ppcurStmt, incPar,p0dead,p0adoptSet, p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead >>

\* resilient store has given permission to execute a remote activity
SubmitPendingActivity(here) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ pendingAct # {}
    /\ msgs # {}
    /\ LET msg == FindIncomingMSG(here, "liveDone")
           actId == msg.aid
           activity == FindPendingActivity(actId)
           submit == msg.submit
       IN  /\ msg # NotMessage
           /\ activity # NotActivity
           /\ RecvMsg ( [   mid |-> msg.mid,
                            src |-> PROG_HOME, 
                            dst |-> here, 
                            aid |-> actId,
                            submit |-> submit,
                           type |-> "liveDone" ])
           /\ IF submit 
              THEN PushReadyFIFO(here, activity) 
              ELSE readyQ' = readyQ
           /\ pendingAct' = pendingAct \ {activity}
    /\ UNCHANGED << fstates, pstate, program, aseq, fseq, mseq, 
           thrds, ppProgram, ppcurStmt, incPar, decPar,p0dead,p0adoptSet, p0state,p0convSet,
           killed, killedCnt, p0fstates, isDead >>

ReleaseRootFinish(here) == 
    /\ here \notin killed
    /\ pstate = "running"
    /\ msgs # {}
    /\ LET msg == FindIncomingMSG(here, "releaseFinish")
           fid == msg.fid           
       IN  /\ msg # NotMessage
           /\ RecvMsg ( [ mid |-> msg.mid,
                          src |-> PROG_HOME, 
                          dst |-> here, 
                          fid |-> fid,
                         type |-> "releaseFinish" ] )
           /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"]
    /\ UNCHANGED << pstate, program, aseq, fseq, mseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0adoptSet, p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead >>

-------------------------------------------------------------------------------
(***************************************************************************)
(* Predicate enumerating all possible next actions                         *)
(***************************************************************************)    
Next ==
    \/ ParseInputProgram 
    \/ Run
    \/ RecvTransit(PROG_HOME)      \* resilient finish
    \/ RecvLive(PROG_HOME)         \* resilient finish
    \/ RecvCompleted(PROG_HOME)    \* resilient finish
    \/ SeekAdoption(PROG_HOME)     \* resilient finish
    \/ ConvertDeadActivities(PROG_HOME) \* resilient finish
    \/ ReleaseAll(PROG_HOME)
    \/ \E here \in PLACE :
        \/ IncreaseParallelism(here)
        \/ DecreaseParallelism(here) 
        \/ CreateRemoteFinish(here)
        \/ RecvAsync (here) 
        \/ RecvAsyncTerm(here)
        \/ NotifyPlaceDeath(here)      \* resilient finish
        \/ SubmitPendingActivity(here) \* resilient finish
        \/ ReleaseRootFinish(here)     \* resilient finish
        \/  \E tid \in ThreadID :
            \/ IThreadFetchActivity(here, tid)
            \/ RThreadRunExpr(here, tid)
            \/ RThreadRunKill(here, tid) 
            \/ RThreadRunAsyncEnd(here, tid) 
            \/ RThreadRunFinishEnd(here, tid)
            \/ BThreadUnblockFinish(here, tid) 
            \/ RThreadRunFinishFirstStmt(here, tid) 
            \/ RThreadRunNestedLocalAsync(here, tid) 
            \/ RThreadRunNestedRemoteAsync(here, tid) 
            \/ RThreadRunNestedFinish(here, tid) 
            \/ RThreadRunNestedExprORKill(here, tid)
            \/ RThreadRunNestedError(here, tid)
            \/ BThreadUnblockResilientAsync(here, tid)  \* resilient finish
        \/  \E fid \in IDRange : 
            \/ NotifyParentFinish(fid)

-------------------------------------------------------------------------------
(***************************************************************************)
(* Asserting fairness properties to all actions                            *)
(***************************************************************************)
Liveness ==
    /\ WF_Vars(ParseInputProgram)
    /\ WF_Vars(Run)
    /\ WF_Vars(RecvTransit(PROG_HOME))       \* resilient finish
    /\ WF_Vars(RecvLive(PROG_HOME))          \* resilient finish
    /\ WF_Vars(RecvCompleted(PROG_HOME))     \* resilient finish
    /\ WF_Vars(SeekAdoption(PROG_HOME))      \* resilient finish
    /\ WF_Vars(ConvertDeadActivities(PROG_HOME)) \* resilient finish
    /\ WF_Vars(ReleaseAll(PROG_HOME))
    /\ \A here \in PLACE : 
          WF_Vars(IncreaseParallelism(here))
       /\ WF_Vars(DecreaseParallelism(here))  
       /\ WF_Vars(CreateRemoteFinish(here)) 
       /\ WF_Vars(RecvAsync(here)) 
       /\ WF_Vars(RecvAsyncTerm(here))
       /\ WF_Vars(NotifyPlaceDeath(here))      \* resilient finish
       /\ WF_Vars(SubmitPendingActivity(here)) \* resilient finish
       /\ WF_Vars(ReleaseRootFinish(here))     \* resilient finish
       /\ \A tid \in ThreadID :
          /\ WF_Vars(IThreadFetchActivity(here, tid))
          /\ WF_Vars(RThreadRunExpr(here, tid))
          /\ WF_Vars(RThreadRunKill(here, tid))
          /\ WF_Vars(RThreadRunAsyncEnd(here, tid))
          /\ WF_Vars(RThreadRunFinishEnd(here, tid))
          /\ WF_Vars(BThreadUnblockFinish(here, tid)) 
          /\ WF_Vars(RThreadRunFinishFirstStmt(here, tid)) 
          /\ WF_Vars(RThreadRunNestedLocalAsync(here, tid))
          /\ WF_Vars(RThreadRunNestedRemoteAsync(here, tid)) 
          /\ WF_Vars(RThreadRunNestedFinish(here, tid)) 
          /\ WF_Vars(RThreadRunNestedExprORKill(here, tid))
          /\ WF_Vars(RThreadRunNestedError(here, tid))     
          /\ WF_Vars(BThreadUnblockResilientAsync(here, tid)) \* resilient finish  
    /\ \A fid \in IDRange :
          WF_Vars(NotifyParentFinish(fid) )    
-------------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)          
Spec ==  Init /\ [][Next]_Vars /\ Liveness

THEOREM Spec => []( TypeOK /\ StateOK )

(****  Example programs
PROG1:
0  finish {
1    async { 
2       expr; 
     }
3    async at (p1) { 
4       expr; 
     }
}

NBLOCKS = 5
MXFINISHES=2
PLACE    = {p0,p1}
<<
[b |-> 0, type |-> "finish", dst |-> p0, body |-> <<1,2>> ],
[b |-> 1, type |-> "async" , dst |-> p0, body |-> <<3>>],
[b |-> 2, type |-> "async" , dst |-> p1, body |-> <<4>>],
[b |-> 3, type |-> "expr" , dst |-> p0, body |-> <<>>],
[b |-> 4, type |-> "expr" , dst |-> p1, body |-> <<>>]
>>


PROG2:  
0 finish {
1    async at (p1) {
2       finish {
3          async at (p2) {
4             expr;
           }
5          kill;
        }
     }
  }
NBLOCKS = 6
MXFINISHES=4
MUST_NOT_RUN={}
PLACE    = {p0,p1,p2}
<<
[b |-> 0, type |-> "finish" , dst |-> p0, body |-> <<1>> ],
[b |-> 1, type |-> "async"  , dst |-> p1, body |-> <<2>> ],
[b |-> 2, type |-> "finish" , dst |-> p1, body |-> <<3,5>> ],
[b |-> 3, type |-> "async"  , dst |-> p2, body |-> <<4>> ],
[b |-> 4, type |-> "expr"   , dst |-> p2, body |-> <<>>  ],
[b |-> 5, type |-> "kill"   , dst |-> p1, body |-> <<>>  ]
>>

***)
=============================================================================
\* Modification History
\* Last modified Mon Nov 06 19:04:04 AEDT 2017 by u5482878
\* Last modified Mon Nov 06 01:23:47 AEDT 2017 by shamouda
\* Created Wed Sep 13 12:14:43 AEST 2017 by u5482878
