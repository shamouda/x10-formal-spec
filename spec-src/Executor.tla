------------------------------ MODULE Executor ------------------------------
(***************************************************************************)
(* This specification models a subset of X10 programs that use finish,     *) 
(* async at (place), simple expression statements, or error statements that*) 
(* raise exceptions.                                                      *)
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
(* Constants and variables                                                 *)
(***************************************************************************)
CONSTANTS 
    PLACE,         (* The set of places                                    *)
    PROG,          (* The input program as a sequence of async statements  *)
    MXFINISHES,    (* Maximum finish objects including root and remote     *)
    ROOT_FINISH,   (* The selected finish implementation for root          *)
    REMOTE_FINISH, (* The selected finish implementation for remote        *)
    PROG_HOME,
    NTHREADS,      (* Minimum number of threads, more threads can be added *) 
                   (* up to MXTHREADS when running threads blocks          *)
    MXTHREADS, 
    NBLOCKS,
    MXSTMTS,
    MUST_NOT_RUN   (* Validation constant: blocks that must not run, for   *) 
                   (* example were not executed because of an execption    *)
          
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
    ppcurStmt      (* Preprocessing temporary variable: current statement  *)

Vars == << fstates, msgs, pstate, program, aseq, fseq, mseq, 
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Predicate to hide the finish implementation                             *)
(***************************************************************************)
Finish(fid) == INSTANCE AbstractFinish

INSTANCE Commons

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

PartialCorrectness ==
    \/  /\ pstate = "init"
        /\ \A p \in PLACE : 
            /\ readyQ[p] = <<>>
            /\ \A t \in ThreadID : thrds[p][t].stack = <<>>
        /\ \A fid \in IDRange : fstates[fid].status = "unused"
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
                /\ \A b \in BlockID : program[b].ran = 1 
           ELSE /\ fstates[FIRST_ID].excs # <<>>  
                /\ \A b \in BlockID : IF b \in MUST_NOT_RUN 
                                      THEN program[b].ran = 0 
                                      ELSE program[b].ran = 1  
    \/  /\ pstate = "running"
        /\ ppProgram = <<>>
        /\ \/ \E p \in PLACE : 
               \/ readyQ[p] # <<>>
               \/ \E t \in ThreadID :  thrds[p][t].stack # <<>>
           \/ fstates[FIRST_ID].status # "forgotten"

CorrectTermination ==
   <> ( pstate \in { "terminated", "exceptionThrown"} )

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init == 
    /\ fstates = [ r \in IDRange |-> 
                   [ id |-> NotID, status |-> "unused", type |-> NotType, 
                     count |-> 0, excs |-> <<>>, here |-> NotPlace, 
                     root |-> NotID, remActs |-> [ p \in PLACE |-> 0 ]]]
    /\ readyQ  = [ p \in PLACE |-> <<>> ] 
    /\ msgs    = {}
    /\ pstate  = "init"
    /\ program = [ b \in BlockID |-> 
                   [ b |-> NotBlockID, type  |-> "NA", dst |-> NotPlace, 
                      mxstmt |-> 0, stmts |-> [ s \in StmtID |-> NotBlockID],
                      ran |-> 0 ]]
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
                                      ![b].ran = 0,
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
                   thrds, incPar, decPar>>

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
    /\ program' = [program EXCEPT ![0].ran = 1] 
    /\ UNCHANGED <<fstates, msgs, aseq, fseq, mseq, readyQ, ppProgram, 
                   ppcurStmt, incPar, decPar>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Scheduler Actions                                                       *)
(***************************************************************************)
\* Helper action: push activity
PushReadyFIFO(here, activity) ==
    /\ readyQ' = [readyQ EXCEPT![here] = Append (@, activity)]

\* Helper action: poll activity    
PollReadyFIFO(here) ==
    /\ readyQ[here] # <<>>
    /\ readyQ' = [readyQ EXCEPT![here] = Tail (readyQ[here])]


\* Push an activity received from another place
SubmitRemoteActivity(here, src, activity) == 
    /\ IF activity.fid # NoParent    
       THEN Finish(activity.fid)!NotifyActivityCreation(src, activity)
       ELSE fstates' = fstates
    /\ PushReadyFIFO(here, activity)

\* Push a local activity
SubmitLocalActivity(here, activity) ==     
    /\ IF activity.fid # NoParent 
       THEN Finish(activity.fid)!NotifyActivitySpawnAndCreation(here, activity)
       ELSE fstates' = fstates
    /\ PushReadyFIFO(here, activity)

\* Increase the number of worker threads 
IncreaseParallelism(here) ==
   /\ pstate = "running" 
   /\ incPar[here] > 0
   /\ LET tid == FindThread(here, "NA")
      IN /\ tid # NotThreadID
         /\ incPar' = [incPar EXCEPT ![here] = @-1]
         /\ thrds' = [thrds EXCEPT ![here][tid].status = "idle"]
   /\ UNCHANGED <<fstates, msgs, pstate, program, aseq, fseq, mseq, readyQ, 
                  ppProgram, ppcurStmt, decPar>>

\* Decrease the number of worker threads
DecreaseParallelism(here) ==
   /\ pstate = "running" 
   /\ decPar[here] > 0
   /\ LET tid == FindThread(here, "idle")
      IN /\ tid # NotThreadID
         /\ decPar' = [decPar EXCEPT ![here] = @-1]
         /\ thrds' = [thrds EXCEPT ![here][tid].status = "NA"]
   /\ UNCHANGED <<fstates, msgs, pstate, program, aseq, fseq, mseq, readyQ, 
                  ppProgram, ppcurStmt, incPar>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Program Execution Actions                                               *)
(***************************************************************************)
\* Idle thread fetching a ready activity
IThreadFetchActivity(here, tid) ==
    /\ pstate = "running"
    /\ thrds[here][tid].status = "idle"
    /\ PollReadyFIFO(here)
    /\ LET  act == Head(readyQ[here])
            stkEntry == [b |-> act.b, i |-> -1 , fid |-> act.fid]
       IN   /\ thrds' = [thrds EXCEPT ![here][tid].stack = <<stkEntry>>,
                                   ![here][tid].status = "running" ]
            /\ program' = [program EXCEPT ![act.b].ran = 1] 
    /\ UNCHANGED <<fstates, msgs, pstate, aseq, fseq, mseq, ppProgram, 
                   ppcurStmt, incPar, decPar>>

\* Running thread processing an expression
RThreadRunExpr(here, tid) ==
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
                   ppProgram, ppcurStmt, incPar, decPar>>

\* Running thread processing the end of an async block
RThreadRunAsyncEnd(here, tid) ==
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
                   ppcurStmt, incPar, decPar>>

\* Running thread processing the end of a finish block and blocking itself
RThreadRunFinishEnd(here, tid) == 
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
       IN  /\ program[top.b].type = "finish"
           /\ program[top.b].mxstmt = top.i
           /\ Finish(top.fid)!NotifyActivityTermination
           /\ thrds' = [thrds EXCEPT ![here][tid].status = "blocked"]
           /\ incPar' = [incPar EXCEPT ![here] = @+1]   
    /\ UNCHANGED <<msgs, pstate, program, aseq, fseq, mseq, readyQ, ppProgram, 
                   ppcurStmt, decPar>>

\* Terminated finish unblocks its thread
BThreadUnblock(here, tid) ==
    /\ pstate = "running"
    /\ thrds[here][tid].status = "blocked"
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
                   ppProgram, ppcurStmt, incPar>>

\* Running thread processing the beginning of a finish block
RThreadRunFinishFirstStmt(here, tid) ==
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
           /\ Finish(fseq)!Alloc(ROOT_FINISH, here, fid)
           /\ thrds' = [thrds EXCEPT ![here][tid].stack = << [ b |-> top.b, 
                                                               i |-> curStmt, 
                                                             fid |-> fseq ]
                                                          >> \o tail ]
           /\ fseq' = fseq + 1
    /\ UNCHANGED <<msgs, pstate, program, aseq, mseq, readyQ, ppProgram, 
                   ppcurStmt, incPar, decPar>>

\* Processing a nested local async in the currently running block
RThreadRunNestedLocalAsync(here, tid) ==
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           nested == program[blk].stmts[curStmt]
       IN  /\ program[blk].type # "expr"
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
                   ppcurStmt, incPar, decPar>>

\* Processing a nested remote async in the currently running block
RThreadRunNestedRemoteAsync(here, tid) ==
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
       IN  /\ program[blk].type # "expr"
           /\ fid # NoParent
           /\ curStmt >= 0  
           /\ curStmt <= program[blk].mxstmt
           /\ program[nested].type = "async"
           /\ program[nested].dst # here
           /\ \/ /\ Finish(fid)!NotifySubActivitySpawn(program[nested].dst)
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
              \/ /\ Finish(fid)!NotifySubActivitySpawnError(program[nested].dst) 
                 /\ msgs' = msgs
                 /\ mseq' = mseq
                 /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                                 <<[ b |-> top.b, 
                                                     i |-> program[blk].mxstmt, 
                                                   fid |-> fid ]
                                                 >> \o tail ]
    /\ UNCHANGED <<pstate, program, aseq, fseq, readyQ, ppProgram, 
                   ppcurStmt, incPar, decPar>>

\* Processing a nested finish in the currently running block
RThreadRunNestedFinish(here, tid) ==
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           nested == program[blk].stmts[curStmt]
       IN  /\ program[blk].type # "expr"
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
           /\ program' = [program EXCEPT ![nested].ran = 1] 
    /\ UNCHANGED <<fstates, msgs, pstate, aseq, fseq, mseq, readyQ, 
                   ppProgram, ppcurStmt, incPar, decPar>>

\* Processing a nested expression in the currently running block
RThreadRunNestedExpr(here, tid) ==
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           nested == program[blk].stmts[curStmt]
       IN  /\ program[blk].type # "expr"
           /\ curStmt >= 0  
           /\ curStmt <= program[blk].mxstmt
           /\ program[nested].type = "expr"
           /\ program[nested].dst = here
           /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                           << [  b |-> nested, 
                                                 i |-> -1, 
                                               fid |-> fid ],
                                              [  b |-> top.b, 
                                                 i |-> curStmt, 
                                               fid |-> fid ]  
                                           >> \o tail ]
           /\ program' = [program EXCEPT ![nested].ran = 1] 
    /\ UNCHANGED <<fstates, msgs, pstate, aseq, fseq, mseq, readyQ, 
                   ppProgram, ppcurStmt, incPar, decPar>>

\* Processing a nested error in the currently running block
RThreadRunNestedError(here, tid) ==
    /\ pstate = "running"
    /\ thrds[here][tid].status = "running"
    /\ LET top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           nested == program[blk].stmts[curStmt]
       IN  /\ program[blk].type \notin { "expr" , "error" }
           /\ curStmt >= 0  
           /\ curStmt <= program[blk].mxstmt
           /\ program[nested].type = "error"
           /\ program[nested].dst = here
           /\ thrds' = [thrds EXCEPT ![here][tid].stack = \* jump to the end of the current block
                                           << [  b |-> top.b, 
                                                 i |-> program[blk].mxstmt,  
                                               fid |-> fid ]  
                                           >> \o tail ]
           /\ program' = [program EXCEPT ![nested].ran = 1] 
           /\ Finish(fid)!PushException([err |-> "ErrorStmt", from |-> here])
    /\ UNCHANGED <<msgs, pstate, aseq, fseq, mseq, readyQ, 
                   ppProgram, ppcurStmt, incPar, decPar>>

\* Parsing an incoming async and creating its RemoteFinish object
CreateRemoteFinish(here) == 
    /\ pstate = "running" 
    /\ LET msg == FindIncomingMSG(here, "async")
           pid == msg.fid
           fid == GetActiveFID(REMOTE_FINISH, here, pid)
       IN /\ pid # NotID
          /\ fid = NotID
          /\ Finish(fseq)!Alloc(REMOTE_FINISH, here, pid)
          /\ fseq' = fseq + 1
    /\ UNCHANGED <<msgs, pstate, program, aseq, mseq, readyQ, thrds, ppProgram, 
                   ppcurStmt, incPar, decPar>>

\* Pushing an incoming async to the ready queue
RecvAsync (here) == 
    /\ pstate = "running"
    /\ LET msg == FindIncomingMSG(here, "async")
           pid == msg.fid
           fid == GetActiveFID(REMOTE_FINISH, here, pid)
           src == msg.src
           blk == msg.b
       IN /\ pid # NotID
          /\ fid # NotID
          /\ src # NotPlace
          /\ RecvMsg ( [ mid |-> msg.mid, 
                         src |-> msg.src, 
                         dst |-> here, 
                         type |-> "async", 
                         b |-> blk, 
                         fid |-> pid])
          /\ SubmitRemoteActivity(here, src, [aid |-> aseq, 
                                                b |-> blk, 
                                              fid |-> fid ])
          /\ aseq' = aseq + 1
    /\ UNCHANGED <<pstate, program, fseq, mseq, thrds, ppProgram, ppcurStmt, 
                   incPar, decPar>>

\* Enclosing finish receiving a termination signal from a remote task 
RecvAsyncTerm(here) ==
    /\ pstate = "running"
    /\ LET msg == FindIncomingMSG(here, "asyncTerm")
           fid == msg.fid
           src == msg.src
       IN  /\ fid # NotID
           /\ src # NotPlace
           /\ Finish(fid)!ProcessChildTermMsg(msg)
    /\ UNCHANGED <<pstate, program, aseq, fseq, mseq, readyQ, thrds, ppProgram, 
                   ppcurStmt, incPar, decPar>>

\* RemoteFinish notifying its RootFinish that it terminated
NotifyParentFinish(fid) == 
    /\ pstate = "running"
    /\ fstates[fid].status = "finished"
    /\ LET type == fstates[fid].type
           pid == fstates[fid].root
           pidHome == GetFinishHome(pid)
           here == fstates[fid].here
       IN  IF type = ROOT_FINISH 
           THEN /\ msgs' = msgs
                /\ mseq' = mseq
                /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"] 
           ELSE /\ pidHome # here
                /\ Finish(fid)!SendTermMsg(mseq)
                /\ mseq' = mseq + 1
    /\ UNCHANGED <<program, pstate, aseq, fseq, readyQ, thrds, ppProgram, 
                   ppcurStmt, incPar, decPar>>
   
-------------------------------------------------------------------------------
(***************************************************************************)
(* Predicate enumerating all possible next actions                          *)
(***************************************************************************)    
Next ==
    \/ ParseInputProgram 
    \/ Run
    \/ \E here \in PLACE :
        \/ IncreaseParallelism(here)
        \/ DecreaseParallelism(here) 
        \/ CreateRemoteFinish(here)
        \/ RecvAsync (here) 
        \/ RecvAsyncTerm(here) 
        \/  \E tid \in ThreadID :
               \/ IThreadFetchActivity(here, tid)
               \/ RThreadRunExpr(here, tid) 
               \/ RThreadRunAsyncEnd(here, tid) 
               \/ RThreadRunFinishEnd(here, tid)
               \/ BThreadUnblock(here, tid) 
               \/ RThreadRunFinishFirstStmt(here, tid) 
               \/ RThreadRunNestedLocalAsync(here, tid) 
               \/ RThreadRunNestedRemoteAsync(here, tid) 
               \/ RThreadRunNestedFinish(here, tid) 
               \/ RThreadRunNestedExpr(here, tid)
               \/ RThreadRunNestedError(here, tid)     
        \/ \E fid \in IDRange : 
               \/ NotifyParentFinish(fid)


-------------------------------------------------------------------------------
(***************************************************************************)
(* Asserting fairness properties to all actions                            *)
(***************************************************************************)
Liveness ==
    /\ WF_Vars(ParseInputProgram)
    /\ WF_Vars(Run)
    /\ \A here \in PLACE : 
          WF_Vars(IncreaseParallelism(here))
       /\ WF_Vars(DecreaseParallelism(here))  
       /\ WF_Vars(CreateRemoteFinish(here)) 
       /\ WF_Vars(RecvAsync(here)) 
       /\ WF_Vars(RecvAsyncTerm(here))
       /\ \A tid \in ThreadID :
           /\ WF_Vars(IThreadFetchActivity(here, tid))
           /\ WF_Vars(RThreadRunExpr(here, tid))
           /\ WF_Vars(RThreadRunAsyncEnd(here, tid))
           /\ WF_Vars(RThreadRunFinishEnd(here, tid))
           /\ WF_Vars(BThreadUnblock(here, tid)) 
           /\ WF_Vars(RThreadRunFinishFirstStmt(here, tid)) 
           /\ WF_Vars(RThreadRunNestedLocalAsync(here, tid))
           /\ WF_Vars(RThreadRunNestedRemoteAsync(here, tid)) 
           /\ WF_Vars(RThreadRunNestedFinish(here, tid)) 
           /\ WF_Vars(RThreadRunNestedExpr(here, tid))
           /\ WF_Vars(RThreadRunNestedError(here, tid))          
    /\ \A fid \in IDRange :
          WF_Vars(NotifyParentFinish(fid) )    
-------------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)          
Spec ==  Init /\ [][Next]_Vars /\ Liveness

THEOREM Spec => []( TypeOK /\ PartialCorrectness )

=============================================================================
\* Modification History
\* Last modified Fri Oct 13 18:26:27 AEDT 2017 by u5482878
\* Last modified Tue Sep 26 22:57:46 AEST 2017 by shamouda
\* Created Wed Sep 13 12:14:43 AEST 2017 by u5482878
