------------------------------ MODULE ExecutorDistFinish ------------------------------
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
    MXDEAD,        (* Maximum number of places to kill                     *)
    BACKUP        

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
    isDead         (* the dead places recognized at each place             *)

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

-----------------------------------------------------------------------------
(***************************************************************************)
(* Variables for distributed finish PPoPP14                                *)
(***************************************************************************)
VARIABLES
    fmasters,      (* Master finish states                                 *)   
    fbackups,      (* Backup finish states                                 *)
    waitForMsgs    (* Messages that threads are blocking and waiting to     
                      receive, if the sender dies, we send them with a 
                      failed status to unblock these threads               *)

Vars == << fstates, msgs, pstate, program, aseq, fseq, mseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fmasters, fbackups, waitForMsgs >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Predicate to hide the finish implementation                             *)
(***************************************************************************)
Finish(fid) == INSTANCE AbstractFinish

CentrStore == INSTANCE P0ResStore

BackupStore == INSTANCE DistFinishBackup

MasterStore == INSTANCE DistFinishMaster

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
    /\ readyQ \in [ PLACE -> Seq( C!Activity) ]
    /\ thrds \in  [ PLACE -> [  C!ThreadID ->  C!Thread ] ]
    /\ msgs \subseteq  C!Messages   
    /\ pstate \in { "init", "running", "terminated","exceptionThrown" }
    /\ program \in [  C!BlockID ->  C!Block ]
    /\ PROG_HOME \in PLACE
    /\ aseq \in Nat
    /\ mseq \in Nat
    /\ fseq \in  C!IDRange
    /\ ppcurStmt \in Nat
    /\ incPar \in [ PLACE -> Nat ]
    /\ decPar \in [ PLACE -> Nat ]
    /\ MUST_NOT_RUN \subseteq  C!BlockID
    /\ MXDEAD \in Nat
    /\ IF ROOT_FINISH \in {"SPMDroot", "SPMDremote", "root", "remote"} 
       THEN MXDEAD = 0 ELSE TRUE \* don't kill places in non-resilient mode 
    /\ killed \subseteq PLACE
    /\ killedCnt \in Nat
    /\ p0fstates \in [ C!IDRange ->  C!ResilientFinishState] 
    /\ pendingAct \subseteq  C!Activity
    /\ isDead \in [ PLACE -> [ PLACE -> BOOLEAN ] ]
    /\ p0dead \in PLACE \cup { C!NotPlace}
    /\ p0adoptSet  \subseteq  C!Adopter
    /\ p0convSet \subseteq  C!ConvTask
    /\ p0state \in {"running", "seekAdoption", "convertDead", "release"}
    /\ fmasters \in [ C!IDRange -> C!MasterFinish ]
    /\ fbackups \in [ C!IDRange -> C!BackupFinish ]
    /\ BACKUP \in [ PLACE -> PLACE ]
  
StateOK ==
    \/  /\ pstate \in { "init", "running" }
    \/  /\ pstate \in { "terminated", "exceptionThrown" }
        /\ ppProgram = <<>>
        /\ (msgs = {} \/ \A m \in msgs : m.src \in killed)
        /\ \A p \in PLACE : 
            /\ readyQ[p] = <<>>
            /\ \A t \in  C!ThreadID : thrds[p][t].stack = <<>>
        /\ \A fid \in  C!IDRange : 
            /\ fstates[fid].status \in {"unused", "forgotten"}
        /\ IF pstate = "terminated" \/ killed = {}
           THEN /\ fstates[ C!FIRST_ID].excs = <<>>  
                /\ \A b \in  C!BlockID : program[b].ran = TRUE \/ program[b].b = C!NotBlockID
           ELSE \*/\ fstates[FIRST_ID].excs # <<>>  
                /\ \A b \in  C!BlockID : IF b \in MUST_NOT_RUN 
                                      THEN program[b].ran = FALSE 
                                      ELSE program[b].ran = TRUE  

StateOKOK ==
    \/  /\ pstate = "init"
        /\ \A p \in PLACE : 
            /\ readyQ[p] = <<>>
            /\ \A t \in  C!ThreadID : thrds[p][t].stack = <<>>
        /\ \A fid \in  C!IDRange : fstates[fid].status = "unused"
    \/  /\ pstate \in { "terminated", "exceptionThrown" }
        /\ ppProgram = <<>>
        /\ msgs = {}
        /\ \A p \in PLACE : 
            /\ readyQ[p] = <<>>
            /\ \A t \in  C!ThreadID : thrds[p][t].stack = <<>>
        /\ \A fid \in  C!IDRange : 
            /\ fstates[fid].status \in {"unused", "forgotten"}
        /\ IF pstate = "terminated" 
           THEN /\ fstates[C!FIRST_ID].excs = <<>>  
                /\ \A b \in  C!BlockID : program[b].ran = TRUE 
           ELSE /\ fstates[C!FIRST_ID].excs # <<>>  
                /\ \A b \in  C!BlockID : IF b \in MUST_NOT_RUN 
                                      THEN program[b].ran = FALSE 
                                      ELSE program[b].ran = TRUE  
    \/  /\ pstate = "running"
        /\ ppProgram = <<>>
        /\ \/ \E p \in PLACE : 
               \/ readyQ[p] # <<>>
               \/ \E t \in C!ThreadID :  thrds[p][t].stack # <<>>
           \/ fstates[C!FIRST_ID].status # "forgotten"
           
MustTerminate ==
   <> ( pstate \in { "terminated", "exceptionThrown"} )

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init == 
    /\ fstates = [ r \in  C!IDRange |-> 
                   [ id |->  C!NotID, status |-> "unused", type |->  C!NotType, 
                     count |-> 0, excs |-> <<>>, here |->  C!NotPlace, 
                     parent |->  C!NotID, root |->  C!NotID, isGlobal |-> FALSE,
                     remActs |-> [ p \in PLACE |-> 0 ], eroot |-> C!NotID ]]
    /\ readyQ  = [ p \in PLACE |-> <<>> ] 
    /\ msgs    = {}
    /\ pstate  = "init"
    /\ program = [ b \in  C!BlockID |-> 
                   [ b |->  C!NotBlockID, type  |-> "NA", dst |->  C!NotPlace, 
                      mxstmt |-> 0, stmts |-> [ s \in  C!StmtID |->  C!NotBlockID],
                      ran |-> FALSE ]]
    /\ aseq    = 1
    /\ fseq    =  C!FIRST_ID
    /\ mseq    = 0
    /\ ppProgram  = PROG
    /\ ppcurStmt  = 0
    /\ incPar     = [ p \in PLACE |-> 0 ] 
    /\ decPar     = [ p \in PLACE |-> 0 ] 
    /\ thrds      = [ p \in PLACE |-> 
                      [ t \in  C!ThreadID |-> 
                        IF t < NTHREADS 
                        THEN [tid |-> t, status |-> "idle", stack |-> <<>> ]
                        ELSE [tid |-> t, status |-> "NA", stack |-> <<>> ]]]
    /\ killed = {}
    /\ killedCnt = 0
    /\ pendingAct = {}
    /\ isDead = [ p \in PLACE |-> [ z \in PLACE |-> FALSE ]  ]
    /\ p0fstates = [ r \in  C!IDRange |-> [   id |-> C!NotID,
                                       parent |-> C!NotID,
                                      gfsRoot |-> C!NotID,
                                 gfsRootPlace |-> C!NotPlace,
                                    numActive |-> 0,
                                         live |-> [ p \in PLACE |-> 0 ],
                                      transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                                  liveAdopted |-> [ p \in PLACE |-> 0 ],
                               transitAdopted |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                                         excs |-> <<>>,
                                    adopterId |-> C!NotID,
                                    isReleased|-> FALSE
                                       ]
                   ] 
    /\ p0dead = C!NotPlace
    /\ p0adoptSet = {}
    /\ p0convSet = {}
    /\ p0state = "running"
    /\ fmasters = [ r \in  C!IDRange  |-> [ id |-> C!NotID,
                                     numActive |-> 0,
                                          live |-> [ p \in PLACE |-> 0 ],
                                       transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                                   liveAdopted |-> [ p \in PLACE |-> 0 ],
                                transitAdopted |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                                          excs |-> <<>>,
                                      children |-> <<>>,
                                       numDead |-> 0,
                                       backupPlace |-> C!NotPlace   
                                          ] 
                  ]
    /\ fbackups = [ r \in  C!IDRange  |-> [  id |-> C!NotID,
                                           live |-> [ p \in PLACE |-> 0 ],
                                        transit |-> [ p \in PLACE |-> [ q \in PLACE |-> 0 ] ],
                                       children |-> <<>>,
                                      isAdopted |-> FALSE,
                                    adoptedRoot |-> C!NotID   
                                          ] 
                  ] 
    /\ waitForMsgs = {}

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
           h == IF body = <<>> THEN C!EMPTY_BLOCK ELSE Head(body) 
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
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

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
                                                 fid |-> C!NoParent ]
                                              >>,
                                  ![PROG_HOME][0].status = "running" ]
    /\ program' = [program EXCEPT ![0].ran = TRUE] 
    /\ UNCHANGED <<fstates, msgs, aseq, fseq, mseq, readyQ, ppProgram, 
                   ppcurStmt, incPar, decPar,p0dead,p0adoptSet, p0state, p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

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
    IN IF aset = {} THEN C!NotActivity
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
            /\ waitForMsgs' = waitForMsgs

\* Push a local activity
SubmitLocalActivity(here, act) ==     
    /\ IF act.fid # C!NoParent 
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
   /\ LET tid == C!FindThread(here, "NA")
      IN /\ tid # C!NotThreadID
         /\ incPar' = [incPar EXCEPT ![here] = @-1]
         /\ thrds' = [thrds EXCEPT ![here][tid].status = "idle"]
   /\ UNCHANGED <<fstates, msgs, pstate, program, aseq, fseq, mseq, readyQ, 
                  ppProgram, ppcurStmt, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                  killed, killedCnt, p0fstates, pendingAct, isDead,
                  fmasters, fbackups, waitForMsgs>>
           
\* Decrease the number of worker threads
DecreaseParallelism(here) ==
   /\ here \notin killed
   /\ pstate = "running" 
   /\ decPar[here] > 0
   /\ LET tid == C!FindThread(here, "idle")
      IN /\ tid # C!NotThreadID
         /\ decPar' = [decPar EXCEPT ![here] = @-1]
         /\ thrds' = [thrds EXCEPT ![here][tid].status = "NA"]
   /\ UNCHANGED <<fstates, msgs, pstate, program, aseq, fseq, mseq, readyQ, 
                  ppProgram, ppcurStmt, incPar, p0dead,p0adoptSet, p0state, p0convSet,
                  killed, killedCnt, p0fstates, pendingAct, isDead,
                  fmasters, fbackups, waitForMsgs>>

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
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

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
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

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
           p0fstates, pendingAct, isDead,p0adoptSet,p0state,
           fmasters, fbackups, waitForMsgs>>

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
    /\ UNCHANGED <<pstate, program, aseq, fseq, readyQ, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups>>

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
    /\ UNCHANGED << pstate, program, aseq, fseq, readyQ, ppProgram, 
                   ppcurStmt, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups>>

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
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

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
           /\ fseq' = fseq + 1
           /\ IF ROOT_FINISH = "distroot"
              THEN /\ thrds' = [thrds EXCEPT ![here][tid].status = "blockedAlloc",
                                             ![here][tid].stack = << [ b |-> top.b, 
                                                                       i |-> lstStmt, 
                                                                     fid |-> fseq ]
                                                                  >> \o tail    ]
                   /\ incPar' = [incPar EXCEPT ![here] = @ + 1 ]
              ELSE /\ thrds' = [thrds EXCEPT ![here][tid].stack = << [ b |-> top.b, 
                                                                    i |-> curStmt, 
                                                                  fid |-> fseq ]
                                                               >> \o tail ]
                   /\ incPar' = incPar
                   /\ msgs' = msgs
                   /\ mseq' = mseq
                   /\ waitForMsgs' = waitForMsgs
    /\ UNCHANGED << pstate, program, aseq, readyQ, ppProgram, 
                    ppcurStmt, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                    killed, killedCnt, p0fstates, pendingAct, isDead,
                    fmasters, fbackups>>
                    
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
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

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
               /\ fid # C!NoParent
               /\ curStmt >= 0  
               /\ curStmt <= program[blk].mxstmt
               /\ program[nested].type = "async"
               /\ program[nested].dst # here
               /\ IF    Finish(fid)!IsResilient
                  THEN  /\ Finish(fid)!NotifySubActivitySpawn(program[nested].dst)
                        /\ thrds' = [thrds EXCEPT ![here][tid].status = "blockedAsync"]
                        /\ incPar' = [incPar EXCEPT ![here] = @+1]
                  ELSE  \/  /\ Finish(fid)!NotifySubActivitySpawn(program[nested].dst)
                            /\ C!SendMsg ([ mid |-> mseq, 
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
                            /\ waitForMsgs' = waitForMsgs
                        \/  /\ Finish(fid)!NotifySubActivitySpawnError(program[nested].dst) 
                            /\ msgs' = msgs
                            /\ mseq' = mseq
                            /\ thrds' = [thrds EXCEPT ![here][tid].stack = 
                                                             <<[ b |-> top.b, 
                                                                 i |-> program[blk].mxstmt, 
                                                               fid |-> fid ]
                                                             >> \o tail ]
                            /\ incPar' = incPar
                            /\ waitForMsgs' = waitForMsgs
        /\ UNCHANGED <<pstate, program, aseq, fseq, readyQ, ppProgram, 
                       ppcurStmt, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                       killed, killedCnt, p0fstates, pendingAct, isDead,
                       fmasters, fbackups>>

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
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

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
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

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
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

\* Parsing an incoming async and creating its RemoteFinish object
CreateRemoteFinish(here) == 
    /\ here \notin killed
    /\ pstate = "running" 
    /\ LET msg == C!FindIncomingMSG(here, "async")
           pid == msg.fid
           fid == C!GetActiveFID(REMOTE_FINISH, here, pid)
       IN /\ pid # C!NotID
          /\ fid = C!NotID
          /\ Finish(fseq)!Alloc(REMOTE_FINISH, here, pid, pid)
          /\ fseq' = fseq + 1
    /\ UNCHANGED <<msgs, pstate, program, aseq, mseq, readyQ, thrds, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

\* Pushing an incoming async to the ready queue
RecvAsync (here) == 
    /\ here \notin killed
    /\ pstate = "running"
    /\ LET msg == C!FindIncomingMSG(here, "async")
           pid == msg.fid
           fid == C!GetActiveFID(REMOTE_FINISH, here, pid)
           src == msg.src
           blk == msg.b
       IN /\ pid # C!NotID
          /\ fid # C!NotID
          /\ src # C!NotPlace
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
                   incPar, decPar, killed, killedCnt, p0fstates, isDead,
                   fmasters, fbackups>>

\* Enclosing finish receiving a termination signal from a remote task 
RecvAsyncTerm(here) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ LET msg == C!FindIncomingMSG(here, "asyncTerm")
           fid == msg.fid
           src == msg.src
       IN  /\ fid # C!NotID
           /\ src # C!NotPlace
           /\ Finish(fid)!ProcessChildTermMsg(msg)
    /\ UNCHANGED <<pstate, program, aseq, fseq, mseq, readyQ, thrds, ppProgram, 
                   ppcurStmt, incPar, decPar, p0dead,p0adoptSet, p0state,p0convSet,
                   killed, killedCnt, p0fstates, pendingAct, isDead,
                   fmasters, fbackups, waitForMsgs>>

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
           p0fstates, pendingAct, isDead, p0dead,
           fmasters, fbackups, waitForMsgs>>

\* When a place detects that another place has died for the first time
NotifyPlaceDeath(here) == 
    /\ here \notin killed
    /\ pstate = "running"
    /\ LET allNewDead == { p \in killed : ~ isDead[here][p] }
           oneNewDead == IF allNewDead = {} THEN C!NotPlace ELSE CHOOSE p \in allNewDead : TRUE
       IN  /\ oneNewDead # C!NotPlace
           /\ isDead[here][oneNewDead] = FALSE
           /\ isDead' = [isDead EXCEPT ![here][oneNewDead] = TRUE]
           /\ IF here = PROG_HOME
              THEN CentrStore!P0NotifyPlaceDeath(oneNewDead)
              ELSE p0dead' = p0dead /\ p0adoptSet' = p0adoptSet /\ p0state' = p0state
    /\ UNCHANGED <<fstates, msgs, pstate, program, aseq, fseq, mseq, 
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar, p0convSet,
           killed, killedCnt, p0fstates, pendingAct,
           fmasters, fbackups, waitForMsgs>>

--------------------------------------------------------------------------------
(**Unblocking blocked thread when the waited-for message arrives ***)
\* resilient store has changed the transit counters
BThreadUnblockResilientAsync(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "blockedAsync"
    /\ msgs # {}
    /\ LET msg == C!FindIncomingMSG(here, "transitDone")
           top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           root == GetRootFinishId(fid)
           nested == program[blk].stmts[curStmt]
       IN  /\ msg # C!NotMessage
           /\ decPar' = [decPar EXCEPT ![here] = @+1]
           /\ msg.src = PROG_HOME
           /\ C!ReplaceMsg ( msg ,  
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
           killed, killedCnt, p0fstates, pendingAct, isDead,
           fmasters, fbackups, waitForMsgs>>

BThreadUnblockResilientAlloc(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "blockedAlloc"
    /\ msgs # {}
    /\ LET msg == C!FindIncomingMSG(here, "addChildDone")
           success == msg.success
           top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           root == GetRootFinishId(fid)
           nested == program[blk].stmts[curStmt]
       IN  /\ msg # C!NotMessage
           /\ waitForMsgs' = waitForMsgs \ {[ src |-> msg.src, 
                                              dst |-> here,  
                                              fid |-> fid, 
                                            eroot |-> msg.eroot ,
                                             type |-> "addChildDone"  ]}
           /\ IF success 
              THEN /\ decPar' = [decPar EXCEPT ![here] = @+1]
                   /\ C!RecvMsg ( msg )
                   /\ mseq' = mseq
                   /\ thrds' = [thrds EXCEPT  ![here][tid].status = "running",
                                              ![here][tid].stack = 
                                                           <<[  b |-> top.b, 
                                                                i |-> curStmt, 
                                                              fid |-> fid ]
                                                           >> \o tail ]
             ELSE  /\ decPar' = decPar   \* I don't except the backup to fail
                   /\ mseq' = mseq + 1   \* so I don't extend waitForMsgs
                   /\ thrds' = thrds
                   /\ C!ReplaceMsg ( msg ,  
                                     [   mid |-> mseq, 
                                         src |-> here, 
                                         dst |-> fmasters[msg.eroot].backupPlace,
                                       eroot |-> msg.eroot,
                                         fid |-> fid,
                                        type |-> "backupAddChild" ])
    /\ UNCHANGED << fstates, pstate, program, aseq, fseq,
           readyQ, ppProgram, ppcurStmt, incPar,p0dead,p0adoptSet, p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,
           fmasters, fbackups>>


BThreadUnblockResilientAsyncMaster(here, tid) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ thrds[here][tid].status = "blockedAsync"
    /\ msgs # {}
    /\ LET msg == C!FindIncomingMSG(here, "masterTransitDone")
           success == msg.success
           top == Head(thrds[here][tid].stack)
           tail == Tail(thrds[here][tid].stack)
           lstStmt == top.i
           curStmt == top.i + 1
           blk == top.b
           fid == top.fid
           root == GetRootFinishId(fid)
           nested == program[blk].stmts[curStmt]
       IN  /\ msg # C!NotMessage
           /\ IF success 
              THEN /\ decPar' = [decPar EXCEPT ![here] = @+1]
                   /\ msg.src = C!GetFinishHome(fstates[fid].root)
                   /\ C!ReplaceMsg ( msg ,  
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
             ELSE  /\ decPar' =  decPar   \* I don't except the backup to fail
                   /\ mseq' = mseq + 1    \* so I don't extend waitForMsgs
                   /\ thrds' = thrds
                   /\ C!ReplaceMsg ( msg , 
                                  [   mid |-> mseq, 
                                      src |-> here, 
                                      dst |-> C!GetBackup(C!GetFinishHome(fstates[fid].root)),
                                   source |-> here,
                                   target |-> msg.target,
                                      fid |-> fid,
                                     type |-> "backupTransit" ]
                                 )
    /\ UNCHANGED << fstates, pstate, program, aseq, fseq,
           readyQ, ppProgram, ppcurStmt, incPar,p0dead,p0adoptSet, p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,
           fmasters, fbackups, waitForMsgs>>

SubmitPendingActivityMaster(here) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ pendingAct # {}
    /\ msgs # {}
    /\ LET msg == C!FindIncomingMSG(here, "masterLiveDone")
           actId == msg.aid
           activity == FindPendingActivity(actId)
           fid == msg.fid
           submit == msg.submit
           success == msg.success
       IN  /\ msg # C!NotMessage
           /\ activity # C!NotActivity
           /\ fstates[activity.fid].here = here
           /\ IF success 
              THEN  /\ C!RecvMsg ( msg )
                    /\ IF submit 
                      THEN PushReadyFIFO(here, activity) 
                      ELSE readyQ' = readyQ
                    /\ pendingAct' = pendingAct \ {activity}
               ELSE /\ pendingAct' = pendingAct
                    /\ readyQ' = readyQ
                    /\ C!ReplaceMsg ( msg , [   mid |-> mseq, 
                                                  src |-> here, 
                                                  dst |-> C!GetBackup(C!GetFinishHome(fstates[fid].root)),
                                               source |-> msg.source,
                                               target |-> msg.target,
                                                  fid |-> msg.fid,
                                                  aid |-> actId,
                                                 type |-> "backupLive" ]
                                             )
    /\ UNCHANGED << fstates, pstate, program, aseq, fseq, mseq, 
           thrds, ppProgram, ppcurStmt, incPar, decPar,p0dead,p0adoptSet, p0state,p0convSet,
           killed, killedCnt, p0fstates, isDead,
           fmasters, fbackups, waitForMsgs>>

RecvMasterCompletedDone(here) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ msgs # {}
    /\ LET msg == C!FindIncomingMSG(here, "masterCompletedDone")
           fid == msg.fid
           success == msg.success
       IN  /\ msg # C!NotMessage
           /\ IF success 
              THEN /\ C!RecvMsg ( msg )
              ELSE /\ C!ReplaceMsg ( msg , 
                                  [ mid |-> mseq,
                                    src |-> here, 
                                    dst |-> C!GetBackup(C!GetFinishHome(fstates[fid].root)),
                                 target |-> msg.target, 
                                    fid |-> fid, \* always refer to the root state
                                   type |-> "backupCompleted" ]
                                 )
    /\ UNCHANGED << fstates, pstate, program, aseq, fseq, mseq, 
           thrds, ppProgram, ppcurStmt, incPar, decPar,p0dead,p0adoptSet, p0state,p0convSet,
           killed, killedCnt, p0fstates, isDead,
           fmasters, fbackups, waitForMsgs, readyQ, pendingAct>>

--------------------------------------------------------------------------------
\* resilient store has given permission to execute a remote activity
SubmitPendingActivity(here) ==
    /\ here \notin killed
    /\ pstate = "running"
    /\ pendingAct # {}
    /\ msgs # {}
    /\ LET msg == C!FindIncomingMSG(here, "liveDone")
           actId == msg.aid
           activity == FindPendingActivity(actId)
           submit == msg.submit
       IN  /\ msg # C!NotMessage
           /\ activity # C!NotActivity
           /\ C!RecvMsg ( [   mid |-> msg.mid,
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
           killed, killedCnt, p0fstates, isDead,
           fmasters, fbackups, waitForMsgs>>

ReleaseRootFinish(here) == 
    /\ here \notin killed
    /\ pstate = "running"
    /\ msgs # {}
    /\ LET msg == C!FindIncomingMSG(here, "releaseFinish")
           fid == msg.fid           
       IN  /\ msg # C!NotMessage
           /\ C!RecvMsg ( msg )
           /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"]
           /\ IF fid = C!FIRST_ID
              THEN TRUE
              ELSE waitForMsgs' = waitForMsgs
    /\ UNCHANGED << pstate, program, aseq, fseq, mseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0adoptSet, p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,
           fmasters, fbackups>>

-------------------------------------------------------------------------------
(***************************************************************************)
(* Predicate enumerating all possible next actions                         *)
(***************************************************************************)    

NextCentrStore == 
    \/ CentrStore!RecvTransit(PROG_HOME)      \* resilient finish
    \/ CentrStore!RecvLive(PROG_HOME)         \* resilient finish
    \/ CentrStore!RecvCompleted(PROG_HOME)    \* resilient finish
    \/ CentrStore!SeekAdoption(PROG_HOME)     \* resilient finish
    \/ CentrStore!ConvertDeadActivities(PROG_HOME) \* resilient finish
    \/ CentrStore!ReleaseAll(PROG_HOME)

NextDistStore(here) ==
    \/ BackupStore!BackupRecvAddChild(here)
    \/ BackupStore!BackupRecvTransit(here)
    \/ BackupStore!BackupRecvLive(here) 
    \/ BackupStore!BackupRecvCompleted(here)
    \/ MasterStore!RecvAddChild(here)
    \/ MasterStore!RecvBackupAddChildDone(here)                    
    \/ MasterStore!RecvMasterTransit(here) 
    \/ MasterStore!RecvBackupTransitDone(here)           
    \/ MasterStore!RecvMasterTransitToLive(here)                         
    \/ MasterStore!RecvBackupLiveDone(here) 
    \/ MasterStore!RecvMasterCompleted(here) 
    \/ MasterStore!RecvBackupCompletedDone(here)
    \/ RecvMasterCompletedDone(here)

NextDistStore2(here, tid) ==
    \/ BThreadUnblockResilientAlloc(here, tid)
             
Next ==
    \/ ParseInputProgram 
    \/ Run
    \/ NextCentrStore
    \/ \E here \in PLACE :
        \/ IncreaseParallelism(here)
        \/ DecreaseParallelism(here) 
        \/ CreateRemoteFinish(here)
        \/ RecvAsync (here) 
        \/ RecvAsyncTerm(here)
        \/ NotifyPlaceDeath(here)      \* resilient finish
        \/ SubmitPendingActivity(here) \* resilient finish
        \/ ReleaseRootFinish(here)     \* resilient finish
        \/ NextDistStore(here)
        \/ SubmitPendingActivityMaster(here)
        \/  \E tid \in C!ThreadID :
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
            \/ BThreadUnblockResilientAsyncMaster(here, tid)
            \/ NextDistStore2(here, tid)

-------------------------------------------------------------------------------
(***************************************************************************)
(* Asserting fairness properties to all actions                            *)
(***************************************************************************)

LivenessCentrStore ==
    /\ WF_Vars(CentrStore!RecvTransit(PROG_HOME))       \* resilient finish
    /\ WF_Vars(CentrStore!RecvLive(PROG_HOME))          \* resilient finish
    /\ WF_Vars(CentrStore!RecvCompleted(PROG_HOME))     \* resilient finish
    /\ WF_Vars(CentrStore!SeekAdoption(PROG_HOME))      \* resilient finish
    /\ WF_Vars(CentrStore!ConvertDeadActivities(PROG_HOME)) \* resilient finish
    /\ WF_Vars(CentrStore!ReleaseAll(PROG_HOME))

LivenessDistStore(here) ==
    /\ WF_Vars(BackupStore!BackupRecvAddChild(here))
    /\ WF_Vars(BackupStore!BackupRecvTransit(here))
    /\ WF_Vars(BackupStore!BackupRecvLive(here))
    /\ WF_Vars(BackupStore!BackupRecvCompleted(here))
    /\ WF_Vars(MasterStore!RecvAddChild(here))
    /\ WF_Vars(MasterStore!RecvBackupAddChildDone(here))                    
    /\ WF_Vars(MasterStore!RecvMasterTransit(here)) 
    /\ WF_Vars(MasterStore!RecvBackupTransitDone(here))           
    /\ WF_Vars(MasterStore!RecvMasterTransitToLive(here))                          
    /\ WF_Vars(MasterStore!RecvBackupLiveDone(here)) 
    /\ WF_Vars(MasterStore!RecvMasterCompleted(here)) 
    /\ WF_Vars(MasterStore!RecvBackupCompletedDone(here))
    /\ WF_Vars(RecvMasterCompletedDone(here))
       
Liveness ==
    /\ WF_Vars(ParseInputProgram)
    /\ WF_Vars(Run)
    /\ LivenessCentrStore
    /\ \A here \in PLACE : 
          WF_Vars(IncreaseParallelism(here))
       /\ WF_Vars(DecreaseParallelism(here))  
       /\ WF_Vars(CreateRemoteFinish(here)) 
       /\ WF_Vars(RecvAsync(here)) 
       /\ WF_Vars(RecvAsyncTerm(here))
       /\ WF_Vars(NotifyPlaceDeath(here))      \* resilient finish
       /\ WF_Vars(SubmitPendingActivity(here)) \* resilient finish
       /\ WF_Vars(ReleaseRootFinish(here))     \* resilient finish
       /\ WF_Vars(SubmitPendingActivityMaster(here))
       /\ LivenessDistStore(here)
       /\ \A tid \in C!ThreadID :
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
          /\ WF_Vars(BThreadUnblockResilientAsyncMaster(here, tid))
  
-------------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)          
Spec ==  Init /\ [][Next]_Vars /\ Liveness

THEOREM Spec => []( TypeOK /\ StateOK )

(****
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
======================================================================
PROG2:  Fails with SPMD finish but works fine with Default finish
0  finish {
1    async { 
2      expr; 
     }
3    async at (p1) {
4      async at (p2) {     // not allowed in SPMD finish 
5        expr; 
       }
6      expr;       //must not run in SPMD because of the exception
     }
   }

NBLOCKS = 7
MXFINISHES=3
MUST_NOT_RUN={4,5,6}
PLACE    = {p0,p1,p2}
<<
[b |-> 0, type |-> "finish", dst |-> p0, body |-> <<1,3>> ],
[b |-> 1, type |-> "async" , dst |-> p0, body |-> <<2>>],
[b |-> 2, type |-> "expr"  , dst |-> p0, body |-> <<>> ],
[b |-> 3, type |-> "async" , dst |-> p1, body |-> <<4,6>>],
[b |-> 4, type |-> "async" , dst |-> p2, body |-> <<5>>],
[b |-> 5, type |-> "expr"  , dst |-> p2, body |-> <<>> ],
[b |-> 6, type |-> "expr"  , dst |-> p1, body |-> <<>> ]
>>
======================================================================
PROG3:
0 finish {
1    async at (p1) {
2        async at (p2) {
3            expr;
         }
4        error;
5        async at (p2) {
6            expr;
         }
     }
 }
NBLOCKS = 7
MXFINISHES=4
MUST_NOT_RUN={5,6}
PLACE    = {p0,p1,p2}
<<
[b |-> 0, type |-> "finish" , dst |-> p0, body |-> <<1>> ],
[b |-> 1, type |-> "async"  , dst |-> p1, body |-> <<2,4,5>>],
[b |-> 2, type |-> "async"  , dst |-> p2, body |-> <<3>> ],
[b |-> 3, type |-> "expr"   , dst |-> p2, body |-> <<>>],
[b |-> 4, type |-> "error"  , dst |-> p1, body |-> <<>>],
[b |-> 5, type |-> "async"  , dst |-> p2, body |-> <<6>> ],
[b |-> 6, type |-> "expr"   , dst |-> p2, body |-> <<>> ]
>>
==========================================================================
PROG4:  VERY SLOW
0 finish {
1    async at (p1) {
2        async at (p2) {
3            async at (p3) {
4                expr;
             }
         }        
     }
 }
NBLOCKS = 5
MXFINISHES=4
MUST_NOT_RUN={}
PLACE    = {p0,p1,p2,p3}
<<
[b |-> 0, type |-> "finish" , dst |-> p0, body |-> <<1>> ],
[b |-> 1, type |-> "async"  , dst |-> p1, body |-> <<2>> ],
[b |-> 2, type |-> "async"  , dst |-> p2, body |-> <<3>> ],
[b |-> 3, type |-> "async"  , dst |-> p3, body |-> <<4>> ],
[b |-> 4, type |-> "expr"   , dst |-> p3, body |-> <<>>  ]
>>
=========================================================================
PROG5:  
0 finish {
1    async at (p1) {
2       async at (p2) {
3          kill;
        }        
     }
  }
NBLOCKS = 4
MXFINISHES=3
MUST_NOT_RUN={}
PLACE    = {p0,p1,p2}
<<
[b |-> 0, type |-> "finish" , dst |-> p0, body |-> <<1>> ],
[b |-> 1, type |-> "async"  , dst |-> p1, body |-> <<2>> ],
[b |-> 2, type |-> "async"  , dst |-> p2, body |-> <<3>> ],
[b |-> 3, type |-> "kill"   , dst |-> p2, body |-> <<>>  ]
>>
=========================================================================
PROG6:  
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
===================================================================

<<
[b |-> 0, type |-> "finish" , dst |-> p0, body |-> <<1>> ],
[b |-> 1, type |-> "async"  , dst |-> p1, body |-> <<2>> ],
[b |-> 2, type |-> "finish" , dst |-> p1, body |-> <<3>> ],
[b |-> 3, type |-> "async"  , dst |-> p2, body |-> <<4>> ],
[b |-> 4, type |-> "expr"   , dst |-> p2, body |-> <<>>  ]
>>

[ p \in PLACE |-> IF p = p0
                  THEN p1
                  ELSE IF p = p1
                  THEN p2
                  ELSE p0 ]
***)
=============================================================================
\* Modification History
\* Last modified Sun Nov 12 08:29:34 AEDT 2017 by shamouda
\* Last modified Fri Nov 10 21:05:26 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:14:43 AEST 2017 by u5482878
