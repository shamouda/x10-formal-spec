---------------------------- MODULE SPMDRemote ----------------------------
(***************************************************************************)
(* A Single Program Multi Data remote finish                               *)
(* See FinishState.RemoteFinishSPMD for the actual implementation          *)
(***************************************************************************)
EXTENDS Sequences, Integers
---------------------------------------------------------------------------
VARIABLES fid, fstates, msgs, thrds, mseq,p0adoptSet, waitForMsgs
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS, BACKUP
INSTANCE Commons
---------------------------------------------------------------------------
Alloc(type, here, parent, root) == \* parent not used here
   /\ fstates[fid].status = "unused"
   /\ fstates' = [fstates EXCEPT ![fid].id = fid,
                                 ![fid].count = 1, 
                                 ![fid].status = "waiting",
                                 ![fid].type = type,
                                 ![fid].here = here,
                                 ![fid].root = root]

PushException(e) == 
    /\ fstates' = [fstates EXCEPT ![fid].excs = Append(@, e)]
                              
NotifySubActivitySpawn(dst) == 
    /\ fstates[fid].here = dst
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]

NotifySubActivitySpawnError(dst) == 
    /\ fstates[fid].here # dst
    /\ PushException([ err |-> "SpawnRemoteAsync", 
                       from |-> fstates[fid].here ])

NotifyRemoteActivityCreation(src, activity, inMsg) == 
    /\ fstates' = fstates  \* always true in SPMD finish
    /\ RecvMsg (inMsg)

NotifyLocalActivitySpawnAndCreation (here, activity) == 
    /\ fstates[fid].here = here
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]

LastActivity ==
   /\ fstates[fid].count = 1

NotifyActivityTermination == 
    /\ fstates[fid].count > 0
    /\ IF LastActivity
       THEN /\ fstates' = [fstates EXCEPT ![fid].count = @-1,
                                          ![fid].status = "forgotten"]
            /\ LET pid == fstates[fid].root
                   pidHome == GetFinishHome(pid) 
                   here == fstates[fid].here
               IN  IF pidHome = here
                   THEN  /\ msgs' = msgs
                         /\ mseq' = mseq
                         /\ waitForMsgs' = waitForMsgs 
                   ELSE  /\ SendMsg ([ mid |-> mseq, 
                                       src |-> here, 
                                       dst |-> pidHome , 
                                      type |-> "asyncTerm", 
                                       fid |-> pid, 
                                      excs |-> fstates[fid].excs ])
                         /\ mseq' = mseq + 1
                         /\ waitForMsgs' = waitForMsgs
       ELSE /\ fstates' = [fstates EXCEPT ![fid].count = @-1]
            /\ msgs' = msgs
            /\ mseq' = mseq
            /\ waitForMsgs' = waitForMsgs 

ProcessChildTermMsg(msg) == FALSE  \* remote does't need this action
    
=============================================================================
\* Modification History
\* Last modified Sun Nov 12 08:25:25 AEDT 2017 by shamouda
\* Last modified Fri Nov 10 17:45:11 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:16:19 AEST 2017 by u5482878
