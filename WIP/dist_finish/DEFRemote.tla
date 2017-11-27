----------------------------- MODULE DEFRemote -----------------------------
(***************************************************************************)
(* The default root finish imeplementation                                 *)
(* See FinishState.RemoteFinish for the actual implementation              *)
(***************************************************************************)
EXTENDS Sequences, Integers
VARIABLES fid, fstates, msgs, thrds, mseq, p0adoptSet, waitForMsgs
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS, BACKUP
INSTANCE Commons
----------------------------------------------------------------------------
Alloc(type, here, parent, root) == \* parent not used here
   /\ fstates[fid].status \in { "unused", "forgotten" }
   /\ fstates' = [fstates EXCEPT ![fid].id = fid,
                                 ![fid].count = 0, 
                                 ![fid].status = "waiting",
                                 ![fid].type = type,
                                 ![fid].here = here,
                                 ![fid].root = root]

LastActivity ==
   /\ fstates[fid].count = 1
     
NotifySubActivitySpawn(dst) == 
    /\ fstates' = [fstates EXCEPT ![fid].remActs[dst] = @+1]

NotifySubActivitySpawnError(dst) == FALSE
    
NotifyRemoteActivityCreation(src, activity, inMsg) == 
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]
    /\ RecvMsg (inMsg) 

NotifyLocalActivitySpawnAndCreation (here, activity) ==
    /\ IF fstates[fid].here = here
       THEN fstates' = [fstates EXCEPT ![fid].count = @+1,
                                       ![fid].remActs[here] = @+1 ] 
       ELSE fstates' = fstates


PushException(e) == 
    /\ fstates' = [fstates EXCEPT ![fid].excs = Append(@, e)]

NotifyActivityTermination ==
    /\ fstates[fid].count > 0 
    /\ LET here == fstates[fid].here
           pid == fstates[fid].root
           pidHome == GetFinishHome(pid) 
       IN  IF LastActivity 
           THEN  /\ fstates' = [fstates EXCEPT ![fid].count = @-1,
                                               ![fid].remActs[here] = @-1,
                                               ![fid].status = "forgotten"]
                 /\ SendMsg ([ mid |-> mseq, 
                               src |-> here, 
                               dst |-> pidHome, 
                              type |-> "asyncTerm", 
                               fid |-> pid, 
                           remActs |-> [ p \in PLACE |-> IF p = here 
                                                         THEN fstates[fid].remActs[here] -1
                                                         ELSE fstates[fid].remActs[p] ],
                              excs |-> fstates[fid].excs])
                 /\ mseq' = mseq + 1
                 /\ waitForMsgs' = waitForMsgs
           ELSE  /\ fstates' = [fstates EXCEPT ![fid].count = @-1,
                                            ![fid].remActs[here] = @-1 ]
                 /\ msgs' = msgs
                 /\ mseq' = mseq
                 /\ waitForMsgs' = waitForMsgs 

ProcessChildTermMsg(msg) == FALSE  \* remote does't need this action

=============================================================================
\* Modification History
\* Last modified Sun Nov 12 08:24:30 AEDT 2017 by shamouda
\* Last modified Fri Nov 10 17:44:22 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:17:03 AEST 2017 by u5482878
