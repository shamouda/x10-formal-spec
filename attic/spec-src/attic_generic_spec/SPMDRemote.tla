---------------------------- MODULE SPMDRemote ----------------------------
(***************************************************************************)
(* A Single Program Multi Data remote finish                               *)
(* See FinishState.RemoteFinishSPMD for the actual implementation          *)
(***************************************************************************)
EXTENDS Sequences, Integers
---------------------------------------------------------------------------
VARIABLES fid, fstates, msgs, thrds, mseq,p0adoptSet
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS
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
       THEN fstates' = [fstates EXCEPT ![fid].count = @-1,
                                       ![fid].status = "finished"]
       ELSE fstates' = [fstates EXCEPT ![fid].count = @-1]
       
SendTermMsg ==
   LET pid == fstates[fid].root
       pidHome == GetFinishHome(pid) 
       here == fstates[fid].here
   IN  /\ pidHome # here
       /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"]
       /\ SendMsg ([ mid |-> mseq, 
                     src |-> here, 
                     dst |-> pidHome , 
                    type |-> "asyncTerm", 
                     fid |-> pid, 
                     excs |-> fstates[fid].excs ])
       /\ mseq' = mseq + 1

ProcessChildTermMsg(msg) == FALSE  \* remote does't need this action
    
=============================================================================
\* Modification History
\* Last modified Mon Nov 06 19:13:53 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:16:19 AEST 2017 by u5482878
