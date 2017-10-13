---------------------------- MODULE SPMDRemote ----------------------------
EXTENDS Sequences, Integers
---------------------------------------------------------------------------
VARIABLES fid, fstates, msgs, thrds
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS
INSTANCE Commons
---------------------------------------------------------------------------
Alloc(type, here, root) ==
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

NotifyActivityCreation(src, activity) == 
    /\ fstates' = fstates  \* always true in SPMD finish

NotifyActivitySpawnAndCreation (dst, src, activity) == 
    /\ fstates[fid].here = dst
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]

LastActivity ==
   /\ fstates[fid].count = 1

NotifyActivityTermination == 
    /\ fstates[fid].count > 0
    /\ IF LastActivity
       THEN fstates' = [fstates EXCEPT ![fid].count = @-1,
                                       ![fid].status = "finished"]
       ELSE fstates' = [fstates EXCEPT ![fid].count = @-1]
       
SendTermMsg(mid) ==
   LET pid == fstates[fid].root
       pidHome == GetFinishHome(pid) 
       here == fstates[fid].here
   IN  /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"]
       /\ SendMsg ([ mid |-> mid, 
                     src |-> here, 
                     dst |-> pidHome , 
                    type |-> "asyncTerm", 
                     fid |-> pid, 
                     excs |-> fstates[fid].excs ])

ProcessChildTermMsg(msg) == FALSE  \* remote does't need this action
    
=============================================================================
\* Modification History
\* Last modified Thu Oct 12 20:13:26 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:16:19 AEST 2017 by u5482878
