----------------------------- MODULE SPMDRoot -----------------------------
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

NotifySubActivitySpawn(dst) == 
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]

NotifySubActivitySpawnError(dst) == FALSE

NotifyActivityCreation(src, activity) == 
    /\ fstates' = fstates  \* always true in SPMD finish

NotifyActivitySpawnAndCreation (dst, src, activity) == 
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]

LastActivity ==
   /\ fstates[fid].count = 1

NotifyActivityTermination == 
    /\ fstates[fid].count > 0
    /\ IF LastActivity = TRUE
       THEN fstates' = [fstates EXCEPT ![fid].count = @-1,
                                       ![fid].status = "finished"] 
       ELSE fstates' = [fstates EXCEPT ![fid].count = @-1]

\* same as NotifyActivityTermination but saves the exceptions too
NotifyActivityTerminationExcs(excs) == 
    /\ fstates[fid].count > 0
    /\ IF LastActivity = TRUE
       THEN fstates' = [fstates EXCEPT ![fid].count = @-1,
                                       ![fid].status = "finished",
                                       ![fid].excs = @ \o excs] 
       ELSE fstates' = [fstates EXCEPT ![fid].count = @-1,
                                       ![fid].excs = @ \o excs]
            
PushException(e) == 
    /\ fstates' = [fstates EXCEPT ![fid].excs = Append(@, e)]

SendTermMsg(mid) == FALSE  \* root doesn't need this action

ProcessChildTermMsg(msg) ==
    LET here == fstates[fid].here
        src == msg.src
        excs == msg.excs
    IN /\ NotifyActivityTerminationExcs(excs)
       /\ RecvMsg (msg)

=============================================================================
\* Modification History
\* Last modified Thu Oct 12 20:18:03 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:16:33 AEST 2017 by u5482878
