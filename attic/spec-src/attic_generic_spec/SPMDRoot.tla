----------------------------- MODULE SPMDRoot -----------------------------
(***************************************************************************)
(* A Single Program Multi Data root finish                                 *)
(* See FinishState.RootFinishSPMD for the actual implementation            *)
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

NotifySubActivitySpawn(dst) == 
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]

NotifySubActivitySpawnError(dst) == FALSE

NotifyRemoteActivityCreation(src, activity, inMsg) == 
    /\ fstates' = fstates  \* always true in SPMD finish
    /\ RecvMsg (inMsg)

NotifyLocalActivitySpawnAndCreation (here, activity) == 
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

SendTermMsg ==
    /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"]
    /\ msgs' = msgs
    /\ mseq' = mseq

ProcessChildTermMsg(msg) ==
    LET here == fstates[fid].here
        src == msg.src
        excs == msg.excs
    IN /\ NotifyActivityTerminationExcs(excs)
       /\ RecvMsg (msg)

=============================================================================
\* Modification History
\* Last modified Mon Nov 06 19:13:59 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:16:33 AEST 2017 by u5482878
