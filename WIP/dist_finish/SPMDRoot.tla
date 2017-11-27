----------------------------- MODULE SPMDRoot -----------------------------
(***************************************************************************)
(* A Single Program Multi Data root finish                                 *)
(* See FinishState.RootFinishSPMD for the actual implementation            *)
(***************************************************************************)
EXTENDS Sequences, Integers
---------------------------------------------------------------------------
VARIABLES fid, fstates, msgs, thrds, mseq,p0adoptSet, waitForMsgs
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS,BACKUP
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
    /\ IF LastActivity
       THEN fstates' = [fstates EXCEPT ![fid].count = @-1,
                                       ![fid].status = "forgotten"] 
       ELSE fstates' = [fstates EXCEPT ![fid].count = @-1]
    /\ msgs' = msgs
    /\ mseq' = mseq
    /\ waitForMsgs' = waitForMsgs

PushException(e) == 
    /\ fstates' = [fstates EXCEPT ![fid].excs = Append(@, e)]

ProcessChildTermMsg(msg) ==
    LET here == fstates[fid].here
        src == msg.src
        excs == msg.excs
    IN  /\ fstates[fid].count > 0
        /\ RecvMsg (msg)
        /\ mseq' = mseq
        /\ waitForMsgs' = waitForMsgs 
        /\ IF LastActivity 
           THEN fstates' = [fstates EXCEPT ![fid].count = @-1,
                                           ![fid].status = "forgotten",
                                           ![fid].excs = @ \o excs] 
           ELSE fstates' = [fstates EXCEPT ![fid].count = @-1,
                                           ![fid].excs = @ \o excs]
=============================================================================
\* Modification History
\* Last modified Sun Nov 12 08:25:33 AEDT 2017 by shamouda
\* Last modified Fri Nov 10 17:45:02 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:16:33 AEST 2017 by u5482878
