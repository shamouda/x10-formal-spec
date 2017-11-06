------------------------------ MODULE DEFRoot ------------------------------
(***************************************************************************)
(* The default root finish imeplementation                                 *)
(* See FinishState.RootFinish for the actual implementation                *)
(***************************************************************************)
VARIABLES fid, fstates, msgs, thrds, mseq, p0adoptSet
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS
INSTANCE Commons
----------------------------------------------------------------------------
Alloc(type, here, parent, root) == \* parent not used here
   /\ fstates[fid].status = "unused"
   /\ fstates' = [fstates EXCEPT ![fid].id = fid,
                                 ![fid].count = 1, 
                                 ![fid].status = "waiting",
                                 ![fid].type = type,
                                 ![fid].here = here,
                                 ![fid].root = root] 

NotifySubActivitySpawn(dst) == 
   LET here == fstates[fid].here
   IN  \/ /\ dst = here
          /\ fstates' = [fstates EXCEPT ![fid].count = @+1]
       \/ /\ dst # here
          /\ fstates' = [fstates EXCEPT ![fid].remActs[dst] = @+1]

NotifySubActivitySpawnError(dst) == FALSE
    
NotifyRemoteActivityCreation(src, activity, inMsg) == 
    /\ fstates' = fstates
    /\ RecvMsg (inMsg)

NotifyLocalActivitySpawnAndCreation (here, activity) ==
    NotifySubActivitySpawn(here)  

LastActivity ==
    /\ fstates[fid].count = 1
    /\ \A p \in PLACE: fstates[fid].remActs[p] = 0
    
NotifyActivityTermination == 
    /\ fstates[fid].count > 0
    /\ IF LastActivity
       THEN fstates' = [fstates EXCEPT ![fid].count = @-1,
                                       ![fid].status = "finished"] 
       ELSE fstates' = [fstates EXCEPT ![fid].count = @-1]

PushException(e) == 
    /\ fstates' = [fstates EXCEPT ![fid].excs = Append(@, e)]

SendTermMsg ==
    /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"]
    /\ msgs' = msgs
    /\ mseq' = mseq
    
LastActivity2(here, msgRemActs) ==
    /\ fstates[fid].count + msgRemActs[here] = 0
    /\ \A p \in PLACE \ {here}: fstates[fid].remActs[p] + msgRemActs[p] = 0

ProcessChildTermMsg(msg) ==
    LET here == fstates[fid].here
        src == msg.src
        remActs == msg.remActs
        excs == msg.excs
    IN  /\ IF LastActivity2(here, remActs)
           THEN  fstates' = [fstates EXCEPT ![fid].remActs =  [ p \in PLACE |->  
                                                IF p = here 
                                                THEN fstates[fid].remActs[p]
                                                ELSE fstates[fid].remActs[p] + remActs[p]], 
                                            ![fid].count = @ + remActs[here],
                                            ![fid].excs = @ \o excs,
                                            ![fid].status = "finished" ]
           ELSE  fstates' = [fstates EXCEPT ![fid].remActs = [ p \in PLACE |->  
                                                IF p = here 
                                                THEN fstates[fid].remActs[p]
                                                ELSE fstates[fid].remActs[p] + remActs[p]],
                                            ![fid].excs = @ \o excs, 
                                            ![fid].count = @ + remActs[here]]
        /\ RecvMsg (msg)
=============================================================================
\* Modification History
\* Last modified Mon Nov 06 19:13:06 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:16:49 AEST 2017 by u5482878
