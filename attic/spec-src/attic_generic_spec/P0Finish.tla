------------------------------ MODULE P0Finish ------------------------------
(***************************************************************************)
(* Resilient place0 finish (see FinishResilientPlace0.x10)                 *)
(* Limitations: (1) p0 resilient store uses an implicit immediate thread   *)
(*              (2) we don't globalize long chains of local finishes, only *)
(*                  the direct local parent is globalized when the child   *)
(*                  goes global                                            *)
(*              (3) PushException not implemented yet                      *) 
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS
VARIABLES fid, fstates, msgs, thrds, p0fstates, pstate, isDead, mseq,p0adoptSet
INSTANCE Commons
-----------------------------------------------------------------------------
Alloc(type, here, parent, root) == 
    /\ fstates[fid].status = "unused"
    /\ fstates' = [fstates EXCEPT ![fid].id = fid,
                                 ![fid].count = 1,   \* one
                                 ![fid].status = "waiting",
                                 ![fid].type = type,
                                 ![fid].here = here,
                                 ![fid].parent = parent,
                                 ![fid].root = root,
                                 ![fid].isGlobal = IF type = "p0remote" 
                                                   THEN TRUE
                                                   ELSE FALSE]  

SendTransit(dst) ==
    /\ dst # fstates[fid].here
    /\ LET parentId == fstates[fid].parent
          here == fstates[fid].here
          root == fstates[fid].root
          rootPlace == GetFinishHome(fstates[fid].root)
      IN /\ SendMsg([ mid |-> mseq,
                      src |-> here, 
                      dst |-> PROG_HOME, 
                   target |-> dst, 
                      fid |-> root, 
                     pfid |-> parentId, 
                     rfid |-> root,
                     rpl  |-> rootPlace,
                     type |-> "transit" ])
         /\ mseq' = mseq + 1

SendTransitToLive(src, actId, inMsg) ==
    /\ ReplaceMsg(inMsg, 
              [ mid |-> mseq,
                src |-> src, 
                dst |-> PROG_HOME, 
             target |-> fstates[fid].here, 
                fid |-> fstates[fid].root, \* always refer 
                                           \* to the root state 
                aid |-> actId,
               type |-> "live" ])
    /\ mseq' = mseq + 1  

SendLiveToCompleted ==
    /\ SendMsg([ mid |-> mseq,
                src |-> fstates[fid].here, 
                dst |-> PROG_HOME, 
             target |-> fstates[fid].here, 
                fid |-> fstates[fid].root, \* always refer 
                                           \* to the root state
               type |-> "completed" ])
    /\ mseq' = mseq + 1

NotifySubActivitySpawn(dst) ==
    /\ fstates' = [fstates EXCEPT ![fid].isGlobal = TRUE ]
    /\ SendTransit(dst)

NotifySubActivitySpawnError(dst) == FALSE

NotifyLocalActivitySpawnAndCreation (here, act) ==
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]
   
NotifyRemoteActivityCreation(src, act, inMsg) ==
    /\ SendTransitToLive(src, act.aid, inMsg)
    /\ fstates' = fstates

LastActivity ==
    /\ fstates[fid].count = 1
      
NotifyActivityTermination ==
    /\ fstates[fid].count > 0
    /\ IF LastActivity
       THEN fstates' = [fstates EXCEPT ![fid].count = @-1,
                                       ![fid].status = "finished"]
       ELSE fstates' = [fstates EXCEPT ![fid].count = @-1]

PushException(e) ==
    FALSE  
      
SendTermMsg ==
    IF  ~fstates[fid].isGlobal
    THEN  /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"]
          /\ msgs' = msgs
          /\ mseq' = mseq
    ELSE  /\ SendLiveToCompleted
          /\ fstates' = [fstates EXCEPT ![fid].status = IF fstates[fid].type = "p0remote"
                                                        THEN  "forgotten"
                                                        ELSE  "p0finished"]
                                     
ProcessChildTermMsg(msg) ==
    FALSE
    
=============================================================================
\* Modification History
\* Last modified Mon Nov 06 19:08:39 AEDT 2017 by u5482878
\* Last modified Sun Nov 05 01:01:52 AEDT 2017 by shamouda
\* Created Fri Oct 13 15:16:37 AEDT 2017 by u5482878
