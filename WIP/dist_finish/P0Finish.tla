------------------------------ MODULE P0Finish ------------------------------
(***************************************************************************)
(* Resilient place0 finish (see FinishResilientPlace0.x10)                 *)
(* Limitations: (1) p0 resilient store uses an implicit immediate thread   *)
(*              (2) we don't globalize chains of local finishes            *)
(*              (3) PushException not implemented yet                      *) 
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS,BACKUP
VARIABLES fid, fstates, msgs, thrds, p0fstates, pstate, isDead, mseq,p0adoptSet,waitForMsgs
INSTANCE Commons
-----------------------------------------------------------------------------
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
         /\ waitForMsgs' = waitForMsgs

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

LastActivity ==
    /\ fstates[fid].count = 1
  
---------------------------------------------------------------------------
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

NotifyLocalActivitySpawnAndCreation (here, act) ==
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]
    
NotifySubActivitySpawn(dst) ==
    /\ fstates' = [fstates EXCEPT ![fid].isGlobal = TRUE ]
    /\ SendTransit(dst)

   
NotifyRemoteActivityCreation(src, act, inMsg) ==
    /\ SendTransitToLive(src, act.aid, inMsg)
    /\ fstates' = fstates
    /\ waitForMsgs' = waitForMsgs
    
NotifyActivityTermination ==
    /\ fstates[fid].count > 0
    /\ IF LastActivity /\ ~fstates[fid].isGlobal
       THEN /\ fstates' = [fstates EXCEPT ![fid].count = @-1,
                                          ![fid].status = "forgotten"]
            /\ msgs' = msgs
            /\ mseq' = mseq                                    
       ELSE IF LastActivity /\ fstates[fid].isGlobal
       THEN /\ SendLiveToCompleted
            /\ fstates' = [fstates EXCEPT ![fid].count = @-1,
                               ![fid].status = IF fstates[fid].type = "p0remote"
                                               THEN  "forgotten"
                                               ELSE  "p0finished"] 
       ELSE /\ fstates' = [fstates EXCEPT ![fid].count = @-1]
            /\ msgs' = msgs
            /\ mseq' = mseq
    /\ waitForMsgs' = waitForMsgs
   
NotifySubActivitySpawnError(dst) == FALSE  \* not needed we will remove it soon

PushException(e) ==
    FALSE  
                                        
ProcessChildTermMsg(msg) ==  \* it does not receive any termination messages. all term messages are sent to p0store
    FALSE
    
=============================================================================
\* Modification History
\* Last modified Sun Nov 12 08:25:04 AEDT 2017 by shamouda
\* Last modified Fri Nov 10 17:45:28 AEDT 2017 by u5482878
\* Created Fri Oct 13 15:16:37 AEDT 2017 by u5482878
