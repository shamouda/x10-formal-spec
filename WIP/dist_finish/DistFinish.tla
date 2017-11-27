----------------------------- MODULE DistFinish -----------------------------
(***************************************************************************)
(* Resilient distributed finish as implemented in PPoPP14                  *)
(* See FinishState.FinishResilientDistributed                              *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS, BACKUP
VARIABLES fid, fstates, msgs, thrds, p0fstates, pstate, isDead, mseq,p0adoptSet, waitForMsgs
INSTANCE Commons

SendMasterAddChild(eroot, erootPlace, here) ==
    /\ SendMsg([ mid |-> mseq,
                 src |-> here, 
                 dst |-> erootPlace,  
                 eroot |-> eroot,
                 fid   |-> fid, 
                 type |-> "addChild" ])
    /\ mseq' = mseq + 1
    /\ waitForMsgs' = waitForMsgs \cup {[ src |-> erootPlace, 
                                         dst |-> here,  
                                         fid |-> fid, 
                                         eroot |-> eroot ,
                                        type |-> "addChildDone"  ]}

SendMasterTransit(dst) ==
    /\ dst # fstates[fid].here
    /\ LET parentId == fstates[fid].parent
           here == fstates[fid].here
           root == fstates[fid].root
           rootPlace == GetFinishHome(fstates[fid].root)
       IN /\ SendMsg([ mid |-> mseq,
                       src |-> here, 
                       dst |-> rootPlace, 
                    target |-> dst, 
                       fid |-> root, 
                      type |-> "masterTransit" ])
          /\ waitForMsgs' = waitForMsgs \cup {[ src |-> rootPlace, 
                                               dst |-> here,  
                                               fid |-> fid,
                                              type |-> "masterTransitDone"  ]}    
          /\ mseq' = mseq + 1

SendMasterTransitToLive(src, actId, inMsg) ==
    LET root == fstates[fid].root
        rootPlace == GetFinishHome(fstates[fid].root)
    IN  /\ ReplaceMsg(inMsg, 
              [ mid |-> mseq,
                src |-> fstates[fid].here,
             source |-> src,
             target |-> fstates[fid].here, 
                dst |-> rootPlace, 
                fid |-> root, \* always refer to the root state 
                aid |-> actId,
               type |-> "masterLive" ])
        /\ waitForMsgs' = waitForMsgs \cup {[ src |-> rootPlace, 
                                             dst |-> fstates[fid].here,  
                                          source |-> src,
                                             fid |-> fid,
                                             aid |-> actId,
                                            type |-> "masterLiveDone"  ]}   
        /\ mseq' = mseq + 1  
  
SendMasterLiveToCompleted ==
    LET root == fstates[fid].root
        rootPlace == GetFinishHome(fstates[fid].root)
    IN /\ SendMsg([ mid |-> mseq,
                    src |-> fstates[fid].here, 
                    dst |-> rootPlace, 
                 target |-> fstates[fid].here, 
                    fid |-> root, \* always refer to the root state
                   type |-> "masterCompleted" ])
        /\ waitForMsgs' = waitForMsgs \cup {[ src |-> rootPlace, 
                                              dst |-> fstates[fid].here,  
                                           target |-> fstates[fid].here,
                                              fid |-> fid,
                                             type |-> "masterCompletedDone"  ]}   
       /\ mseq' = mseq + 1

LastActivity ==
    /\ fstates[fid].count = 1
-----------------------------------------------------------------------------
Alloc(type, here, parent, root) ==
    LET encRoot ==  GetEnclosingRoot(parent, fid)
        encRootPlace == IF fid = FIRST_ID THEN PROG_HOME ELSE fstates[encRoot].here
    IN /\ fstates[fid].status = "unused"
       /\ fstates' = [fstates EXCEPT ![fid].id = fid,
                                     ![fid].count = 1,
                                     ![fid].status = "waiting",
                                     ![fid].type = type,
                                     ![fid].here = here,
                                     ![fid].parent = parent,
                                     ![fid].root = root,
                                     ![fid].eroot = encRoot,
                                     ![fid].isGlobal = IF type = "distremote" 
                                                       THEN TRUE 
                                                       ELSE FALSE ]
       /\ IF type = "distroot"
          THEN SendMasterAddChild(encRoot, encRootPlace, here)
          ELSE TRUE

NotifyLocalActivitySpawnAndCreation (here, act) ==
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]
    
NotifySubActivitySpawn(dst) == 
    /\ fstates' = [fstates EXCEPT ![fid].isGlobal = TRUE ]
    /\ SendMasterTransit(dst)
        
NotifyRemoteActivityCreation(src, act, inMsg) ==
    /\ SendMasterTransitToLive(src, act.aid, inMsg)
    /\ fstates' = fstates
   
NotifyActivityTermination ==
    /\ fstates[fid].count > 0
    /\ IF LastActivity /\ ~fstates[fid].isGlobal
       THEN /\ fstates' = [fstates EXCEPT ![fid].count = @-1,
                                          ![fid].status = "forgotten"]
            /\ msgs' = msgs
            /\ mseq' = mseq  
            /\ waitForMsgs' = waitForMsgs                                  
       ELSE IF LastActivity /\ fstates[fid].isGlobal
       THEN /\ SendMasterLiveToCompleted
            /\ fstates' = [fstates EXCEPT ![fid].count = @-1,
                                          ![fid].status = IF fstates[fid].type = "p0remote"
                                                          THEN  "forgotten"
                                                          ELSE  "p0finished"] 
       ELSE /\ fstates' = [fstates EXCEPT ![fid].count = @-1]
            /\ msgs' = msgs
            /\ mseq' = mseq
            /\ waitForMsgs' = waitForMsgs 

SendTermMsg ==
    IF  ~fstates[fid].isGlobal
    THEN  /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"]
          /\ msgs' = msgs
          /\ mseq' = mseq
    ELSE  /\ SendMasterLiveToCompleted
          /\ fstates' = [fstates EXCEPT ![fid].status = IF fstates[fid].type = "distremote"
                                                        THEN  "forgotten"
                                                        ELSE  "p0finished"]


PushException(e) == FALSE

ProcessChildTermMsg(msg) == FALSE

NotifySubActivitySpawnError(dst) == FALSE

=============================================================================
\* Modification History
\* Last modified Sat Nov 11 15:33:09 AEDT 2017 by shamouda
\* Last modified Fri Nov 10 19:04:10 AEDT 2017 by u5482878
\* Created Tue Nov 07 17:50:59 AEDT 2017 by u5482878
