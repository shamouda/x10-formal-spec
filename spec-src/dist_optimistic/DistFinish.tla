----------------------------- MODULE DistFinish -----------------------------
(***************************************************************************)
(* Resilient distributed finish as implemented in PPoPP14                  *)
(* See FinishState.FinishResilientDistributed                              *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS PLACE, MXFINISHES, PROG_HOME, BACKUP
VARIABLES fid, fstates, msgs, thrds, pstate, waitForMsgs, killed, fbackups, seq

INSTANCE Commons

Terminated ==
    /\ fstates[fid].status = "forgotten"

Running ==
    /\ fstates[fid].status = "waiting"

IsRoot ==
    /\ fstates[fid].type = "distroot"
    
LastActivity ==
    /\ fstates[fid].count = 1


SendMasterTransit(dst) ==
    /\ dst # fstates[fid].here
    /\ LET parentId == fstates[fid].parent
           here == fstates[fid].here
           root == fstates[fid].root
           rootPlace == GetFinishHome(fstates[fid].root)
       IN /\ SendMsg([ mid |-> seq.mseq,
                       src |-> here, 
                       dst |-> rootPlace, 
                    target |-> dst, 
                       fid |-> root, 
                   taskFID |-> fid,
                 finishSrc |-> fstates[fid].src,
                      type |-> "masterTransit" ])
          /\ waitForMsgs' = waitForMsgs \cup {[ src |-> rootPlace, 
                                               dst |-> here,  
                                            target |-> dst,
                                               fid |-> root,
                                           taskFID |-> fid,
                                         finishSrc |-> fstates[fid].src,
                                              type |-> "masterTransitDone"  ]}    
          /\ IncrMSEQ(1)
  
SendMasterLiveToCompleted(source, finishEnd) ==
    LET root == fstates[fid].root
        rootPlace == GetFinishHome(fstates[fid].root)
        here == fstates[fid].here
    IN /\ SendMsg([ mid |-> seq.mseq,
                    src |-> here, 
                    dst |-> rootPlace, 
                 source |-> IF finishEnd THEN here ELSE source,
                 target |-> here, 
                    fid |-> root,
                taskFID |-> fid,
              finishEnd |-> finishEnd,
                   type |-> "masterCompleted" ])
       /\ waitForMsgs' = waitForMsgs \cup {[ src |-> rootPlace, 
                                             dst |-> here,
                                          source |-> IF finishEnd THEN here ELSE source,
                                          target |-> here,
                                             fid |-> root,
                                         taskFID |-> fid,
                                            type |-> "masterCompletedDone"  ]}
       /\ IncrMSEQ(1)

-----------------------------------------------------------------------------
Alloc(type, here, parent, root, finishSrc) ==
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
                                     ![fid].isGlobal = (type = "distremote"),
                                     ![fid].src      = IF type = "distroot"
                                                        THEN finishSrc
                                                        ELSE NotPlace,
                                     ![fid].received[finishSrc] = @ + 1 ]
\*needed for the local path of Runtime.runAsync
NotifyLocalActivitySpawnAndCreation (here, act) ==
    /\ fstates[fid].status = "waiting"
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1]
    
NotifySubActivitySpawn(dst) == 
    /\ fstates[fid].status = "waiting"
    /\ fstates' = [fstates EXCEPT ![fid].isGlobal = TRUE ]
    /\ SendMasterTransit(dst)
        
AllocRemoteAndNotifyRemoteActivityCreation(src, act, inMsg, type, here, parent, root, finishSrc) ==
    /\ RecvMsg(inMsg)
    /\ here # NotPlace
    /\ type = "distremote"               \* create and notify
    /\ Alloc(type, here, parent, root, finishSrc)

NotifyRemoteActivityCreation(src, act, inMsg, type, here, parent, root, finishSrc) ==
    /\ RecvMsg(inMsg)
    /\ here # NotPlace
    /\ type = "distremote"  
    /\ fstates' = [ fstates EXCEPT ![fid].received[finishSrc] = @ + 1 ]            
       
NotifyActivityTermination(source, finishEnd) ==
    /\ fstates[fid].status = "waiting" 
    /\ fstates[fid].count > 0
    /\ IF LastActivity /\ ~fstates[fid].isGlobal
       THEN /\ fstates' = [fstates EXCEPT ![fid].count = @-1,
                                          ![fid].status = "forgotten"]
            /\ msgs' = msgs
            /\ seq' = seq  
            /\ waitForMsgs' = waitForMsgs   
       ELSE IF LastActivity /\ fstates[fid].isGlobal
            THEN /\ SendMasterLiveToCompleted(source, finishEnd)
                 /\ fstates' = [fstates EXCEPT ![fid].count = @-1,
                                               ![fid].status = IF fstates[fid].type = "distremote"
                                                               THEN  "forgotten"
                                                               ELSE  "pendingRelease"] 
            ELSE /\ fstates' = [fstates EXCEPT ![fid].count = @-1]
                 /\ msgs' = msgs
                 /\ seq' = seq
                 /\ waitForMsgs' = waitForMsgs 

=============================================================================
\* Modification History
\* Last modified Thu Dec 14 18:05:06 AEDT 2017 by u5482878
\* Last modified Sun Dec 10 12:28:32 AEDT 2017 by shamouda
\* Created Tue Nov 07 17:50:59 AEDT 2017 by u5482878
