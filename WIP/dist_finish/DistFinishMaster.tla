-------------------------- MODULE DistFinishMaster --------------------------
(***************************************************************************)
(* Resilient distributed finish master state as implemented for PPoPP14    *)
(* See FinishState.FinishResilientDistributedMaster                        *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS, BACKUP
VARIABLES fstates, msgs, pstate, program, aseq, fseq, mseq, 
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,
           killed, killedCnt, p0fstates, pendingAct, isDead, 
           p0dead, p0adoptSet, p0state, p0convSet,
           fmasters, fbackups, waitForMsgs
INSTANCE Commons
-----------------------------------------------------------------------------                 
RecvAddChild(here) ==
   /\ pstate = "running"
   /\ here \notin killed
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "addChild")
           fid == msg.fid
           eroot == msg.eroot
           src == msg.src
           backupPlace == IF eroot = NoParent THEN PROG_HOME ELSE fmasters[eroot].backupPlace
      IN  /\ src # NotPlace
          /\ fid # NotID
          /\ msg # NotMessage
          /\ IF fid = FIRST_ID
             THEN   /\ here = PROG_HOME
                    /\ fmasters' = fmasters \* will be initialized in transit 
             ELSE   /\ here = fstates[eroot].here
                    /\ fmasters' = [fmasters EXCEPT ![eroot].children = Append (@, fid)]
          /\ ReplaceMsg (msg,
                        [   mid |-> mseq, 
                            src |-> here, 
                            dst |-> backupPlace,
                          eroot |-> eroot,
                            fid |-> fid,
                           type |-> "backupAddChild" ]) 
          /\ mseq' = mseq + 1
          /\ waitForMsgs' = waitForMsgs \cup {[ src |-> backupPlace, 
                                               dst |-> here,  
                                               fid |-> fid, 
                                              type |-> "backupAddChildDone"  ]}
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fbackups >>
                                                     
\* ignore failures when the back dies here, because it is not src or dst of an async
RecvBackupAddChildDone(here) == 
   /\ pstate = "running"
   /\ msgs # {}
   /\ here \notin killed
   /\ LET  msg == FindIncomingMSG(here, "backupAddChildDone")
           fid == msg.fid
           eroot == msg.eroot
           src == msg.src
      IN  /\ src # NotPlace
          /\ fid # NotID
          /\ msg # NotMessage
          /\ IF fid = FIRST_ID
             THEN here = PROG_HOME
             ELSE here = fstates[eroot].here
          /\ ReplaceMsg (msg,
                        [   mid |-> mseq, 
                            src |-> here, 
                            dst |-> fstates[fid].here,
                          eroot |-> eroot,
                            fid |-> fid,
                           type |-> "addChildDone",
                           success |-> TRUE ]) 
          /\ mseq' = mseq + 1
          /\ waitForMsgs' = waitForMsgs \ {[ src |-> src, 
                                               dst |-> here,  
                                               fid |-> fid, 
                                              type |-> "backupAddChildDone"  ]}
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fmasters, fbackups >>

RecvMasterTransit(here) ==
   /\ pstate = "running"
   /\ here \notin killed
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "masterTransit")
           fid == msg.fid
           src == msg.src
           target == msg.target
           backupPlace == GetBackup(here)
      IN  /\ src # NotPlace
          /\ fid # NotID
          /\ msg # NotMessage
          /\ fstates[fid].here = here
          /\ IF fmasters[fid].id = NotID
             THEN fmasters' = [fmasters EXCEPT ![fid].id = fid,
                                               ![fid].backupPlace = backupPlace,
                                               ![fid].transit[src][target] = @ + 1,
                                               ![fid].numActive  =  @ + 2,
                                               ![fid].live[here] = 1 ]
             ELSE fmasters' = [fmasters EXCEPT ![fid].transit[src][target] = @ + 1,
                                               ![fid].numActive = @ + 1 ]
          /\ ReplaceMsg (msg,
                        [   mid |-> mseq, 
                            src |-> here, 
                            dst |-> backupPlace,
                         source |-> src,
                         target |-> target,
                            fid |-> fid,
                           type |-> "backupTransit" ]) 
          /\ mseq' = mseq + 1
          /\ waitForMsgs' = waitForMsgs \cup {[ src |-> backupPlace, 
                                               dst |-> here,  
                                               fid |-> fid, 
                                            source |-> src,
                                            target |-> target,
                                              type |-> "backupTransitDone"  ]}
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fbackups >>

RecvBackupTransitDone(here) ==
   /\ here \notin killed 
   /\ pstate = "running"
   /\ msgs # {}
   /\ here \notin killed
   /\ LET  msg == FindIncomingMSG(here, "backupTransitDone")
           mid == msg.mid
           fid == msg.fid
        source == msg.source
        target == msg.target
           src == msg.src
      IN  /\ msg # NotMessage
          /\ fstates[fid].here = here
          /\ ReplaceMsg (msg,
                        [   mid |-> mseq, 
                            src |-> here, 
                            dst |-> source,
                         target |-> target,
                            fid |-> fid,
                           type |-> "masterTransitDone",
                           success |-> TRUE ]) 
          /\ mseq' = mseq + 1
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fmasters, fbackups, waitForMsgs >>

RecvMasterTransitToLive(here) ==
   /\ pstate = "running"
   /\ here \notin killed
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "masterLive")
           fid == msg.fid
           backupPlace == fmasters[fid].backupPlace
           
      IN  /\ msg # NotMessage
          /\ backupPlace # NotPlace
          /\ fstates[fid].here = here
          /\ LET source == msg.source
                 target == msg.target
                 submit == IF isDead[here][source] \/ isDead[here][target]
                           THEN FALSE
                           ELSE TRUE
             IN  /\ IF submit
                    THEN  /\ fmasters' = [fmasters EXCEPT ![fid].transit[source][target] = @ - 1,
                                                          ![fid].live[target] = @ + 1 ]
                          /\ ReplaceMsg (msg,
                                        [   mid |-> mseq, 
                                            src |-> here, 
                                            dst |-> backupPlace,
                                         source |-> source,
                                         target |-> target,
                                            fid |-> fid,
                                            aid |-> msg.aid,
                                           type |-> "backupLive" ]) 
                          /\ mseq' = mseq + 1
                          /\ waitForMsgs' = waitForMsgs \cup {[ src |-> backupPlace, 
                                                                dst |-> here,  
                                                                fid |-> fid, 
                                                             source |-> source,
                                                             target |-> target,
                                                                aid |-> msg.aid,
                                                               type |-> "backupLiveDone"  ]}
                    ELSE  /\ fmasters' = fmasters
                          /\ waitForMsgs' = waitForMsgs
                          /\ ReplaceMsg (msg,
                                [   mid |-> mseq, 
                                    src |-> here, 
                                    dst |-> target,\*nonic
                                 target |-> target,
                                    fid |-> fid,
                                    aid |-> msg.aid,
                                   type |-> "masterLiveDone",
                                   submit |-> FALSE,
                                   success |-> TRUE ]) 
                          /\ mseq' = mseq + 1
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fbackups >>

RecvBackupLiveDone(here) ==
   /\ here \notin killed 
   /\ pstate = "running"
   /\ msgs # {}
   /\ here \notin killed
   /\ LET  msg == FindIncomingMSG(here, "backupLiveDone")
           mid == msg.mid
           fid == msg.fid
        source == msg.source
        target == msg.target
           src == msg.src
      IN  /\ msg # NotMessage
          /\ fstates[fid].here = here
          /\ ReplaceMsg (msg,
                        [   mid |-> mseq, 
                            src |-> here, 
                            dst |-> target,
                         target |-> target,
                            fid |-> fid,
                            aid |-> msg.aid,
                           type |-> "masterLiveDone",
                           submit |-> TRUE,
                           success |-> TRUE ]) 
          /\ mseq' = mseq + 1
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fmasters, fbackups, waitForMsgs >>               
                   
Quiescent(fid) ==
   fmasters[fid].numActive = 1

\* TODO: if Quiescent release finish
\* TODO: should we block the thread until notify activity termination is done???               
RecvMasterCompleted(here) ==
   /\ pstate = "running"
   /\ here \notin killed
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "masterCompleted")
           mid == msg.mid
           fid == msg.fid
           src == msg.src
           target == msg.target
           backupPlace == fmasters[fid].backupPlace
      IN  /\ msg # NotMessage
          /\ backupPlace # NotPlace
          /\ fstates[fid].here = here
          /\ IF ~isDead[here][target] 
             THEN  /\ fmasters' = [fmasters EXCEPT ![fid].live[target] = @ - 1,
                                                   ![fid].numActive = @ - 1 ]
                   /\ ReplaceMsg (msg,
                                [ mid |-> mseq,
                                  src |-> here, 
                                  dst |-> backupPlace, 
                               target |-> target, 
                                  fid |-> fid, \* always refer to the root state
                                 type |-> "backupCompleted" ]) 
                   /\ mseq' = mseq + 1
                   /\ waitForMsgs' = waitForMsgs \cup {[ src |-> backupPlace, 
                                                        dst |-> here,  
                                                        fid |-> fid, 
                                                     target |-> target,
                                                       type |-> "backupCompletedDone"  ]}
             ELSE   /\ fmasters' = fmasters   \*FIXME: that is not in the actual code, delete it, taken from p0 finish
                    /\ waitForMsgs' = waitForMsgs
                    /\ ReplaceMsg (msg,
                                [ mid |-> mseq,
                                  src |-> here, 
                                  dst |-> target, 
                               target |-> target, 
                                  fid |-> fid, \* always refer to the root state
                                 type |-> "masterCompletedDone",
                                 success |-> TRUE ])
                   /\ mseq' = mseq + 1                                             
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fbackups >>

RecvBackupCompletedDone(here) ==
   /\ here \notin killed 
   /\ pstate = "running"
   /\ msgs # {}
   /\ here \notin killed
   /\ LET  msg == FindIncomingMSG(here, "backupCompletedDone")
           mid == msg.mid
           fid == msg.fid
        target == msg.target
           src == msg.src
      IN  /\ msg # NotMessage
          /\ fstates[fid].here = here
          /\ LET release == fmasters[fid].numActive = 0
             IN IF release
                THEN IF    target = here
                     THEN /\ ReplaceMsg (msg, 
                                   [ mid |-> mseq+1,
                                     src |-> here, 
                                     dst |-> here, 
                                     fid |-> fid,
                                    type |-> "releaseFinish" ]
                              ) 
                          /\ mseq' = mseq + 1
                     ELSE /\ ReplaceMsgSet (msg, {
                                [   mid |-> mseq, 
                                    src |-> here, 
                                    dst |-> target,
                                 target |-> target,
                                    fid |-> fid,
                                   type |-> "masterCompletedDone",
                                   success |-> TRUE],
                                   [ mid |-> mseq+1,
                                     src |-> here, 
                                     dst |-> here, 
                                     fid |-> fid,
                                    type |-> "releaseFinish" ]
                              }) 
                          /\ mseq' = mseq + 2
                ELSE /\ ReplaceMsg (msg, 
                        [   mid |-> mseq, 
                            src |-> here, 
                            dst |-> target,
                         target |-> target,
                            fid |-> fid,
                           type |-> "masterCompletedDone",
                           success |-> TRUE])
                     /\ mseq' = mseq + 1 
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fmasters, fbackups, waitForMsgs >>                                     
=============================================================================
\* Modification History
\* Last modified Sun Nov 12 08:39:07 AEDT 2017 by shamouda
\* Last modified Fri Nov 10 21:02:24 AEDT 2017 by u5482878
\* Created Tue Nov 07 17:51:11 AEDT 2017 by u5482878
