-------------------------- MODULE DistFinishBackup --------------------------
(***************************************************************************)
(* Resilient distributed finish backup state as implemented for PPoPP14    *)
(* See FinishState.FinishResilientDistributedBackup                        *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS,BACKUP
VARIABLES fstates, msgs, pstate, program, aseq, fseq, mseq, 
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,
           killed, killedCnt, p0fstates, pendingAct, isDead, 
           p0dead, p0adoptSet, p0state, p0convSet,
           fmasters, fbackups, waitForMsgs
INSTANCE Commons
-----------------------------------------------------------------------------

BackupRecvAddChild(here) ==
   /\ here \notin killed
   /\ pstate = "running"
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "backupAddChild")
           fid == msg.fid
           eroot == msg.eroot
           src == msg.src
      IN  /\ msg # NotMessage
          /\ IF fid = FIRST_ID
             THEN fbackups' = fbackups 
             ELSE  /\ fmasters[eroot].backupPlace = here
                   /\ IF \E i \in 1..Len(fbackups[eroot].children) : fbackups[eroot].children[i] = fid
                      THEN fbackups' = fbackups 
                      ELSE fbackups' = [fbackups EXCEPT ![eroot].children = Append (@, fid)]
          /\ LET type == IF fid = FIRST_ID 
                         THEN "backupAddChildDone"
                         ELSE IF src = fstates[eroot].here 
                              THEN "backupAddChildDone" 
                              ELSE "addChildDone"
             IN  /\ ReplaceMsg (msg,
                                [   mid |-> mseq, 
                                    src |-> here, 
                                    dst |-> src,
                                  eroot |-> eroot,
                                    fid |-> fid,
                                   type |-> type,
                                   success |-> TRUE ])
                 /\ mseq' = mseq + 1
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fmasters, waitForMsgs >>

BackupRecvTransit(here) ==
   /\ here \notin killed
   /\ pstate = "running"
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "backupTransit")
           fid == msg.fid
           src == msg.src
           source == msg.source
           target == msg.target
      IN  /\ msg # NotMessage
          /\ fmasters[fid].backupPlace = here
          /\ IF fbackups[fid].id = NotID
             THEN fbackups' = [ fbackups EXCEPT ![fid].id = fid,
                                                ![fid].transit[source][target] = @+1,
                                                ![fid].live[src] = 1]
             ELSE fbackups' = [ fbackups EXCEPT ![fid].transit[source][target] = @+1]
          /\ LET type == IF src = fstates[fid].here THEN "backupTransitDone" ELSE "masterTransitDone"
             IN ReplaceMsg (msg,
                        [   mid |-> mseq, 
                            src |-> here, 
                            dst |-> src,
                         target |-> target,
                         source |-> source,
                            fid |-> fid,
                           type |-> type,
                           success |-> TRUE ])
          /\ mseq' = mseq + 1
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fmasters, waitForMsgs >>

BackupRecvLive(here) ==
   /\ here \notin killed
   /\ pstate = "running"
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "backupLive")
           fid == msg.fid
           src == msg.src
           source == msg.source
           target == msg.target
      IN  /\ msg # NotMessage
          /\ fmasters[fid].backupPlace = here
          /\ fbackups' = [ fbackups EXCEPT ![fid].transit[source][target] = @ - 1,
                                           ![fid].live[target] = @ + 1 ]
          /\ LET type == IF src = fstates[fid].here THEN "backupLiveDone" ELSE "masterLiveDone"
             IN ReplaceMsg (msg,
                        [   mid |-> mseq, 
                            src |-> here,
                            dst |-> src,
                         target |-> target,
                            fid |-> fid,
                            aid |-> msg.aid,
                           type |-> type,
                           source |-> source,
                           success |-> TRUE,
                           submit |-> TRUE ])
          /\ mseq' = mseq + 1
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fmasters, waitForMsgs >>

BackupRecvCompleted(here) ==
   /\ here \notin killed
   /\ pstate = "running"
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "backupCompleted")
           fid == msg.fid
           src == msg.src
           target == msg.target
      IN  /\ msg # NotMessage
          /\ fmasters[fid].backupPlace = here
          /\ fbackups' = [ fbackups EXCEPT ![fid].live[target] = @ - 1 ]
          /\ LET type == IF src = fstates[fid].here THEN "backupCompletedDone" ELSE "masterCompletedDone"
             IN ReplaceMsg (msg,
                        [   mid |-> mseq, 
                            src |-> here, 
                            dst |-> src,
                         target |-> target,
                            fid |-> fid,
                           type |-> type,
                           success |-> TRUE]) \* if master died, we don't want to release. if master is alive, we can release
          /\ mseq' = mseq + 1
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0state,p0convSet,
           killed, killedCnt, p0fstates, pendingAct, isDead,p0adoptSet,
           fmasters, waitForMsgs >>

=============================================================================
\* Modification History
\* Last modified Fri Nov 10 20:50:09 AEDT 2017 by u5482878
\* Created Tue Nov 07 17:51:22 AEDT 2017 by u5482878
