---------------------------- MODULE AsyncFinishReplication ----------------------------
(**************************************************************************)
EXTENDS Integers

CONSTANTS CLIENT_NUM,     \* the number of clients                        
          MAX_KILL        \* maximum allowed kill events                  

VARIABLES state,          \* the program state, running or terminated     
          clients,        \* clients sending value update requests to master and backup                            
          master,         \* pool of master instances, only one is active 
          backup,         \* pool of backup instances, only one is active 
          msgs,           \* in-flight messages                           
          killed          \* number of invoked kill actions to master or backup                                       

Vars == << state, clients, master, backup, msgs, killed >>
----------------------------------------------------------------------------
C == INSTANCE Commons
----------------------------------------------------------------------------
TypeOK ==
  (*************************************************************************)
  (* Variables type constrains                                             *)
  (*************************************************************************)
  /\ clients \in [ C!CLIENT_ID -> C!Client ]
  /\ master \in [ C!INSTANCE_ID -> C!Master ]
  /\ backup \in [ C!INSTANCE_ID -> C!Backup ]
  /\ state \in { "running", "terminated", "fatal" }
  /\ msgs \subseteq C!Messages
  /\ killed \in 0..MAX_KILL

StateOK ==
  (*************************************************************************)
  (* State invariants:                                                     *)
  (* - master version >= backup version                                    *)
  (* - upon termination, the final version = the number of clients         *)
  (* - if a fatal error occured, this must indicate the failure of both    *)
  (*   the master and the backup known by the client                       *)
  (*************************************************************************)
  LET curMaster == C!LastKnownMaster
      curBackup == C!LastKnownBackup
  IN /\ curMaster.version >= curBackup.version
     /\ IF state = "terminated"
        THEN /\ curMaster.version = CLIENT_NUM 
             /\ curBackup.version = CLIENT_NUM
        ELSE /\ curMaster.version <= CLIENT_NUM 
             /\ curBackup.version <= CLIENT_NUM
     /\ IF state = "fatal"
        THEN \E c \in C!CLIENT_ID : 
                /\ clients[c].phase = C!PH2_COMPLETED_FATAL
                /\ master[clients[c].masterId].status = C!INST_STATUS_LOST
                /\ IF clients[c].backupId # C!UNKNOWN_ID
                   THEN backup[clients[c].backupId].status = C!INST_STATUS_LOST
                   ELSE TRUE
        ELSE TRUE

----------------------------------------------------------------------------             
MustTerminate ==
  (*************************************************************************)
  (* The program must terminate by having all clients complete their       *)
  (* update actions on both master and backup                              *)
  (*************************************************************************)
   <> ( state \in { "terminated", "fatal" } )

----------------------------------------------------------------------------
Init ==
  (*************************************************************************)
  (* Initialiaze variables                                                 *)
  (*************************************************************************)
  /\ state = "running"
  /\ clients = [ i \in C!CLIENT_ID |->  [ id |-> i , phase |-> C!PH1_PENDING, 
                 value |-> i,  masterId |-> C!FIRST_ID, backupId |-> C!UNKNOWN_ID ] ]
  /\ backup = [ i \in C!INSTANCE_ID |-> 
               IF i = C!FIRST_ID 
               THEN [ id |-> C!FIRST_ID, masterId |-> C!FIRST_ID, status |-> C!INST_STATUS_ACTIVE, 
                      value |-> 0, version |-> 0 ]
               ELSE [ id |-> i, masterId |-> C!UNKNOWN_ID, status |-> C!INST_STATUS_NULL, 
                      value |-> 0, version |-> 0 ] ]
  /\ master = [ i \in C!INSTANCE_ID |-> 
               IF i = C!FIRST_ID 
               THEN [ id |-> C!FIRST_ID, backupId |-> C!FIRST_ID, status |-> C!INST_STATUS_ACTIVE, 
                      value |-> 0, version |-> 0 ]
               ELSE [ id |-> i, backupId |-> C!UNKNOWN_ID, status |-> C!INST_STATUS_NULL, 
                      value |-> 0, version |-> 0 ] ]
  /\ msgs = {}
  /\ killed = 0
  
----------------------------------------------------------------------------
AtLeastOneClientStarted ==
  (*************************************************************************)
  (* We use this condition to prevent killing a master or backup before at *)
  (* least one client starts                                               *)
  (*************************************************************************) 
  \/ /\ killed > 0 
  \/ /\ killed = 0 
     /\ \E c \in C!CLIENT_ID : clients[c].phase # C!PH1_PENDING

KillMaster ==
  (*************************************************************************)
  (* Kill the active master instance.                                      *)
  (*************************************************************************)
  /\ state = "running"
  /\ AtLeastOneClientStarted
  /\ killed < MAX_KILL
  /\ LET activeM == C!FindMaster(C!INST_STATUS_ACTIVE)
     IN /\ activeM # C!NOT_MASTER
        /\ master' = [ master EXCEPT ![activeM.id].status = C!INST_STATUS_LOST ]
        /\ killed' = killed + 1
  /\ UNCHANGED << state, clients, backup, msgs >>

KillBackup ==
  (*************************************************************************)
  (* Kill the active backup instance.                                      *)
  (*************************************************************************)
  /\ state = "running"
  /\ AtLeastOneClientStarted
  /\ killed < MAX_KILL
  /\ LET activeB == C!FindBackup(C!INST_STATUS_ACTIVE)
     IN /\ activeB # C!NOT_BACKUP
        /\ backup' = [ backup EXCEPT ![activeB.id].status = C!INST_STATUS_LOST ]
        /\ killed' = killed + 1
  /\ UNCHANGED << state, clients, master, msgs >>

C_Start ==
  (*************************************************************************)
  (* Client start the replication process by sending "do" to master        *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET client == C!FindClient(C!PH1_PENDING)
     IN  /\ client # C!NOT_CLIENT
         /\ C!SendMsg( [ from |-> "c",
                       to |-> "m",
                       clientId |-> client.id,
                       masterId |-> client.masterId,
                       backupId |-> C!UNKNOWN_ID,
                       value |-> client.value,
                       tag |-> "masterDo" ] )
         /\ clients' = [ clients EXCEPT ![client.id].phase = C!PH2_WORKING ] 
  /\ UNCHANGED << state, master, backup, killed >>

M_HandleDo ==
  (*************************************************************************)
  (* Master receiving "do", updating value, and sending "done"             *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET msg == C!FindMessageToWithTag("m", C!INST_STATUS_ACTIVE, "masterDo")
     IN /\ msg # C!NOT_MESSAGE
        /\ master' = [ master EXCEPT ![msg.masterId].value = master[msg.masterId].value + msg.value,
                                     ![msg.masterId].version = master[msg.masterId].version + 1 ]
        /\ C!ReplaceMsg( msg, [ from |-> "m",
                              to |-> "c",
                              clientId |-> msg.clientId,
                              masterId |-> msg.masterId,
                              backupId |-> master[msg.masterId].backupId ,
                              value |-> 0,
                              tag |-> "masterDone" ] )
  /\ UNCHANGED << state, clients, backup, killed >>

C_HandleMasterDone ==
  (*************************************************************************)
  (* Client receiving "done" from master, and forwarding action to backup  *)
  (*************************************************************************) 
  /\ state = "running"
  /\ LET msg == C!FindMessageToClient("m", "masterDone")
     IN /\ msg # C!NOT_MESSAGE
        /\ C!ReplaceMsg( msg, [ from |-> "c",
                              to |-> "b",
                              clientId |-> msg.clientId,
                              masterId |-> msg.masterId,
                              backupId |-> msg.backupId,
                              value |-> clients[msg.clientId].value,
                              tag |-> "backupDo" ] )
        \* update our knowledge about the backup identity
        /\ clients' = [ clients EXCEPT ![msg.clientId].backupId = msg.backupId ]
  /\ UNCHANGED << state, master, backup, killed >>

B_HandleDo == 
  (*************************************************************************)
  (* Backup receiving "do", updating value, then sending "done"            *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET msg == C!FindMessageToWithTag("b", C!INST_STATUS_ACTIVE, "backupDo")
     IN /\ msg # C!NOT_MESSAGE
        /\ IF msg.masterId = backup[msg.backupId].masterId
           THEN (* Master info is consistent between client and backup *)
                /\ backup' = [ backup EXCEPT ![msg.backupId].value = backup[msg.backupId].value + msg.value,
                                             ![msg.backupId].version = backup[msg.backupId].version + 1 ]
                /\ C!ReplaceMsg( msg, [ from |-> "b",
                                      to |-> "c",
                                      clientId |-> msg.clientId,
                                      masterId |-> msg.masterId,
                                      backupId |-> msg.backupId,
                                      value |-> 0,
                                      tag |-> "backupDone" ] )
           ELSE (* Master has changed, client must restart *)
                /\ backup' = backup  
                /\ C!ReplaceMsg( msg, [ from |-> "b",
                                      to |-> "c",
                                      clientId |-> msg.clientId,
                                      masterId |-> backup[msg.backupId].masterId,
                                      backupId |-> msg.backupId,
                                      value |-> 0,
                                      tag |-> "newMasterId" ] )
  /\ UNCHANGED << state, clients, master, killed >>
 
C_HandleBackupDone ==
  (*************************************************************************)
  (* Client receiving "done" from backup. Replication completed            *)
  (*************************************************************************) 
  /\ state = "running"
  /\ LET msg == C!FindMessageToClient("b", "backupDone")
     IN /\ msg # C!NOT_MESSAGE
        /\ C!RecvMsg( msg )
        /\ clients' = [ clients EXCEPT ![msg.clientId].phase = C!PH2_COMPLETED ]
  /\ UNCHANGED << state, master, backup, killed >>

--------------------------------------------------------------------------------
Sys_NotifyMasterFailure ==
  (*************************************************************************)
  (* System notifying client of a dead master                              *)
  (*************************************************************************) 
  /\ state = "running"
  /\ LET msg == C!FindMessageTo("m", C!INST_STATUS_LOST)
     IN /\ msg # C!NOT_MESSAGE
        /\ LET notifyTag == IF msg.tag = "masterDo" 
                            THEN "masterDoFailed"
                            ELSE IF msg.tag = "masterGetNewBackup" 
                            THEN "masterGetNewBackupFailed"
                            ELSE "INVALID" \* this should be unreachable
           IN /\ notifyTag # "INVALID" 
              /\ C!ReplaceMsg( msg,
                   [ from |-> "sys",
                     to |-> "c",
                     clientId |-> msg.clientId,
                     masterId |-> C!UNKNOWN_ID,
                     backupId |-> C!UNKNOWN_ID,
                     value |-> 0,
                     tag |-> notifyTag ] )
  /\ UNCHANGED << state, clients, master, backup, killed >>

Sys_NotifyBackupFailure == 
  (*************************************************************************)
  (* System notifying client of a dead backup                              *)
  (*************************************************************************) 
  /\ state = "running"
  /\ LET msg == C!FindMessageTo("b", C!INST_STATUS_LOST)
     IN /\ msg # C!NOT_MESSAGE
        /\ LET notifyTag == IF msg.tag = "backupDo" 
                            THEN "backupDoFailed"
                            ELSE IF msg.tag = "backupGetNewMaster"
                            THEN "backupGetNewMasterFailed"
                            ELSE "INVALID" \* this should be unreachable
           IN /\ notifyTag # "INVALID" 
              /\ C!ReplaceMsg( msg,
                   [ from |-> "sys",
                     to |-> "c",
                     clientId |-> msg.clientId,
                     masterId |-> C!UNKNOWN_ID,
                     backupId |-> C!UNKNOWN_ID,
                     value |-> 0,
                     tag |-> notifyTag ] )
  /\ UNCHANGED << state, clients, master, backup, killed >>

--------------------------------------------------------------------------------
C_HandleMasterDoFailed ==
  (*************************************************************************)
  (* Client received the system's notification of a dead master, and       *)
  (* is requesting the backup to return the new master info                *)
  (*************************************************************************) 
  /\ state = "running"
  /\ LET msg == C!FindMessageToClient("sys", "masterDoFailed")
         knownBackup == IF msg # C!NOT_MESSAGE 
                        THEN C!SearchForBackup
                        ELSE C!NOT_BACKUP
     IN /\ msg # C!NOT_MESSAGE
        /\ IF knownBackup = C!NOT_BACKUP
           THEN /\ C!RecvMsg (msg)
                /\ state' = "fatal"
                /\ clients' = [ clients EXCEPT ![msg.clientId].phase = C!PH2_COMPLETED_FATAL]
           ELSE /\ C!ReplaceMsg( msg, [ from |-> "c",
                                      to |-> "b",
                                      clientId |-> msg.clientId,
                                      \* send the client's master knowledge, 
                                      \* to force the backup to not respond until rereplication
                                      masterId |-> clients[msg.clientId].masterId,
                                      backupId |-> knownBackup.id,
                                      value |-> 0,
                                      tag |-> "backupGetNewMaster" ])
                /\ state' = state
                /\ clients' = clients
  /\ UNCHANGED << master, backup, killed >>

C_HandleBackupDoFailed ==
  (*************************************************************************)
  (* Client received the system's notification of a dead backup, and       *)
  (* is requesting the master to return the new backup info                *)
  (*************************************************************************) 
  /\ state = "running"
  /\ LET msg == C!FindMessageToClient("sys", "backupDoFailed")
     IN /\ msg # C!NOT_MESSAGE
        /\ C!ReplaceMsg( msg, [ from |-> "c",
                                to |-> "m",
                                clientId |-> msg.clientId,
                                masterId |-> clients[msg.clientId].masterId,
                                \* send the client's backup knowledge, 
                                \* to force the master to not respond until rereplication
                                backupId |-> clients[msg.clientId].backupId,
                                value |-> 0,
                                tag |-> "masterGetNewBackup" ])
  /\ UNCHANGED << state, clients, master, backup, killed >>

----------------------------------------------------------------------------------
M_HandleGetNewBackup == 
  (*************************************************************************)
  (* Master responding to client with updated backup identity              *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET msg == C!FindMessageToWithTag("m", C!INST_STATUS_ACTIVE, "masterGetNewBackup" )
     IN /\ msg # C!NOT_MESSAGE
           \* master must not respond until it recovers the dead backup
        /\ msg.backupId # master[msg.masterId].backupId
        /\ C!ReplaceMsg( msg, [ from |-> "m",
                                to |-> "c",
                                clientId |-> msg.clientId,
                                masterId |-> msg.masterId,
                                backupId |-> master[msg.masterId].backupId,
                                value |-> 0,
                                tag |-> "newBackupId" ])
  /\ UNCHANGED << state, clients, master, backup, killed >>
  
B_HandleGetNewMaster == 
  (*************************************************************************)
  (* Backup responding to client with updated master identity              *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET msg == C!FindMessageToWithTag("b", C!INST_STATUS_ACTIVE, "backupGetNewMaster")
     IN /\ msg # C!NOT_MESSAGE
           \* backup must not respond until it recovers the dead master
        /\ msg.masterId # backup[msg.backupId].masterId 
        /\ C!ReplaceMsg( msg, [ from |-> "b",
                                to |-> "c",
                                clientId |-> msg.clientId,
                                masterId |-> backup[msg.backupId].masterId,
                                backupId |-> msg.backupId,
                                value |-> 0,
                                tag |-> "newMasterId" ])
  /\ UNCHANGED << state, clients, master, backup, killed >>

-----------------------------------------------------------------------------------
C_HandleBackupGetNewMasterFailed ==
  (*************************************************************************)
  (* The client handling the failure of the backup, when the client asked  *)
  (* the backup to return the new master identity. The client mannually    *)
  (* searches for the master.                                              *)
  (* If manual search does not find a master, a fatal error occurs.        *)
  (* Otherwise, the client updates it's masterId and eventually restarts.  *)
  (* Restarting is safe because this action is reached only if "masterDo"  *)
  (* fails                                                                 *)
  (*************************************************************************) 
  /\ state = "running"
  /\ LET msg == C!FindMessageToClient("sys", "backupGetNewMasterFailed")
         searchManually == msg # C!NOT_MESSAGE
         foundMaster == C!SearchForMaster
     IN /\ msg # C!NOT_MESSAGE
        /\ searchManually
        /\ C!RecvMsg(msg)
        /\ IF foundMaster = C!NOT_MASTER \* no live master found
           THEN /\ state' = "fatal"
                /\ clients' = [ clients EXCEPT ![msg.clientId].phase = C!PH2_COMPLETED_FATAL]
           ELSE /\ state' = state
                   \* at this point, the live master must have been changed
                /\ foundMaster.id # clients[msg.clientId].masterId
                   \* change status to pending to be eligible for restart 
                /\ clients' = [ clients EXCEPT ![msg.clientId].masterId = foundMaster.id,
                                               ![msg.clientId].phase = C!PH1_PENDING]
  /\ UNCHANGED << master, backup, killed >>

C_HandleMasterGetNewBackupFailed ==
  (*************************************************************************)
  (* The client handling the failure of the master when the client asked   *)
  (* the master to return the new backup identity. The failure of the      *)
  (* master is fatal. If a recovered master exists we should not search for*)
  (* it, because it may have the old version before masterDone.            *)
  (*************************************************************************) 
  /\ state = "running"
  /\ LET msg == C!FindMessageToClient("sys", "masterGetNewBackupFailed")
     IN /\ msg # C!NOT_MESSAGE
        /\ state' = "fatal"
        /\ clients' = [ clients EXCEPT ![msg.clientId].phase = C!PH2_COMPLETED_FATAL ]
        /\ C!RecvMsg(msg)
  /\ UNCHANGED << master, backup, killed >>
  
-----------------------------------------------------------------------------------  
C_UpdateBackupId ==
  /\ state = "running"
  /\ LET msg == C!FindMessageToClient("m", "newBackupId")
     IN /\ msg # C!NOT_MESSAGE \* receive new backup identity, and complete request, 
                               \* don't restart, master is alive and up to date
        /\ C!RecvMsg( msg )
        /\ clients' = [ clients EXCEPT ![msg.clientId].backupId = msg.backupId ,
                                       ![msg.clientId].phase = C!PH2_COMPLETED ]
  /\ UNCHANGED << state, master, backup, killed >>
  

C_UpdateMasterIdAndRestart ==
  (*************************************************************************)
  (* Client receiving a new master identify from a live backup and is      *)
  (* preparing to restart                                                  *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET msg == C!FindMessageToClient("b", "newMasterId")
     IN  /\ msg # C!NOT_MESSAGE
         /\ C!RecvMsg( msg )
         /\ clients' = [ clients EXCEPT ![msg.clientId].masterId = msg.masterId,
                                        ![msg.clientId].phase = C!PH1_PENDING ] 
  /\ UNCHANGED << state, master, backup, killed >>
-------------------------------------------------------------------------------
M_DetectBackupLost ==
  (*************************************************************************)
  (* Master detected backup failure and is getting ready to recovery it    *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET activeM == C!FindMaster(C!INST_STATUS_ACTIVE)
         liveB == C!LiveBackup
     IN /\ activeM # C!NOT_MASTER \* master is active
        /\ liveB = C!NOT_BACKUP \* backup is lost
        /\ master' = [ master EXCEPT ![activeM.id].status = C!INST_STATUS_BUSY ] 
  /\ UNCHANGED << state, clients, backup, msgs, killed >>

M_RecoverBackup ==
  (*************************************************************************)
  (* Master creating a new backup using its own state. Master does not     *)
  (* process any client requests during recovery                           *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET busyM == C!FindMaster(C!INST_STATUS_BUSY)
         lostB == C!LastLostBackup
     IN /\ lostB # C!NOT_BACKUP \* a lost backup exists
        /\ busyM # C!NOT_MASTER \* master is busy recovering master
        /\ LET newBackupId == lostB.id + 1
           IN /\ newBackupId <= C!MAX_INSTANCE_ID
              /\ backup' = [ backup EXCEPT ![newBackupId].status = C!INST_STATUS_ACTIVE,
                                             ![newBackupId].masterId = busyM.id,
                                             ![newBackupId].value = busyM.value,
                                             ![newBackupId].version = busyM.version ]
              /\ master' = [ master EXCEPT ![busyM.id].status = C!INST_STATUS_ACTIVE,
                                             ![busyM.id].backupId = newBackupId  ] 
  /\ UNCHANGED << state, clients, msgs, killed >>
  
B_DetectMasterLost ==
  (*************************************************************************)
  (* Backup detected master failure and is getting ready to recover it     *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET liveM == C!SearchForMaster
         activeB == C!FindBackup(C!INST_STATUS_ACTIVE)
     IN /\ liveM = C!NOT_MASTER \* master is not active
        /\ activeB # C!NOT_BACKUP \* backup is active
        /\ backup' = [ backup EXCEPT ![activeB.id].status = C!INST_STATUS_BUSY ] 
  /\ UNCHANGED << state, clients, master, msgs, killed >>

B_RecoverMaster ==
  (*************************************************************************)
  (* Backup creating a new master using its own state. Backup does not     *)
  (* process any client requests during recovery                           *)
  (*************************************************************************)
  /\ state = "running"
  /\ LET lostM == C!LastLostMaster
         busyB == C!FindBackup(C!INST_STATUS_BUSY)
     IN /\ lostM # C!NOT_MASTER \* a lost master exists
        /\ busyB # C!NOT_BACKUP \* backup is busy recovering master
        /\ LET newMasterId == lostM.id + 1
           IN /\ newMasterId <= C!MAX_INSTANCE_ID
              /\ master' = [ master EXCEPT ![newMasterId].status = C!INST_STATUS_ACTIVE,
                                             ![newMasterId].backupId = busyB.id,
                                             ![newMasterId].value = busyB.value,
                                             ![newMasterId].version = busyB.version ]
              /\ backup' = [ backup EXCEPT ![busyB.id].status = C!INST_STATUS_ACTIVE,
                                             ![busyB.id].masterId = newMasterId  ] 
  /\ UNCHANGED << state, clients, msgs, killed >>
----------------------------------------------------------------------------------
TerminateSuccessfully ==
  (*************************************************************************)
  (* TerminateSuccessfully the program if all clients completed their work             *)
  (*************************************************************************)
  /\ state = "running"
     (* wait for all clients to complete updating the master and backup *)
  /\ \A c \in C!CLIENT_ID: clients[c].phase = C!PH2_COMPLETED
  /\ state' = "terminated"
  /\ UNCHANGED << clients, master, backup, msgs, killed >>

Next ==
  \/ KillMaster
  \/ KillBackup
  \/ C_Start
  \/ M_HandleDo
  \/ C_HandleMasterDone
  \/ B_HandleDo
  \/ C_HandleBackupDone
  \/ Sys_NotifyMasterFailure
  \/ Sys_NotifyBackupFailure
  \/ C_HandleMasterDoFailed
  \/ C_HandleBackupDoFailed
  \/ M_HandleGetNewBackup
  \/ B_HandleGetNewMaster
  \/ C_HandleBackupGetNewMasterFailed
  \/ C_HandleMasterGetNewBackupFailed
  \/ C_UpdateBackupId
  \/ C_UpdateMasterIdAndRestart
  \/ M_DetectBackupLost
  \/ M_RecoverBackup
  \/ B_DetectMasterLost
  \/ B_RecoverMaster
  \/ TerminateSuccessfully 
  
Liveness ==
  /\ WF_Vars( KillMaster )
  /\ WF_Vars( KillBackup )
  /\ WF_Vars( C_Start )
  /\ WF_Vars( M_HandleDo )
  /\ WF_Vars( C_HandleMasterDone )
  /\ WF_Vars( B_HandleDo )
  /\ WF_Vars( C_HandleBackupDone )
  /\ WF_Vars( Sys_NotifyMasterFailure )
  /\ WF_Vars( Sys_NotifyBackupFailure )
  /\ WF_Vars( C_HandleMasterDoFailed )
  /\ WF_Vars( C_HandleBackupDoFailed )
  /\ WF_Vars( M_HandleGetNewBackup )
  /\ WF_Vars( B_HandleGetNewMaster )
  /\ WF_Vars( C_HandleBackupGetNewMasterFailed )
  /\ WF_Vars( C_HandleMasterGetNewBackupFailed )
  /\ WF_Vars( C_UpdateBackupId )
  /\ WF_Vars( C_UpdateMasterIdAndRestart )
  /\ WF_Vars( M_DetectBackupLost )
  /\ WF_Vars( M_RecoverBackup )
  /\ WF_Vars( B_DetectMasterLost )
  /\ WF_Vars( B_RecoverMaster )
  /\ WF_Vars( TerminateSuccessfully )

-----------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)          
Spec ==  Init /\ [][Next]_Vars /\ Liveness

THEOREM Spec => []( TypeOK /\ StateOK)
=============================================================================
\* Modification History
\* Last modified Tue Mar 20 15:30:27 AEDT 2018 by u5482878
\* Last modified Sat Mar 17 16:42:36 AEDT 2018 by shamouda
\* Created Mon Mar 05 13:44:57 AEDT 2018 by u5482878
