---------------------------- MODULE AsyncFinishReplication ----------------------------
EXTENDS Integers

CONSTANTS CLIENT_NUM, \* the number of clients                        
          MAX_KILL    \* maximum allowed kill events                  

VARIABLES exec_state, \* the execution state of the program: running, success, or fatal   
          clients,    \* clients sending value update requests to master and backup                            
          master,     \* array of master instances, only one is active 
          backup,     \* array of backup instances, only one is active 
          msgs,       \* in-flight messages                           
          killed      \* number of invoked kill actions to master or backup          

----------------------------------------------------------------------------                                       
Vars == << exec_state, clients, master, backup, msgs, killed >>
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
  /\ exec_state \in { "running", "success", "fatal" }
  /\ msgs \subseteq C!Messages
  /\ killed \in 0..MAX_KILL

----------------------------------------------------------------------------
MaxOneActiveMaster ==
  (*************************************************************************)
  (* Return true if maximum one active master exists, and false otherwise  *)
  (*************************************************************************)
  LET activeM == C!FindMaster(C!INST_STATUS_ACTIVE)
      otherIds == C!INSTANCE_ID \ { activeM.id }
  IN IF activeM = C!NOT_MASTER
     THEN TRUE \* zero active masters
     ELSE LET otherActiveMs == { m \in otherIds : master[m].status = C!INST_STATUS_ACTIVE }
          IN IF otherActiveMs = {} THEN TRUE \* no other active masters
             ELSE FALSE \* other active masters exist

MaxOneActiveBackup ==
  (*************************************************************************)
  (* Return true if maximum one active backup exists, and false otherwise  *)
  (*************************************************************************)
  LET activeB == C!FindBackup(C!INST_STATUS_ACTIVE)
      otherIds == C!INSTANCE_ID \ { activeB.id }
  IN IF activeB = C!NOT_BACKUP
     THEN TRUE \* zero active backups
     ELSE LET otherActiveBs == { b \in otherIds : backup[b].status = C!INST_STATUS_ACTIVE }
          IN IF otherActiveBs = {} THEN TRUE \* no other active backups
             ELSE FALSE \* other active backup exist

StateOK ==
  (*************************************************************************)
  (* State invariants                                                      *)
  (* 1. on successful termination: the final version equals CLIENT_NUM     *)
  (* 2. on fatal termination: there must be a client whose master is lost  *)
  (*   and whose backup is lost or is unknown                              *)
  (* 3. before termination:                                                *)
  (*   a) master version >= backup version                                 *)
  (*   b) master and backup version should not exceed CLIENT_NUM           *)
  (*   c) maximum one active master and maximum one active backup          *)
  (*************************************************************************)
  LET curMaster == C!LastKnownMaster
      curBackup == C!LastKnownBackup
  IN  IF exec_state = "success"
      THEN /\ curMaster.version = CLIENT_NUM 
           /\ curBackup.version = CLIENT_NUM
      ELSE IF exec_state = "fatal"
      THEN \E c \in C!CLIENT_ID : 
              /\ clients[c].phase = C!PH2_COMPLETED_FATAL
              /\ master[clients[c].masterId].status = C!INST_STATUS_LOST
              /\ IF clients[c].backupId # C!UNKNOWN_ID
                 THEN backup[clients[c].backupId].status = C!INST_STATUS_LOST
                 ELSE TRUE
      ELSE /\ curMaster.version >= curBackup.version
           /\ curMaster.version <= CLIENT_NUM 
           /\ curBackup.version <= CLIENT_NUM
           /\ MaxOneActiveMaster
           /\ MaxOneActiveBackup

----------------------------------------------------------------------------   
MustTerminate ==
  (*************************************************************************)
  (* Temporal property: the program must eventually terminate either       *)
  (* successfully or fatally                                               *) 
  (*************************************************************************)
   <> ( exec_state \in { "success", "fatal" } )
----------------------------------------------------------------------------
Init ==
  (*************************************************************************)
  (* Initialize variables                                                  *)
  (*************************************************************************)
  /\ exec_state = "running"
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
E_KillingMaster ==
  (*************************************************************************)
  (* Kill the active master instance.                                      *)
  (*************************************************************************)
  /\ exec_state = "running"
  /\ killed < MAX_KILL
  /\ LET activeM == C!FindMaster(C!INST_STATUS_ACTIVE)
     IN /\ activeM # C!NOT_MASTER
        /\ master' = [ master EXCEPT ![activeM.id].status = C!INST_STATUS_LOST ]
        /\ killed' = killed + 1
  /\ UNCHANGED << exec_state, clients, backup, msgs >>

E_KillingBackup ==
  (*************************************************************************)
  (* Kill the active backup instance.                                      *)
  (*************************************************************************)
  /\ exec_state = "running"
  /\ killed < MAX_KILL
  /\ LET activeB == C!FindBackup(C!INST_STATUS_ACTIVE)
     IN /\ activeB # C!NOT_BACKUP
        /\ backup' = [ backup EXCEPT ![activeB.id].status = C!INST_STATUS_LOST ]
        /\ killed' = killed + 1
  /\ UNCHANGED << exec_state, clients, master, msgs >>

C_Starting ==
  (*************************************************************************)
  (* Client start the replication process by sending "do" to master        *)
  (*************************************************************************)
  /\ exec_state = "running"
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
  /\ UNCHANGED << exec_state, master, backup, killed >>

M_Doing ==
  (*************************************************************************)
  (* Master receiving "do", updating value, and sending "done"             *)
  (*************************************************************************)
  /\ exec_state = "running"
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
  /\ UNCHANGED << exec_state, clients, backup, killed >>

C_HandlingMasterDone ==
  (*************************************************************************)
  (* Client receiving "done" from master, and forwarding action to backup  *)
  (*************************************************************************) 
  /\ exec_state = "running"
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
  /\ UNCHANGED << exec_state, master, backup, killed >>

B_Doing == 
  (*************************************************************************)
  (* Backup receiving "do", updating value, then sending "done"            *)
  (*************************************************************************)
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToWithTag("b", C!INST_STATUS_ACTIVE, "backupDo")
     IN /\ msg # C!NOT_MESSAGE
           (* Master info is consistent between client and backup *)
        /\ msg.masterId = backup[msg.backupId].masterId
        /\ backup' = [ backup EXCEPT ![msg.backupId].value = backup[msg.backupId].value + msg.value,
                                     ![msg.backupId].version = backup[msg.backupId].version + 1 ]
        /\ C!ReplaceMsg( msg, [ from |-> "b",
                              to |-> "c",
                              clientId |-> msg.clientId,
                              masterId |-> msg.masterId,
                              backupId |-> msg.backupId,
                              value |-> 0,
                              tag |-> "backupDone" ] )
  /\ UNCHANGED << exec_state, clients, master, killed >>

B_DetectingOldMasterId == 
  (*************************************************************************)
  (* Backup receiving "do" and detecting that the client is using an old   *)
  (* master id. It does not update the value, and it sends the new master  *)
  (* id to the client                                                      *)
  (*************************************************************************)
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToWithTag("b", C!INST_STATUS_ACTIVE, "backupDo")
     IN /\ msg # C!NOT_MESSAGE
           (* Master has changed, client must restart *)
        /\ msg.masterId # backup[msg.backupId].masterId
        /\ C!ReplaceMsg( msg, [ from |-> "b",
                              to |-> "c",
                              clientId |-> msg.clientId,
                              masterId |-> backup[msg.backupId].masterId,
                              backupId |-> msg.backupId,
                              value |-> 0,
                              tag |-> "newMasterId" ] )
  /\ UNCHANGED << exec_state, clients, master, backup, killed >>

C_HandlingBackupDone ==
  (*************************************************************************)
  (* Client receiving "done" from backup. Replication completed            *)
  (*************************************************************************) 
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToClient("b", "backupDone")
     IN /\ msg # C!NOT_MESSAGE
        /\ C!RecvMsg( msg )
        /\ clients' = [ clients EXCEPT ![msg.clientId].phase = C!PH2_COMPLETED ]
                      \* if all clients completed, then terminate the execution successfully
        /\ IF \A c \in C!CLIENT_ID: clients'[c].phase = C!PH2_COMPLETED
           THEN exec_state' = "success"
           ELSE exec_state' = exec_state
  /\ UNCHANGED << master, backup, killed >>

--------------------------------------------------------------------------------
C_HandlingMasterDoFailed ==
  (*************************************************************************)
  (* Client received the system's notification of a dead master, and       *)
  (* is requesting the backup to return the new master info                *)
  (*************************************************************************) 
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToWithTag("m", C!INST_STATUS_LOST, "masterDo") 
         knownBackup == IF msg # C!NOT_MESSAGE 
                        THEN C!FindBackup(C!INST_STATUS_ACTIVE)
                        ELSE C!NOT_BACKUP
     IN /\ msg # C!NOT_MESSAGE
        /\ IF knownBackup = C!NOT_BACKUP
           THEN /\ C!RecvMsg (msg)
                /\ exec_state' = "fatal"
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
                /\ exec_state' = exec_state
                /\ clients' = clients
  /\ UNCHANGED << master, backup, killed >>

C_HandlingBackupDoFailed ==
  (*************************************************************************)
  (* Client received the system's notification of a dead backup, and       *)
  (* is requesting the master to return the new backup info                *)
  (*************************************************************************) 
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToWithTag("b", C!INST_STATUS_LOST, "backupDo") 
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
  /\ UNCHANGED << exec_state, clients, master, backup, killed >>

----------------------------------------------------------------------------------
M_GettingNewBackup == 
  (*************************************************************************)
  (* Master responding to client with updated backup identity              *)
  (*************************************************************************)
  /\ exec_state = "running"
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
  /\ UNCHANGED << exec_state, clients, master, backup, killed >>
  
B_GettingNewMaster == 
  (*************************************************************************)
  (* Backup responding to client with updated master identity              *)
  (*************************************************************************)
  /\ exec_state = "running"
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
  /\ UNCHANGED << exec_state, clients, master, backup, killed >>

-----------------------------------------------------------------------------------
C_HandlingBackupGetNewMasterFailed ==
  (*************************************************************************)
  (* The client handling the failure of the backup, when the client asked  *)
  (* the backup to return the new master identity. The client mannually    *)
  (* searches for the master.                                              *)
  (* If manual search does not find a master, a fatal error occurs.        *)
  (* Otherwise, the client updates it's masterId and eventually restarts.  *)
  (* Restarting is safe because this action is reached only if "masterDo"  *)
  (* fails                                                                 *)
  (*************************************************************************) 
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToWithTag("b", C!INST_STATUS_LOST, "backupGetNewMaster")
         foundMaster == C!FindMaster(C!INST_STATUS_ACTIVE)
     IN /\ msg # C!NOT_MESSAGE
        /\ C!RecvMsg(msg)
        /\ IF foundMaster = C!NOT_MASTER \* no live master found
           THEN /\ exec_state' = "fatal"
                /\ clients' = [ clients EXCEPT ![msg.clientId].phase = C!PH2_COMPLETED_FATAL ]
           ELSE /\ exec_state' = exec_state
                   \* at this point, the live master must have been changed
                /\ foundMaster.id # clients[msg.clientId].masterId
                   \* change status to pending to be eligible for restart 
                /\ clients' = [ clients EXCEPT ![msg.clientId].masterId = foundMaster.id,
                                               ![msg.clientId].phase = C!PH1_PENDING ]
  /\ UNCHANGED << master, backup, killed >>

C_HandlingMasterGetNewBackupFailed ==
  (*************************************************************************)
  (* The client handling the failure of the master when the client asked   *)
  (* the master to return the new backup identity. The failure of the      *)
  (* master is fatal. If a recovered master exists we should not search for*)
  (* it, because it may have the old version before masterDone.            *)
  (*************************************************************************) 
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToWithTag("m", C!INST_STATUS_LOST, "masterGetNewBackup") 
     IN /\ msg # C!NOT_MESSAGE
        /\ exec_state' = "fatal"
        /\ clients' = [ clients EXCEPT ![msg.clientId].phase = C!PH2_COMPLETED_FATAL ]
        /\ C!RecvMsg(msg)
  /\ UNCHANGED << master, backup, killed >>
  
-----------------------------------------------------------------------------------  
C_UpdatingBackupId ==
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToClient("m", "newBackupId")
     IN /\ msg # C!NOT_MESSAGE \* receive new backup identity, and complete request, 
                               \* don't restart, master is alive and up to date
        /\ C!RecvMsg( msg )
        /\ clients' = [ clients EXCEPT ![msg.clientId].backupId = msg.backupId ,
                                       ![msg.clientId].phase = C!PH2_COMPLETED ]
           \* if all clients completed, then terminate the execution successfully
        /\ IF \A c \in C!CLIENT_ID: clients'[c].phase = C!PH2_COMPLETED
           THEN exec_state' = "success"
           ELSE exec_state' = exec_state
  /\ UNCHANGED << master, backup, killed >>

C_UpdatingMasterId ==
  (*************************************************************************)
  (* Client receiving a new master identify from a live backup and is      *)
  (* preparing to restart by changing its phase to pending                 *)
  (*************************************************************************)
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToClient("b", "newMasterId")
     IN  /\ msg # C!NOT_MESSAGE
         /\ C!RecvMsg( msg )
         /\ clients' = [ clients EXCEPT ![msg.clientId].masterId = msg.masterId,
                                        ![msg.clientId].phase = C!PH1_PENDING ] 
  /\ UNCHANGED << exec_state, master, backup, killed >>
-------------------------------------------------------------------------------
M_CreatingNewBackup ==
  (*************************************************************************)
  (* Master creating a new backup using its own exec_state. Master does not     *)
  (* process any client requests during recovery                           *)
  (*************************************************************************)
  /\ exec_state = "running"
  /\ LET activeM == C!FindMaster(C!INST_STATUS_ACTIVE)
         activeB == C!FindBackup(C!INST_STATUS_ACTIVE)
         lostB == C!LastLostBackup
     IN /\ activeM # C!NOT_MASTER \* active master exists
        /\ activeB = C!NOT_BACKUP \* active backup does not exist
        /\ lostB # C!NOT_BACKUP \* a lost backup exists
        /\ LET newBackupId == lostB.id + 1 \* new backup id is the following id of the dead backup
           IN /\ newBackupId <= C!MAX_INSTANCE_ID
              /\ backup' = [ backup EXCEPT ![newBackupId].status = C!INST_STATUS_ACTIVE,
                                           ![newBackupId].masterId = activeM.id,
                                           ![newBackupId].value = activeM.value,
                                           ![newBackupId].version = activeM.version ]
              /\ master' = [ master EXCEPT ![activeM.id].backupId = newBackupId  ] 
  /\ UNCHANGED << exec_state, clients, msgs, killed >>
  
B_CreatingNewMaster ==
  (*************************************************************************)
  (* Backup creating a new master using its own exec_state. Backup does not     *)
  (* process any client requests during recovery                           *)
  (*************************************************************************)
  /\ exec_state = "running"
  /\ LET activeM == C!FindMaster(C!INST_STATUS_ACTIVE)
         activeB == C!FindBackup(C!INST_STATUS_ACTIVE)
         lostM == C!LastLostMaster
     IN /\ activeM = C!NOT_MASTER \* active master does not exist
        /\ activeB # C!NOT_BACKUP \* active backup exists
        /\ lostM # C!NOT_MASTER \* a lost master exists
        /\ LET newMasterId == lostM.id + 1
           IN /\ newMasterId <= C!MAX_INSTANCE_ID
              /\ master' = [ master EXCEPT ![newMasterId].status = C!INST_STATUS_ACTIVE,
                                             ![newMasterId].backupId = activeB.id,
                                             ![newMasterId].value = activeB.value,
                                             ![newMasterId].version = activeB.version ]
              /\ backup' = [ backup EXCEPT ![activeB.id].masterId = newMasterId  ] 
  /\ UNCHANGED << exec_state, clients, msgs, killed >>

Next ==
  \/ E_KillingMaster
  \/ E_KillingBackup
  \/ C_Starting
  \/ M_Doing
  \/ C_HandlingMasterDone
  \/ B_Doing
  \/ B_DetectingOldMasterId
  \/ C_HandlingBackupDone
  \/ C_HandlingMasterDoFailed
  \/ C_HandlingBackupDoFailed
  \/ M_GettingNewBackup
  \/ B_GettingNewMaster
  \/ C_HandlingBackupGetNewMasterFailed
  \/ C_HandlingMasterGetNewBackupFailed
  \/ C_UpdatingBackupId
  \/ C_UpdatingMasterId
  \/ M_CreatingNewBackup
  \/ B_CreatingNewMaster
  
Liveness ==
  /\ WF_Vars( E_KillingMaster )
  /\ WF_Vars( E_KillingBackup )
  /\ WF_Vars( C_Starting )
  /\ WF_Vars( M_Doing )
  /\ WF_Vars( C_HandlingMasterDone )
  /\ WF_Vars( B_Doing )
  /\ WF_Vars( B_DetectingOldMasterId )
  /\ WF_Vars( C_HandlingBackupDone )
  /\ WF_Vars( C_HandlingMasterDoFailed )
  /\ WF_Vars( C_HandlingBackupDoFailed )
  /\ WF_Vars( M_GettingNewBackup )
  /\ WF_Vars( B_GettingNewMaster )
  /\ WF_Vars( C_HandlingBackupGetNewMasterFailed )
  /\ WF_Vars( C_HandlingMasterGetNewBackupFailed )
  /\ WF_Vars( C_UpdatingBackupId )
  /\ WF_Vars( C_UpdatingMasterId )
  /\ WF_Vars( M_CreatingNewBackup )
  /\ WF_Vars( B_CreatingNewMaster )

-----------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)          
Spec ==  Init /\ [][Next]_Vars /\ Liveness

THEOREM Spec => []( TypeOK /\ StateOK)
=============================================================================
