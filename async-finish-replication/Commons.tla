---------------------------- MODULE Commons --------------------------------
EXTENDS Integers
CONSTANTS CLIENT_NUM,     \* the number of clients                        
          MAX_KILL        \* maximum allowed kill events                  

VARIABLES exec_state,     \* the execution state of the program: running, terminated, or fatal   
          clients,        \* clients sending value update requests to master and backup                            
          master,         \* pool of master instances, only one is active 
          backup,         \* pool of backup instances, only one is active 
          msgs,           \* in-flight messages                           
          killed          \* number of invoked kill actions to master or backup          
----------------------------------------------------------------------------
(* Identifiers related to master and backup instance ids *)
FIRST_ID == 1
MAX_INSTANCE_ID == MAX_KILL+1
INSTANCE_ID == FIRST_ID..MAX_INSTANCE_ID
UNKNOWN_ID == 0
NOT_INSTANCE_ID == -1

(* Identifiers related to master and backup instance statuses *)
INST_STATUS_NULL == "null"   \* null, not used yet
INST_STATUS_ACTIVE == "active" \* active and handling client requests
INST_STATUS_LOST == "lost"   \* lost
INST_STATUS_BUSY == "busy"   \* busy recoverying the other replica
NOT_STATUS == "invalid"        \* invalid status
INSTANCE_STATUS == { INST_STATUS_NULL, 
                     INST_STATUS_ACTIVE, 
                     INST_STATUS_LOST,
                     INST_STATUS_BUSY }

LiveStatus == { INST_STATUS_ACTIVE, INST_STATUS_BUSY }

(* Master instance record structure *)
Master == [ id:INSTANCE_ID, backupId:INSTANCE_ID \cup {UNKNOWN_ID}, 
            status:INSTANCE_STATUS, value:Nat, version:Nat ]

(* Invalid master instance *)
NOT_MASTER == [ id |-> NOT_INSTANCE_ID, backupId |-> NOT_INSTANCE_ID, 
                status |-> NOT_STATUS, value |-> -1, version |-> -1 ]

(* Backup instance record structure *)
Backup == [ id:INSTANCE_ID, masterId:INSTANCE_ID \cup {UNKNOWN_ID}, 
            status:INSTANCE_STATUS, value:Nat, version:Nat ]

(* Invalid backup instance *)
NOT_BACKUP == [ id |-> NOT_INSTANCE_ID, masterId |-> NOT_INSTANCE_ID, 
                status |-> NOT_STATUS, value |-> -1, version |-> -1 ]

SearchForMaster ==
  (*************************************************************************)
  (* Return the live master, or NOT_MASTER if master is lost               *)
  (*************************************************************************)
  LET mset == { m \in INSTANCE_ID : master[m].status \in LiveStatus }
  IN IF mset = {} THEN NOT_MASTER
     ELSE master[(CHOOSE x \in mset : TRUE)]

LastLostMaster ==
  (*************************************************************************)
  (* Return the lost master, or NOT_MASTER if master is alive              *)
  (*************************************************************************)
  LET mset == { m \in INSTANCE_ID : master[m].status = INST_STATUS_LOST }
  IN IF mset = {} THEN NOT_MASTER
     ELSE master[(CHOOSE n \in mset : \A m \in mset : n \geq m)]

FindMaster(mStatus) == 
  (*************************************************************************)
  (* Return the master with given status or NOT_MASTER otherwise           *)
  (*************************************************************************)
  LET mset == { m \in INSTANCE_ID : master[m].status = mStatus }
  IN IF mset = {} THEN NOT_MASTER
     ELSE master[(CHOOSE x \in mset : TRUE)]

LastKnownMaster ==
  (*************************************************************************)
  (* Return the last known master, whether active, busy or lost            *)
  (*************************************************************************)
  LET mset == { m \in INSTANCE_ID : master[m].status # INST_STATUS_NULL }
  IN master[(CHOOSE n \in mset : \A m \in mset : n \geq m)]
  
LiveBackup ==
  (*************************************************************************)
  (* Return the active back, or NOT_BACKUP if backup is lost or busy       *)
  (*************************************************************************)
  LET bset == { b \in INSTANCE_ID : backup[b].status \in LiveStatus }
  IN IF bset = {} THEN NOT_BACKUP
     ELSE backup[(CHOOSE x \in bset : TRUE)]

FindBackup(bStatus) == 
  (*************************************************************************)
  (* Return the backup with given status or NOT_BACKUP otherwise           *)
  (*************************************************************************)
  LET bset == { b \in INSTANCE_ID : backup[b].status = bStatus }
  IN IF bset = {} THEN NOT_BACKUP
     ELSE backup[(CHOOSE x \in bset : TRUE)]

LastLostBackup ==
  (*************************************************************************)
  (* Return the lost backup, or NOT_BACKUP if backup is alive              *)
  (*************************************************************************)
  LET bset == { b \in INSTANCE_ID : backup[b].status = INST_STATUS_LOST }
  IN IF bset = {} THEN NOT_BACKUP
     ELSE backup[(CHOOSE n \in bset : \A m \in bset : n \geq m)]

SearchForBackup ==
  (*************************************************************************)
  (* Return the live backup, or NOT_BACKUP if backup is lost               *)
  (*************************************************************************)
  LET bset == { b \in INSTANCE_ID : backup[b].status \in LiveStatus }
  IN IF bset = {} THEN NOT_BACKUP
     ELSE backup[(CHOOSE x \in bset : TRUE)]
     
LastKnownBackup ==
  (*************************************************************************)
  (* Return the last known backup, whether active, busy or lost            *)
  (*************************************************************************)
  LET bset == { m \in INSTANCE_ID : backup[m].status # INST_STATUS_NULL }
  IN backup[(CHOOSE n \in bset : \A m \in bset : n \geq m)]

----------------------------------------------------------------------------
(* Identifiers related to client ids and phases *)
CLIENT_ID == 1..CLIENT_NUM
NOT_CLIENT_ID == -1

\*client phases
CLIENT_PHASE == 1..4
PH1_PENDING == 1
PH2_WORKING == 2
PH2_COMPLETED == 3
PH2_COMPLETED_FATAL == 4
NOT_CLIENT_PHASE == -1

(* Client record structure *)
Client == [ id:CLIENT_ID, phase:CLIENT_PHASE, value:Nat, 
            masterId:INSTANCE_ID, \* the master instance last communicated with 
            backupId:INSTANCE_ID \cup {UNKNOWN_ID} \* the backup instance last communicated with, initially unknown
          ]

(* Invalid client instance *)
NOT_CLIENT == [ id |-> NOT_CLIENT_ID, phase |-> NOT_CLIENT_PHASE, value |-> 0 ]

FindClient(phase) ==
  (*************************************************************************)
  (* Return a client matching the given phase, or NOT_CLIENT otherwise     *)
  (*************************************************************************)
  LET cset == { c \in CLIENT_ID : clients[c].phase = phase }
  IN IF cset = {} THEN NOT_CLIENT
     ELSE clients[(CHOOSE x \in cset : TRUE)]

----------------------------------------------------------------------------
(* Message record structure *)
Messages == [ from:{"c","m","b","sys"}, to:{"c","m","b"},
              clientId:CLIENT_ID,
              masterId:INSTANCE_ID \cup {UNKNOWN_ID},
              backupId:INSTANCE_ID \cup {UNKNOWN_ID},
              value:Nat,
              tag:{ "masterDo", "backupDo",   
                    "masterDone", "backupDone", 
                    "masterDoFailed", "backupDoFailed",
                    "masterGetNewBackup", "backupGetNewMaster",
                    "newBackupId", "newMasterId",
                    "backupGetNewMasterFailed", "masterGetNewBackupFailed"  
                  } ]

(* Invalid message instance *)
NOT_MESSAGE == [ from |-> "na", to |-> "na" ]

SendMsg(m) == 
  (*************************************************************************)
  (* Add message to the msgs set                                           *)
  (*************************************************************************)
  msgs' = msgs \cup {m}

RecvMsg(m) ==
  (*************************************************************************)
  (* Delete message from the msgs set                                      *)
  (*************************************************************************) 
  msgs' = msgs \ {m}

ReplaceMsg(toRemove, toAdd) ==
  (*************************************************************************)
  (* Remove an existing message and add another one                        *)
  (*************************************************************************) 
  msgs' =  (msgs \ {toRemove}) \cup {toAdd}

FindMessageToWithTag(to, status, optionalTag) ==
  (*************************************************************************)
  (* Return a message matching the given criteria, or NOT_MESSAGE otherwise*)
  (*************************************************************************) 
  LET mset == { m \in msgs : /\ m.to = to
                             /\ IF to = "m" 
                                THEN master[m.masterId].status = status
                                ELSE IF to = "b"
                                THEN backup[m.backupId].status = status
                                ELSE FALSE
                             /\ IF optionalTag = "NA"
                                THEN TRUE
                                ELSE m.tag = optionalTag}
  IN IF mset = {} THEN NOT_MESSAGE
     ELSE ( CHOOSE x \in mset : TRUE ) 

FindMessageTo(to, status) == FindMessageToWithTag(to, status, "NA")

FindMessageToClient(from, tag) ==
  (*************************************************************************)
  (* Return a message sent to client matching given criteria,              *)
  (* or NOT_MESSAGE otherwise                                              *)
  (*************************************************************************) 
  LET mset == { m \in msgs : /\ m.from = from
                             /\ m.to = "c"
                             /\ m.tag = tag }
  IN IF mset = {} THEN NOT_MESSAGE
     ELSE ( CHOOSE x \in mset : TRUE ) 

=============================================================================
\* Modification History
\* Last modified Wed Mar 21 00:40:31 AEDT 2018 by shamouda
\* Last modified Tue Mar 20 15:30:59 AEDT 2018 by u5482878
\* Created Mon Mar 05 13:44:57 AEDT 2018 by u5482878
