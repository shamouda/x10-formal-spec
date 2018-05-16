---------------------------- MODULE OptimisticCommons --------------------------------
(* Constants and common utility actions                                             *)
EXTENDS Integers

CONSTANTS LEVEL,
          WIDTH,
          NUM_PLACES,
          MAX_KILL

VARIABLES exec_state,
          tasks,
          f_set,
          lf_set,
          rf_set,
          msgs,
          nxt_finish_id,
          nxt_task_id,
          nxt_remote_place,
          killed,
          rec_child,
          rec_to,
          rec_from,
          rec_from_waiting
          
---------------------------------------------------------------------------------------

FIRST_PLACE_ID == 0
PlaceID == FIRST_PLACE_ID..(NUM_PLACES-1)
NOT_PLACE_ID == -1

ROOT_FINISH_ID == 0
MAX_FINISH_ID == ( ( 1 - (WIDTH)^(LEVEL+1) ) \div (1-WIDTH) ) \*the power series
NOT_FINISH_ID == -1
FinishID == ROOT_FINISH_ID..MAX_FINISH_ID

ROOT_TASK_ID == 0
MAX_TASK_ID == MAX_FINISH_ID
NOT_TASK_ID == -1
TaskID == ROOT_TASK_ID..MAX_TASK_ID

BranchID == 0..WIDTH
LevelID == 0..LEVEL

TASK_STATUS == { "waitingForPublish", "waitingForTransit", "sent", "dropped", "running", "blocked", "terminated" }

TASK_TYPE == { "normal", (* terminates at any time *)
               "finishMainTask" (*terminates after finish creates all its branches*) 
             }

FINISH_STATUS == { "active", "waitingForPublish", "waitingForRelease", "released" }   

Task   == [ id:TaskID, 
            pred_id:TaskID \cup {NOT_TASK_ID}, \*predecessor task, used for debugging only
            src:PlaceID, dst:PlaceID, 
            finish_id:FinishID, 
            level:LevelID,
            last_branch:BranchID, 
            status:TASK_STATUS,
            type:TASK_TYPE,
            finish_type:{"global", "local", "N/A"} ]

RootTask == [ id |-> ROOT_TASK_ID, 
              pred_id |-> NOT_TASK_ID,
              src |-> FIRST_PLACE_ID,
              dst |-> FIRST_PLACE_ID,  
              finish_id |-> ROOT_FINISH_ID, 
              level |-> 0,
              last_branch |-> WIDTH, 
              status |-> "blocked",
              type |-> "normal",
              finish_type |-> "global" ]

NOT_TASK == [ id |-> NOT_TASK_ID, 
              src |-> NOT_PLACE_ID,
              dst |-> NOT_PLACE_ID,
              level |-> -1,
              finish_id |-> NOT_FINISH_ID,
              finish_type |-> "N/A" ]


Place1D == [ PlaceID -> Nat ]
Place2D == [ PlaceID -> [ PlaceID -> Nat ] ]

Place1DZeros == [ i \in PlaceID |-> 0 ]
Place2DZeros == [ i \in PlaceID |-> [ j \in PlaceID |-> 0 ] ]

Place1DTerminateTask(src, cnt) == [ i \in PlaceID |-> IF i = src THEN cnt ELSE 0 ]

Place2DInitResilientFinish(home) == [ i \in PlaceID |-> [ j \in PlaceID |-> IF i = home /\ j = home THEN 1 ELSE 0 ] ]

Finish == [ id:FinishID \ {ROOT_FINISH_ID},
            pred_id:TaskID \cup {NOT_TASK_ID}, \*predecessor task
            home:PlaceID,
            origin:PlaceID,
            parent_finish_id:FinishID,
            status:FINISH_STATUS,
            lc:Nat ]

RootFinish == [ id |-> ROOT_FINISH_ID + 1, 
                pred_id |-> RootTask.id, 
                home |-> FIRST_PLACE_ID, 
                origin |-> FIRST_PLACE_ID, 
                parent_finish_id |-> ROOT_FINISH_ID, 
                status |-> "active", 
                lc |-> 1 ]

RootFinishTask == [ id |-> ROOT_TASK_ID + 1, 
                    pred_id |-> ROOT_TASK_ID, 
                    dst |-> FIRST_PLACE_ID, 
                    src |-> FIRST_PLACE_ID, 
                    finish_id |-> RootFinish.id, 
                    status |-> "running", 
                    level |-> 1, 
                    last_branch |-> 0, 
                    type |-> "finishMainTask",
                    finish_type |-> "global" ]

NOT_FINISH == [ id |-> NOT_FINISH_ID,
                home |-> NOT_PLACE_ID,
                origin |-> NOT_PLACE_ID,
                parent_finish_id |-> NOT_FINISH_ID,
                status |-> "",
                lc |-> 0]
            
LFinish == [ id:FinishID \ {ROOT_FINISH_ID},
             home:PlaceID,
             lc:Nat,
             reported:Place1D,
             received:Place1D, 
             deny:Place1D ]
             
RFinish == [ id:FinishID \ {ROOT_FINISH_ID},
             home:PlaceID,
             origin:PlaceID,
             parent_finish_id:FinishID,
             transOrLive:Place2D,
             sent:Place2D,
             gc:Nat,
             ghost_children:SUBSET FinishID,
             isAdopted:BOOLEAN ]

Message == [ from:{"f","rf","src","dst","lf"},
             to:{"f","rf","src","dst","lf"},
             tag:{ "transit", "transitDone", "transitNotDone",
                   "terminateTask", "terminateGhost",
                   "task", 
                   "publish", "publishDone", 
                   "release",
                   "countDropped", "countDroppedDone" },
             src:PlaceID,
             dst:PlaceID,
             finish_id:FinishID,
             ghost_finish_id:FinishID,
             task_id:TaskID,
             term_tasks_by_src:Place1D, \* termination only
             term_tasks_dst:PlaceID,  \* termination only
             num_sent:Nat,
             num_dropped:Nat
           ]

NOT_MESSAGE == [ from |-> "N/A", to |-> "N/A" , tag |-> "N/A",
                 src |-> NOT_PLACE_ID, dst |-> NOT_PLACE_ID,
                 finish_id |-> NOT_FINISH_ID,
                 task_id |-> NOT_TASK_ID,
                 ghost_finish_id |-> NOT_FINISH_ID,
                 term_tasks_by_src |-> Place1DZeros,
                 term_tasks_dst |-> NOT_PLACE_ID ]

FindRunningTask(maxLevel) ==
  LET tset == { task \in tasks : /\ task.status = "running"
                                 /\ task.last_branch < WIDTH
                                 /\ task.level <= maxLevel }
  IN IF tset = {} THEN NOT_TASK
     ELSE CHOOSE t \in tset : TRUE
     
FindRunningTaskWithFinishType(maxLevel, fin_type) ==
  LET tset == { task \in tasks : /\ task.status = "running"
                                 /\ task.last_branch < WIDTH
                                 /\ task.level <= maxLevel
                                 /\ task.finish_type = fin_type }
  IN IF tset = {} THEN NOT_TASK
     ELSE CHOOSE t \in tset : TRUE

FindFinishById(id) ==
   CHOOSE f \in f_set : f.id = id

FindResilientFinishById(id) ==
   CHOOSE f \in rf_set : f.id = id

FindTaskById(id) ==
   CHOOSE t \in tasks : t.id = id

ActiveFinishSet == { "active", "waitingForRelease" }
       
FindActiveFinish(id, home) ==
  LET fset == { finish \in f_set : /\ finish.status \in ActiveFinishSet
                                   /\ finish.id = id
                                   /\ \/ /\ home # NOT_PLACE_ID
                                         /\ finish.home = home
                                      \/ /\ home = NOT_PLACE_ID }
  IN IF fset = {} THEN NOT_FINISH
     ELSE CHOOSE f \in fset : TRUE

FindPendingRemoteTask(finish_id, status) == 
  LET tset == { task \in tasks : /\ task.status = status
                                 /\ task.src # task.dst
                                 /\ task.finish_type = "local"
                                 /\ task.finish_id = finish_id
              }
  IN IF tset = {} THEN NOT_TASK
     ELSE CHOOSE t \in tset : TRUE
          
IsPublished(finish_id) ==
  \E rf \in rf_set : /\ rf.id = finish_id
                     /\ \E f \in f_set : /\ f.id = finish_id
                                         /\ f.status \in ActiveFinishSet
LocalFinishExists(place, finish_id) ==
  \E lf \in lf_set : /\ lf.id = finish_id
                     /\ lf.home = place
                     
ResilientFinishExists(finish_id) ==
  \E rf \in rf_set : rf.id = finish_id  
  
FindLocalFinish(place, finish_id) ==
  CHOOSE f \in lf_set : f.home = place /\ f.id = finish_id

FindFinishToRelease(finish_id) ==
  CHOOSE f \in f_set : f.id = finish_id /\ f.status = "waitingForRelease" /\ f.lc = 0

\* a task can terminate if cannot branch further - at last level or at last branch number
FindTaskToTerminate(fin_type) == 
  LET tset == { task \in tasks : /\ task.status = "running"
                                 /\ task.finish_type = fin_type
                                 /\ \/ task.level = LEVEL
                                    \/ task.last_branch = WIDTH
                                 /\ IF fin_type = "global"
                                    THEN FindActiveFinish(task.finish_id, task.src) # NOT_FINISH
                                    ELSE TRUE
              }
  IN IF tset = {} THEN NOT_TASK
     ELSE CHOOSE t \in tset : TRUE

FindBlockedTask(task_id) == 
  LET tset == { task \in tasks : /\ task.status = "blocked"
                                 /\ task.id = task_id
              }
  IN IF tset = {} THEN NOT_TASK
     ELSE CHOOSE t \in tset : TRUE
     
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

FindMessageToActivePlaceWithTag(to, tag) ==
  (*************************************************************************)
  (* Return a message matching the given criteria, or NOT_MESSAGE otherwise*)
  (*************************************************************************) 
  LET mset == { m \in msgs : /\ m.to = to
                             /\ m.tag = tag
                             /\ IF m.to = "rf"
                                THEN TRUE
                                ELSE m.dst \notin killed }
  IN IF mset = {} THEN NOT_MESSAGE
     ELSE ( CHOOSE x \in mset : TRUE ) 
     
Sum(place1D) ==
   IF NUM_PLACES = 0 THEN 0
   ELSE IF NUM_PLACES = 1 THEN place1D[0]
   ELSE IF NUM_PLACES = 2 THEN place1D[0] +  place1D[1]
   ELSE IF NUM_PLACES = 3 THEN place1D[0] +  place1D[1] + place1D[2] 
   ELSE IF NUM_PLACES = 4 THEN place1D[0] +  place1D[1] + place1D[2] + place1D[3]
   ELSE IF NUM_PLACES = 5 THEN place1D[0] +  place1D[1] + place1D[2] + place1D[3] + place1D[4]
   ELSE IF NUM_PLACES = 6 THEN place1D[0] +  place1D[1] + place1D[2] + place1D[3] + place1D[4] + place1D[5]
   ELSE -1

NextRemotePlace(here) ==
  IF nxt_remote_place[here] = here
  THEN ( nxt_remote_place[here] + 1 ) % NUM_PLACES
  ELSE nxt_remote_place[here]

ShiftNextRemotePlace(here) ==
  IF nxt_remote_place[here] = here
  THEN nxt_remote_place' = [ nxt_remote_place EXCEPT ![here] = (nxt_remote_place[here] + 2) % NUM_PLACES ]
  ELSE nxt_remote_place' = [ nxt_remote_place EXCEPT ![here] = (nxt_remote_place[here] + 1) % NUM_PLACES ]
-------------------------------------------------------------------------------
FindLostTasks(dead) == 
  { 
     task \in tasks : \/ /\ task.status \in { "waitingForPublish", "waitingForTransit" }
                         /\ task.src = dead
                      \/ /\ task.status \in { "running", "blocked" } 
                         /\ task.dst = dead 
  }

FindLostFinishes(dead) ==
  { 
    finish \in f_set : /\ finish.status # "released"
                       /\ finish.home = dead
  }     

FindLostLocalFinishes(dead) == 
  {
    local_fin \in lf_set : /\ local_fin.home = dead
  }

FindImpactedResilientFinish(victim) ==
{ 
  id \in FinishID : \E rf \in rf_set : /\ rf.id = id
                                       /\ \/ \E i \in PlaceID : rf.transOrLive[i][victim] > 0
                                          \/ \E j \in PlaceID : rf.transOrLive[victim][j] > 0 
}

FindImpactedResilientFinishToDead(victim) ==
{ 
  id \in FinishID : \E rf \in rf_set : /\ rf.id = id
                                       /\ \E i \in PlaceID : rf.transOrLive[i][victim] > 0
}

FindImpactedResilientFinishFromDead(victim) ==
{ 
  id \in FinishID : \E rf \in rf_set : /\ rf.id = id
                                       /\ \E j \in PlaceID : rf.transOrLive[victim][j] > 0 
}

GetSrc(rf) ==
  CHOOSE i \in PlaceID : CHOOSE j \in killed : rf.transOrLive[i][j] > 0

GetDst(rf, src) ==
  CHOOSE j \in killed : rf.transOrLive[src][j] > 0
  
GetAdoptedGhostChildren(fin_id) ==
 { 
   id \in FinishID : \E rf \in rf_set : /\ rf.id = id 
                                        /\ rf.home \in killed
                                        /\ rf.parent_finish_id = fin_id
                                        /\ rf.isAdopted = TRUE
 }

GetNonAdoptedGhostChildren(fin_id) ==
 { 
   id \in FinishID : \E rf \in rf_set : /\ rf.id = id 
                                        /\ rf.home \in killed
                                        /\ rf.parent_finish_id = fin_id
                                        /\ rf.isAdopted = FALSE
 }

IsRecoveringTasksToDeadPlaces(fin_id) == 
  \/ \E task \in rec_child : task.finish_id = fin_id
  \/ \E task \in rec_to    : task.finish_id = fin_id

ConvTask == [ finish_id:FinishID, from:PlaceID, to:PlaceID ]

GetChildrenTask == [ finish_id:FinishID, victim:PlaceID, markingDone:BOOLEAN ]

NOT_REQUEST == [ finish_id |-> NOT_FINISH_ID ]
     
ChildRequestExists(fin_id) ==
  \E creq \in rec_child : fin_id = creq.finish_id

ToRequestExists(fin_id) ==
  \E treq \in rec_to : fin_id = treq.finish_id

FindMarkGhostChildrenRequest ==
  LET rset == { r \in rec_child : r.markingDone = FALSE }
  IN IF rset = {} THEN NOT_REQUEST
     ELSE ( CHOOSE x \in rset : TRUE ) 
 
FindAddGhostChildrenRequest ==
  LET rset == { r \in rec_child : r.markingDone = TRUE }
  IN IF rset = {} THEN NOT_REQUEST
     ELSE ( CHOOSE x \in rset : TRUE ) 

ChooseGhost(ghosts) ==
  IF ghosts = {} THEN NOT_FINISH ELSE CHOOSE x \in rf_set : x.id \in ghosts
  
FindToDeadRequest ==
  IF rec_to = {} THEN NOT_REQUEST
  ELSE IF \E a \in rec_to : ~ ChildRequestExists (a.finish_id)
       THEN ( CHOOSE b \in rec_to : ~ ChildRequestExists (b.finish_id) )
       ELSE NOT_REQUEST

FindFromDeadRequest ==
  IF rec_from = {} THEN NOT_REQUEST
  ELSE IF \E a \in rec_from : /\ ~ ChildRequestExists (a.finish_id)
                              /\ ~ ToRequestExists(a.finish_id)
       THEN ( CHOOSE b \in rec_from : /\ ~ ChildRequestExists (b.finish_id)
                                      /\ ~ ToRequestExists(b.finish_id) )
       ELSE NOT_REQUEST
       
FindFromDeadWaitingRequest(fin_id, from, to) ==
  CHOOSE x \in rec_from_waiting : /\ x.finish_id = fin_id
                                  /\ x.from = from
                                  /\ x.to = to

ApplyTerminateSignal(rf, rf_updated, msg) == 
  IF rf_updated.gc = 0 /\ rf_updated.ghost_children = {}
  THEN IF rf.isAdopted
       THEN /\ ReplaceMsg(msg, [ from |-> "rf", to |-> "rf", tag |-> "terminateGhost",
                                   finish_id |-> rf.parent_finish_id,
                                   ghost_finish_id |-> rf.id,
                                   dst |-> NOT_PLACE_ID ]) \* rf.id is enough
            /\ rf_set' = rf_set \ { rf } 
       ELSE /\ ReplaceMsg(msg, [ from |-> "rf", to |-> "f", tag |-> "release",
                                   finish_id |-> rf.id,
                                   dst |-> rf.home ]) 
            /\ rf_set' = rf_set \ { rf }
  ELSE /\ RecvMsg(msg)
       /\ rf_set' = ( rf_set \ {rf} ) \cup { rf_updated } 

ApplyTerminateSignal2(rf, rf_updated) == 
  IF rf_updated.gc = 0 /\ rf_updated.ghost_children = {}
  THEN IF rf.isAdopted
       THEN /\ SendMsg([ from |-> "rf", to |-> "rf", tag |-> "terminateGhost",
                           finish_id |-> rf.parent_finish_id,
                           ghost_finish_id |-> rf.id,
                           dst |-> NOT_PLACE_ID ]) \* rf.id is enough
            /\ rf_set' = rf_set \ { rf }
       ELSE /\ SendMsg([ from |-> "rf", to |-> "f", tag |-> "release",
                           finish_id |-> rf.id,
                           dst |-> rf.home ])
            /\ rf_set' = rf_set \ { rf }
  ELSE /\ msgs' = msgs
       /\ rf_set' = ( rf_set \ {rf} ) \cup { rf_updated } 
       
RecvTerminateSignal(msg) ==
  /\ RecvMsg(msg)
  /\ rf_set' = rf_set

RecvCountDroppedResponse(msg) == 
   /\ RecvMsg(msg)
   /\ rf_set' = rf_set 
=============================================================================
