----------------------------- MODULE Optimistic -----------------------------
EXTENDS Integers

CONSTANTS LEVEL,
          WIDTH,
          NUM_PLACES,
          MAX_KILL,
          KILL_FROM,
          KILL_TO

VARIABLES exec_state, \* execution state
          tasks,      \* set of tasks
          f_set,      \* finish objects
          lf_set,     \* local finish objects
          rf_set,     \* resilient finish objects
          msgs,       \* msgs
          nxt_finish_id, \* sequence to create unique finish ids
          nxt_task_id,    \* sequence to create unique task ids
          nxt_remote_place,
          killed,
          killed_cnt,
          rec_child,
          rec_to,
          rec_from,
          rec_from_waiting,
          lost_tasks,
          lost_f_set,
          lost_lf_set,
          step

\* TODO: we need to publish the parent if not published
\* send multiple publish messages for parent - grand parent - grand grand parent
\* the store needs to do them in order from top to buttom

Vars == << exec_state, tasks, f_set, lf_set, rf_set, msgs, 
           nxt_finish_id, nxt_task_id, nxt_remote_place,
           killed, killed_cnt,
           lost_tasks, lost_f_set, lost_lf_set,
           rec_child, rec_to, rec_from, rec_from_waiting, step >>
           
----------------------------------------------------------------------------
C == INSTANCE OptimisticCommons
----------------------------------------------------------------------------
TypeOK ==
  (*************************************************************************)
  (* Variables type constrains                                             *)
  (*************************************************************************)
  /\ exec_state \in { "running", "success" }
  /\ tasks \subseteq C!Task
  /\ f_set \subseteq C!Finish
  /\ lf_set \subseteq C!LFinish
  /\ rf_set \subseteq C!RFinish
  /\ nxt_finish_id \in C!FinishID
  /\ nxt_task_id \in C!TaskID
  /\ nxt_remote_place \in C!Place1D
  /\ killed \subseteq C!PlaceID
  /\ killed_cnt \in 0..(NUM_PLACES-1)
  /\ rec_child \subseteq C!GetChildrenTask
  /\ rec_to \subseteq C!ConvTask
  /\ rec_from \subseteq C!ConvTask
  /\ rec_from_waiting \subseteq C!ConvTask
  /\ step \in Nat
   
StateOK == 
  (*************************************************************************)
  (* State invariants:                                                     *)
  (* - every finish that sent a remote task must have a remote finish      *)
  (* - for every local finish at P, the received[X] <= rf.sent[fhome][P]   *)
  (* - upon successful termination, all tasks are either terminated or lost*)
  (*************************************************************************)
  /\ TRUE

----------------------------------------------------------------------------   
MustTerminate ==
  (*************************************************************************)
  (* Temporal property: the program must eventually terminate successfully *)
  (*************************************************************************)
   <> ( exec_state = "success" )
   
----------------------------------------------------------------------------   
Init == 
  (*************************************************************************)
  (* Initialize variables                                                  *)
  (*************************************************************************)
  /\ exec_state = "running"
  /\ tasks = { C!RootTask, C!RootFinishTask }
  /\ f_set = { C!RootFinish }
  /\ lf_set = {}
  /\ rf_set = {}
  /\ msgs = {}
  /\ nxt_finish_id = 2
  /\ nxt_task_id = 2
  /\ nxt_remote_place = [ i \in C!PlaceID |-> i ]
  /\ killed = {}
  /\ killed_cnt = 0
  /\ lost_tasks = {}
  /\ lost_f_set = {}
  /\ lost_lf_set = {}
  /\ rec_child = {}
  /\ rec_to = {}
  /\ rec_from = {}
  /\ rec_from_waiting = {}
  /\ step = 0

NewFinish(task) ==
[ id |-> nxt_finish_id,
  pred_id |-> task.id,
  home |-> task.dst,
  origin |-> task.src,
  parent_finish_id |-> task.finish_id,
  status |-> "active",
  lc |-> 1 \* the main finish task 
] 

NewResilientFinish(finish) ==
[ id |-> finish.id,
  home |-> finish.home,
  origin |-> finish.origin,
  parent_finish_id |-> finish.parent_finish_id,
  transOrLive |-> C!Place2DInitResilientFinish(finish.home),
  sent |-> C!Place2DInitResilientFinish(finish.home),
  gc |-> 1,
  ghost_children |-> {},
  isAdopted |-> FALSE ]

NewLocalFinish(fid, dst) ==
[ id |-> fid,
  home |-> dst,
  lc |-> 0 ,
  reported |-> C!Place1DZeros,
  received |-> C!Place1DZeros, 
  deny |-> C!Place1DZeros ]

NewTask(pred, fid, s, d, t , l, st, fin_type) ==
[ id |-> nxt_task_id, 
  pred_id |-> pred,
  src |-> s, 
  dst |-> d, 
  finish_id |-> fid , 
  level |-> l,
  last_branch |-> 0, 
  status |-> st,
  type |-> t,
  finish_type |-> fin_type ]
                           
---------------------------------------------------------------------------- 
CreatingFinish == 
  /\ exec_state = "running"
  /\ LET task == C!FindRunningTask(LEVEL-1)
         task_updated == IF task = C!NOT_TASK THEN C!NOT_TASK
                         ELSE [ task EXCEPT !.last_branch = task.last_branch+1,
                                            !.status = "blocked" ]
         finish == IF task # C!NOT_TASK 
                      THEN NewFinish(task) 
                      ELSE C!NOT_FINISH
         finish_task == IF task # C!NOT_TASK 
                    THEN NewTask(task.id, finish.id, task.dst, task.dst, 
                                 "finishMainTask", task.level + 1, "running", "global")
                    ELSE C!NOT_TASK
     IN /\ task # C!NOT_TASK
        /\ nxt_finish_id' = nxt_finish_id + 1
        /\ nxt_task_id' = nxt_task_id + 1
        /\ f_set' = f_set \cup { finish }
        /\ tasks' = (tasks \ {task} ) \cup { task_updated, finish_task }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, lf_set, rf_set, msgs, 
                  nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

Finish_ForkingLocalTask ==  \* fork local task by global finish
  /\ exec_state = "running"
  /\ LET task == C!FindRunningTaskWithFinishType(LEVEL-1, "global")
         task_updated == IF task = C!NOT_TASK THEN C!NOT_TASK
                         ELSE [ task EXCEPT !.last_branch = task.last_branch+1 ]
         src == task.dst
         dst == task.dst
         new_task == IF task = C!NOT_TASK THEN C!NOT_TASK
                     ELSE NewTask(task.id, task.finish_id, task.dst, task.dst, "normal", task.level + 1, "running", task.finish_type)
         finish == IF task = C!NOT_TASK THEN C!NOT_FINISH
                   ELSE C!FindFinishById(task.finish_id)
         finish_updated == IF task = C!NOT_TASK THEN C!NOT_FINISH
                           ELSE [finish EXCEPT !.lc = finish.lc + 1 ]          
     IN /\ task # C!NOT_TASK
        /\ finish # C!NOT_FINISH
        /\ nxt_task_id' = nxt_task_id + 1
        /\ f_set' = ( f_set \ {finish} ) \cup { finish_updated }
        /\ tasks' = (tasks \ {task} ) \cup { task_updated, new_task }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, lf_set, rf_set, msgs, 
                  nxt_finish_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>
      
LocalFinish_ForkingLocalTask ==  \* create local task with status created and put it in the set
  /\ exec_state = "running"
  /\ LET task == C!FindRunningTaskWithFinishType(LEVEL-1, "local")
         task_updated == IF task = C!NOT_TASK THEN C!NOT_TASK
                         ELSE [ task EXCEPT !.last_branch = task.last_branch+1 ]
         src == task.dst
         finish_id == task.finish_id
         new_task == IF task = C!NOT_TASK THEN C!NOT_TASK
                     ELSE NewTask(task.id, task.finish_id, src, src, "normal", task.level + 1, "running", task.finish_type)
         lfinish == IF task = C!NOT_TASK THEN C!NOT_FINISH
                    ELSE C!FindLocalFinish(src, finish_id)
         lfinish_updated == [ lfinish EXCEPT !.received[src] = lfinish.received[src] + 1,
                                             !.lc = lfinish.lc + 1 ]
     IN /\ task # C!NOT_TASK
        /\ nxt_task_id' = nxt_task_id + 1
        /\ lf_set' = ( lf_set \ { lfinish } ) \cup { lfinish_updated }
        /\ tasks' = (tasks \ { task } ) \cup { task_updated, new_task }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, f_set, rf_set, msgs, 
                  nxt_finish_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>
                  
Finish_CreatingRemoteTask ==  \* create task with status created and put it in the set
  /\ exec_state = "running"
  /\ LET task == C!FindRunningTaskWithFinishType(LEVEL-1, "global")
         task_updated == IF task = C!NOT_TASK THEN C!NOT_TASK
                         ELSE [ task EXCEPT !.last_branch = task.last_branch+1,
                                            !.status = "blocked" ]
         finish == IF task = C!NOT_TASK THEN C!NOT_FINISH
                   ELSE C!FindFinishById(task.finish_id)
         new_finish_status == IF C!IsPublished(task.finish_id) 
                              THEN finish.status
                              ELSE "waitingForPublish"
         finish_updated == IF task = C!NOT_TASK THEN C!NOT_FINISH
                          ELSE [ finish EXCEPT !.status = new_finish_status ]
         src == task.dst
         dst == C!NextRemotePlace(src)
         new_task_status == IF C!IsPublished(task.finish_id) 
                            THEN "waitingForTransit"
                            ELSE "waitingForPublish"
         new_task == IF task = C!NOT_TASK THEN C!NOT_TASK
                     ELSE NewTask(task.id, task.finish_id, src, dst, "normal", task.level + 1, new_task_status, "local")
         msg_transit == [ from |-> "src", to |-> "rf", tag |-> "transit",
                          src |-> new_task.src, dst |-> new_task.dst,
                          finish_id |-> new_task.finish_id,
                          task_id |-> new_task.id ]
         msg_publish == [ from |-> "f", to |-> "rf", tag |-> "publish", 
                         src |-> finish.home,
                         finish_id |-> finish.id ]
     IN /\ task # C!NOT_TASK
        /\ finish.status = "active"
        /\ nxt_task_id' = nxt_task_id + 1
        /\ tasks' = (tasks \ {task} ) \cup { task_updated, new_task }
        /\ f_set' = (f_set \ { finish } ) \cup { finish_updated }
        /\ C!ShiftNextRemotePlace(src)
        /\ IF C!IsPublished(task.finish_id) 
           THEN C!SendMsg(msg_transit)
           ELSE C!SendMsg(msg_publish)
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, lf_set, rf_set, 
                  nxt_finish_id,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

Finish_ReceivingPublishDoneSignal ==
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("f", "publishDone")
         finish == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
                   ELSE C!FindFinishById(msg.finish_id)
         finish_updated == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
                           ELSE [ finish EXCEPT !.status = "active" ]
         pending_task == C!FindPendingRemoteTask(finish.id, "waitingForPublish")
         pending_task_updated == IF msg = C!NOT_MESSAGE THEN C!NOT_TASK
                                 ELSE [ pending_task EXCEPT !.status = "waitingForTransit" ]
         msg_transit == [ from |-> "src", to |-> "rf", tag |-> "transit",
                          src |-> pending_task.src, dst |-> pending_task.dst,
                          finish_id |-> pending_task.finish_id,
                          task_id |-> pending_task.id ]
     IN /\ msg # C!NOT_MESSAGE
        /\ C!ReplaceMsg (msg, msg_transit)
        /\ f_set' = (f_set \ { finish } ) \cup { finish_updated }
        /\ tasks' = (tasks \ {pending_task} ) \cup { pending_task_updated } 
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, lf_set, rf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

Finish_TerminatingTask ==
  /\ exec_state = "running"
  /\ LET task == C!FindTaskToTerminate("global")
         finish == IF task = C!NOT_TASK THEN C!NOT_FINISH
                   ELSE C!FindFinishById(task.finish_id)
         task_updated == IF task # C!NOT_TASK
                         THEN [ task EXCEPT !.status = "terminated" ]
                         ELSE C!NOT_TASK
         finish_updated == IF task = C!NOT_TASK THEN C!NOT_FINISH
                           ELSE IF finish.lc = 1 /\ C!IsPublished(finish.id)
                           THEN [ finish EXCEPT !.lc = finish.lc - 1,
                                                !.status = "waitingForRelease" ]
                           ELSE IF finish.lc = 1 /\ ~ C!IsPublished(finish.id)
                           THEN [ finish EXCEPT !.lc = finish.lc - 1,
                                                !.status = "released" ]
                           ELSE [ finish EXCEPT !.lc = finish.lc - 1 ]
     IN /\ task # C!NOT_TASK
        /\ finish # C!NOT_FINISH
        /\ f_set' = ( f_set \ {finish} ) \cup { finish_updated }
        /\ IF finish_updated.status = "waitingForRelease"
           THEN msgs' = msgs \cup {[ from |-> "f", to |-> "rf", tag |-> "terminateTask", 
                                    src |-> finish.home,
                                    finish_id |-> finish.id,
                                    task_id |-> task.id,
                                    term_tasks_by_src |-> C!Place1DTerminateTask(finish.home, 1), 
                                    term_tasks_dst |-> finish.home ]}
           ELSE msgs' = msgs
        /\ IF finish_updated.status = "released"
           THEN LET task_blocked == C!FindBlockedTask(finish.pred_id)
                    task_unblocked == [ task_blocked EXCEPT !.status = "running" ]
                IN tasks' = ( tasks \ { task, task_blocked } ) \cup { task_updated, task_unblocked }
           ELSE tasks' = ( tasks \ {task} ) \cup { task_updated }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, lf_set, rf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

Finish_ReceivingReleaseSignal == 
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("f", "release")
         finish == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
                   ELSE C!FindFinishToRelease(msg.finish_id)
         finish_updated == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
                           ELSE [ finish EXCEPT !.status = "released" ]
         task_blocked == IF msg = C!NOT_MESSAGE THEN C!NOT_TASK
                         ELSE C!FindBlockedTask(finish.pred_id)
         task_unblocked == IF msg = C!NOT_MESSAGE THEN C!NOT_TASK
                           ELSE [ task_blocked EXCEPT !.status = "running" ]
     IN /\ msg # C!NOT_MESSAGE
        /\ C!RecvMsg ( msg )
        /\ f_set' = ( f_set \ { finish } ) \cup { finish_updated }
        /\ tasks' = ( tasks \ { task_blocked } ) \cup { task_unblocked }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, lf_set, rf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

----------------------------------------------------------------------
DroppingTask ==
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("src", "transitNotDone")
         task == IF msg = C!NOT_MESSAGE THEN C!NOT_TASK
                 ELSE C!FindTaskById(msg.task_id)
         task_updated == IF task = C!NOT_TASK THEN C!NOT_TASK
                         ELSE [ task EXCEPT !.status = "dropped" ]
         blocked_task == C!FindTaskById(task.pred_id)
         blocked_task_updated == [ blocked_task EXCEPT !.status = "running" ]
     IN /\ msg # C!NOT_MESSAGE
        /\ task.status = "waitingForTransit"
        /\ blocked_task.status = "blocked"
        /\ tasks' = ( tasks \ {task, blocked_task } ) \cup { task_updated, blocked_task_updated }
        /\ C!RecvMsg(msg)
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, f_set, lf_set, rf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>
                   
SendingTask ==
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("src", "transitDone")
         task == IF msg = C!NOT_MESSAGE THEN C!NOT_TASK
                 ELSE C!FindTaskById(msg.task_id)
         task_updated == IF task = C!NOT_TASK THEN C!NOT_TASK
                         ELSE [ task EXCEPT !.status = "sent" ]
         blocked_task == C!FindTaskById(task.pred_id)
         blocked_task_updated == [ blocked_task EXCEPT !.status = "running" ]
     IN /\ msg # C!NOT_MESSAGE
        /\ task.status = "waitingForTransit"
        /\ blocked_task.status = "blocked"
        /\ tasks' = ( tasks \ {task, blocked_task } ) \cup { task_updated, blocked_task_updated }
        /\ C!ReplaceMsg(msg, [ from |-> "src", to |-> "dst", tag |-> "task",
                               src |-> task.src, dst |-> task.dst,
                               finish_id |-> task.finish_id,
                               task_id |-> task.id ])
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, f_set, lf_set, rf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

ReceivingTask == 
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("dst", "task")
         src == msg.src
         dst == msg.dst
         finish_id == msg.finish_id
         lfinish == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
                    ELSE IF C!LocalFinishExists(dst, finish_id) THEN C!FindLocalFinish(dst, finish_id)
                    ELSE NewLocalFinish(finish_id, dst)
         lfinish_updated == [ lfinish EXCEPT !.received[src] = lfinish.received[src] + 1,
                                             !.lc = lfinish.lc + 1 ]
         task == IF msg = C!NOT_MESSAGE THEN C!NOT_TASK
                 ELSE C!FindTaskById(msg.task_id)
         task_updated == IF task = C!NOT_TASK THEN C!NOT_TASK
                         ELSE [ task EXCEPT !.status = "running" ]
     IN /\ msg # C!NOT_MESSAGE
        /\ C!RecvMsg(msg)
        /\ IF lfinish.deny[src] = 1
           THEN /\ lf_set' = lf_set
                /\ tasks' = tasks
           ELSE /\ lf_set' = ( lf_set \ { lfinish } ) \cup { lfinish_updated }
                /\ tasks' = ( tasks \ {task} ) \cup { task_updated }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, f_set, rf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

-------------------------------------------------------------------------------------- 
LocalFinish_CreatingRemoteTask ==  \* create task with status created and put it in the set
  /\ exec_state = "running"
  /\ LET task == C!FindRunningTaskWithFinishType(LEVEL-1, "local")
         task_updated == IF task = C!NOT_TASK THEN C!NOT_TASK
                         ELSE [ task EXCEPT !.last_branch = task.last_branch+1,
                                            !.status = "blocked" ]
         finish == IF task = C!NOT_TASK THEN C!NOT_FINISH
                   ELSE C!FindFinishById(task.finish_id)
         src == task.dst
         dst == C!NextRemotePlace(src)
         new_task == IF task = C!NOT_TASK THEN C!NOT_TASK
                     ELSE NewTask(task.id, task.finish_id, src, dst, "normal", task.level + 1, "waitingForTransit", "local")
         msg_transit == [ from |-> "src", to |-> "rf", tag |-> "transit",
                          src |-> new_task.src, dst |-> new_task.dst,
                          finish_id |-> new_task.finish_id,
                          task_id |-> new_task.id ]
     IN /\ task # C!NOT_TASK
        /\ nxt_task_id' = nxt_task_id + 1
        /\ tasks' = (tasks \ {task} ) \cup { task_updated, new_task }
        /\ C!ShiftNextRemotePlace(src)
        /\ C!SendMsg(msg_transit)
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, f_set, lf_set, rf_set, 
                  nxt_finish_id,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

LocalFinish_TerminatingTask ==
  /\ exec_state = "running"
  /\ LET task == C!FindTaskToTerminate("local")
         task_updated == IF task = C!NOT_TASK THEN C!NOT_TASK
                         ELSE [ task EXCEPT !.status = "terminated" ]
         here == task.dst
         finish_id == task.finish_id
         lfinish == IF task = C!NOT_TASK THEN C!NOT_FINISH
                    ELSE C!FindLocalFinish(here, finish_id)
         lfinish_updated == IF task = C!NOT_TASK THEN C!NOT_FINISH
                            ELSE [ lfinish EXCEPT !.lc = lfinish.lc - 1 ]
         term_tasks == IF task = C!NOT_TASK THEN C!NOT_FINISH
                             ELSE [ i \in C!PlaceID |-> IF i = lfinish.home THEN 0 
                                                        ELSE lfinish.received[i] - lfinish.reported[i]  ]
         lfinish_terminated == IF task = C!NOT_TASK THEN C!NOT_FINISH
                               ELSE [ lfinish EXCEPT !.lc = 0, 
                                                     !.reported = lfinish.received ]
     IN /\ task # C!NOT_TASK
        /\ lfinish # C!NOT_FINISH
        /\ IF lfinish_updated.lc = 0
           THEN /\ msgs' = msgs \cup {[ from |-> "f", to |-> "rf", tag |-> "terminateTask", 
                                    src |-> here,
                                    finish_id |-> finish_id,
                                    task_id |-> task.id,
                                    term_tasks_by_src |-> term_tasks, 
                                    term_tasks_dst |-> here ]}
                /\ lf_set' = ( lf_set \ {lfinish} ) \cup { lfinish_terminated }
           ELSE /\ msgs' = msgs
                /\ lf_set' = ( lf_set \ {lfinish} ) \cup { lfinish_updated }
        /\ tasks' = ( tasks \ {task} ) \cup { task_updated }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, f_set, rf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

LocalFinish_CountingDroppedTasksFromDeadPlace == 
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("dst", "countDropped")
         finish_id == msg.finish_id
         here == msg.dst
         dead == msg.src
         lfinish == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
                    ELSE IF C!LocalFinishExists(here, finish_id) THEN C!FindLocalFinish(here, finish_id)
                    ELSE NewLocalFinish(finish_id, here)
         lfinish_updated == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
                            ELSE [ lfinish EXCEPT !.deny[dead] = 1 ]
         resp == IF msg = C!NOT_MESSAGE THEN C!NOT_MESSAGE
                 ELSE [ from |-> "dst", to |-> "rf", tag |-> "countDroppedDone",
                        finish_id |-> msg.finish_id,
                        src |-> msg.src, dst |-> msg.dst,
                        num_dropped |-> msg.num_sent - lfinish.received[dead] ]
     IN /\ msg # C!NOT_MESSAGE
        /\ C!ReplaceMsg(msg, resp)
        /\ lf_set' = ( lf_set \ { lfinish } ) \cup { lfinish_updated }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, rf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>
  
----------------------------------------------------------------------------
Store_ReceivingPublishSignal ==
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("rf", "publish")
         finish_home == msg.src
         finish == IF msg = C!NOT_MESSAGE \/ finish_home \in killed 
                   THEN C!NOT_FINISH
                   ELSE C!FindFinishById(msg.finish_id)
     IN /\ msg # C!NOT_MESSAGE
        /\ IF finish_home \notin killed
           THEN /\ C!ReplaceMsg ( msg,  [ from |-> "rf", to |-> "f", tag |-> "publishDone", 
                                  dst |-> msg.src,
                                  finish_id |-> msg.finish_id ] )
                /\ rf_set' = rf_set \cup { NewResilientFinish(finish) }
           ELSE /\ C!RecvMsg ( msg )
                /\ rf_set' = rf_set 
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, lf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

Store_ReceivingTransitSignal ==
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("rf", "transit")
         rf == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
               ELSE C!FindResilientFinishById(msg.finish_id)
         s == msg.src
         d == msg.dst
         rf_updated == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
                       ELSE [rf EXCEPT !.sent[s][d] = rf.sent[s][d] + 1,
                                       !.transOrLive[s][d] = rf.transOrLive[s][d] + 1,
                                       !.gc = rf.gc + 1 ]
         msg_tag == IF s \in killed \/ d \in killed THEN "transitNotDone" ELSE "transitDone"
     IN /\ msg # C!NOT_MESSAGE
        /\ ~ C!IsRecoveringTasksToDeadPlaces(rf.id)
        /\ IF s \in killed \/ d \in killed
           THEN rf_set' = rf_set
           ELSE rf_set' = ( rf_set \ {rf} ) \cup {rf_updated}
        /\ C!ReplaceMsg(msg, [ from |-> "rf", to |-> "src", tag |-> msg_tag,
                               dst |-> s,
                               finish_id |-> msg.finish_id,
                               task_id |-> msg.task_id ])
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, lf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>
 
ApplyTerminateSignal(rf, rf_updated, msg) == 
  IF rf_updated.gc = 0 /\ rf_updated.ghost_children = {}
  THEN IF rf.isAdopted
       THEN /\ C!ReplaceMsg(msg, [ from |-> "rf", to |-> "rf", tag |-> "terminateGhost",
                                   finish_id |-> rf.parent_finish_id,
                                   ghost_finish_id |-> rf.id,
                                   dst |-> C!NOT_PLACE_ID ]) \* rf.id is enough
            /\ rf_set' = rf_set \ { rf } 
       ELSE /\ C!ReplaceMsg(msg, [ from |-> "rf", to |-> "f", tag |-> "release",
                                   finish_id |-> rf.id,
                                   dst |-> rf.home ]) 
            /\ rf_set' = rf_set \ { rf }
  ELSE /\ C!RecvMsg(msg)
       /\ rf_set' = ( rf_set \ {rf} ) \cup { rf_updated } 

ApplyTerminateSignal2(rf, rf_updated) == 
  IF rf_updated.gc = 0 /\ rf_updated.ghost_children = {}
  THEN IF rf.isAdopted
       THEN /\ C!SendMsg([ from |-> "rf", to |-> "rf", tag |-> "terminateGhost",
                           finish_id |-> rf.parent_finish_id,
                           ghost_finish_id |-> rf.id,
                           dst |-> C!NOT_PLACE_ID ]) \* rf.id is enough
            /\ rf_set' = rf_set \ { rf }
       ELSE /\ C!SendMsg([ from |-> "rf", to |-> "f", tag |-> "release",
                           finish_id |-> rf.id,
                           dst |-> rf.home ])
            /\ rf_set' = rf_set \ { rf }
  ELSE /\ msgs' = msgs
       /\ rf_set' = ( rf_set \ {rf} ) \cup { rf_updated } 
       
DropTerminateSignal(msg) ==
  /\ C!RecvMsg(msg)
  /\ rf_set' = rf_set
                                  
Store_ReceivingTerminateTaskSignal ==
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("rf", "terminateTask")
         term_tasks == msg.term_tasks_by_src
         dst == msg.term_tasks_dst
         rf == IF msg = C!NOT_MESSAGE \/ dst \in killed THEN C!NOT_FINISH
               ELSE C!FindResilientFinishById(msg.finish_id)
         trans_live_updated == [ i \in C!PlaceID |-> [ j \in C!PlaceID |-> 
                                 IF j = dst THEN rf.transOrLive[i][j] - term_tasks[i] 
                                 ELSE rf.transOrLive[i][j] 
                               ] ]
         total == C!Sum(term_tasks)
         rf_updated == IF msg = C!NOT_MESSAGE \/ dst \in killed THEN C!NOT_FINISH
                       ELSE [rf EXCEPT !.transOrLive = trans_live_updated,
                                       !.gc = rf.gc - total ]
     IN /\ msg # C!NOT_MESSAGE
        /\ total # -1 \* see C!Sum() definition
        /\ IF dst \notin killed
           THEN /\ ~ C!IsRecoveringTasksToDeadPlaces(rf.id)
                /\ ApplyTerminateSignal(rf, rf_updated, msg)
           ELSE DropTerminateSignal(msg)
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, lf_set,
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

Store_ReceivingTerminateGhostSignal == 
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("rf", "terminateGhost")
         rf == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
               ELSE C!FindResilientFinishById(msg.finish_id)
         ghost_child == msg.ghost_finish_id
         rf_updated == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
                       ELSE [rf EXCEPT !.ghost_children = rf.ghost_children \ { ghost_child } ]
     IN /\ msg # C!NOT_MESSAGE
        /\ ~ C!IsRecoveringTasksToDeadPlaces(rf.id)
        /\ ApplyTerminateSignal(rf, rf_updated, msg)
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, lf_set,
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>

Store_MarkingGhostChildrenAsAdopted ==
  /\ exec_state = "running"
  /\ LET req == C!FindMarkGhostChildrenRequest
         rf == IF req = C!NOT_REQUEST THEN C!NOT_FINISH
               ELSE C!FindResilientFinishById(req.finish_id)
         ghosts == IF req = C!NOT_REQUEST THEN {} 
                   ELSE C!GetNonAdoptedGhostChildren(rf.id)
         grf == C!ChooseGhost(ghosts)
         grf_updated == IF grf = C!NOT_FINISH THEN C!NOT_FINISH
                         ELSE [ grf EXCEPT !.isAdopted = TRUE ]
         req_updated == IF req = C!NOT_REQUEST THEN C!NOT_REQUEST
                       ELSE [ req EXCEPT !.markingDone = TRUE ]
     IN /\ req # C!NOT_REQUEST
        /\ rf # C!NOT_FINISH
        /\ IF ghosts = {}
           THEN /\ rf_set' = rf_set 
                /\ rec_child' = ( rec_child \ { req } ) \cup { req_updated }
           ELSE /\ rf_set' = ( rf_set \ { grf } ) \cup { grf_updated }
                /\ rec_child' = rec_child
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, lf_set, msgs, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_to, rec_from, rec_from_waiting >>
  
Store_AddingGhostChildren ==
  /\ exec_state = "running"
  /\ LET req == C!FindAddGhostChildrenRequest
         rf == IF req = C!NOT_REQUEST THEN C!NOT_FINISH
               ELSE C!FindResilientFinishById(req.finish_id)
         ghosts == C!GetAdoptedGhostChildren(rf.id)
         rf_updated == IF req = C!NOT_REQUEST THEN C!NOT_FINISH
                       ELSE [ rf EXCEPT !.ghost_children = rf.ghost_children \cup ghosts ]
     IN /\ req # C!NOT_REQUEST
        /\ rf # C!NOT_FINISH
        /\ rf_set' = ( rf_set \ { rf } ) \cup { rf_updated }
        /\ rec_child' = rec_child \ { req }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, lf_set, msgs, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_to, rec_from, rec_from_waiting >>

Store_CancellingTasksToDeadPlace ==
  /\ exec_state = "running"
  /\ LET req == C!FindToDeadRequest
         rf == IF req = C!NOT_REQUEST THEN C!NOT_FINISH
               ELSE C!FindResilientFinishById(req.finish_id)
         rf_updated == IF req = C!NOT_REQUEST THEN C!NOT_FINISH
                       ELSE [ rf EXCEPT !.transOrLive[req.from][req.to] = 0,
                                        !.gc = rf.gc - rf.transOrLive[req.from][req.to] ]
     IN /\ req # C!NOT_REQUEST
        /\ rf # C!NOT_FINISH
        /\ ApplyTerminateSignal2(rf, rf_updated)
        /\ rec_to' = rec_to \ { req }
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, lf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_from, rec_from_waiting >>

Store_SendingCountDroppedSignalToLocalFinish ==
  /\ exec_state = "running"
  /\ LET req == C!FindFromDeadRequest
         rf == IF req = C!NOT_REQUEST THEN C!NOT_FINISH
               ELSE IF ~ C!ResilientFinishExists(req.finish_id) THEN C!NOT_FINISH
               ELSE C!FindResilientFinishById(req.finish_id)
         msg == IF req = C!NOT_REQUEST THEN C!NOT_MESSAGE
                ELSE  [ from |-> "rf" , to |-> "dst", tag |-> "countDropped",
                        finish_id |-> rf.id, 
                        src |-> req.from, dst |-> req.to,
                        num_sent |-> rf.sent[req.from][req.to] ]
     IN /\ req # C!NOT_REQUEST
        /\ rec_from' = rec_from \ { req }
        /\ IF rf # C!NOT_FINISH
           THEN /\ C!SendMsg ( msg )
                /\ rec_from_waiting' = rec_from_waiting \cup { req }
           ELSE /\ msgs' = msgs \* resilient finish has been released already
                /\ rec_from_waiting' = rec_from_waiting
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, lf_set, rf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to >>

IgnoreCountDroppedResponse(msg) == 
   /\ C!RecvMsg(msg)
   /\ rf_set' = rf_set 
  
Store_CancellingDroppedTasksFromDeadPlace ==
  /\ exec_state = "running"
  /\ LET msg == C!FindMessageToActivePlaceWithTag("rf", "countDroppedDone")
         from == msg.src
         to == msg.dst
         finish_id == msg.finish_id
         req == IF msg = C!NOT_MESSAGE THEN C!NOT_REQUEST
                ELSE C!FindFromDeadWaitingRequest(finish_id, from, to)
         rf == IF msg = C!NOT_MESSAGE THEN C!NOT_FINISH
               ELSE IF ~ C!ResilientFinishExists(req.finish_id) THEN C!NOT_FINISH
               ELSE C!FindResilientFinishById(finish_id)
         rf_updated == IF rf = C!NOT_FINISH THEN C!NOT_FINISH
                       ELSE [ rf EXCEPT !.transOrLive[from][to] = rf.transOrLive[from][to] - msg.num_dropped,
                                        !.gc = rf.gc - msg.num_dropped ]
     IN /\ msg # C!NOT_MESSAGE
        /\ rec_from_waiting' = rec_from_waiting \ { req }
        /\ IF msg.num_dropped > 0
           THEN ApplyTerminateSignal(rf, rf_updated, msg)
           ELSE IgnoreCountDroppedResponse(msg)
        /\ step' = step + 1
  /\ UNCHANGED << exec_state, tasks, f_set, lf_set, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from >> 
                  
---------------------------------------------------------------------------- 
KillingPlace ==
  /\ exec_state = "running"
  /\ killed_cnt < MAX_KILL
  /\ LET victim == CHOOSE x \in ( C!PlaceID \ killed  ) : x # 0
         victim_tasks == C!FindLostTasks(victim)
         victim_finishes == C!FindLostFinishes(victim)
         victim_local_finishes == C!FindLostLocalFinishes(victim)
         rf_to == C!FindImpactedResilientFinishToDead(victim)
         rf_from == C!FindImpactedResilientFinishFromDead(victim)
     IN /\ step >= KILL_FROM
        /\ step < KILL_TO
        /\ killed' = killed \cup { victim }
        /\ killed_cnt' = killed_cnt + 1
        /\ lost_tasks' = lost_tasks \cup victim_tasks
        /\ tasks' = tasks \ victim_tasks
        /\ lost_f_set' = lost_f_set \cup victim_finishes
        /\ f_set' = f_set \ victim_finishes
        /\ lost_lf_set' = lost_lf_set \cup victim_local_finishes
        /\ lf_set' = lf_set \ victim_local_finishes
        /\ rec_child' = rec_child \cup { 
                                          task \in C!GetChildrenTask : /\ task.finish_id \in rf_to
                                                                       /\ task.victim = victim
                                                                       /\ task.markingDone = FALSE
                                       }
        /\ rec_to' = rec_to \cup {
                                   task \in C!ConvTask: \E rf \in rf_set : \E p \in C!PlaceID : 
                                   /\ task.finish_id = rf.id
                                   /\ task.finish_id \in rf_to
                                   /\ rf.transOrLive[p][victim] > 0
                                   /\ task.from = p
                                   /\ task.to = victim
                                 }
        /\ rec_from' = rec_from \cup {
                                       task \in C!ConvTask: \E rf \in rf_set : \E p \in C!PlaceID : 
                                       /\ task.finish_id = rf.id
                                       /\ task.finish_id \in rf_to
                                       /\ rf.transOrLive[victim][p] > 0
                                       /\ task.to = p
                                       /\ task.from = victim                                 
                                     } 
        /\ step' = step + 1 
  /\ UNCHANGED << exec_state, rf_set, msgs, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  rec_from_waiting >>  


Program_Terminating ==
  /\ exec_state = "running"
  /\ LET root_task == CHOOSE task \in tasks : task.id = C!ROOT_TASK_ID
         root_task_updated == [ root_task EXCEPT !.status = "terminated" ]
     IN /\ root_task.status = "running" \* root task unblocked
        /\ tasks' = ( tasks \ {root_task} ) \cup { root_task_updated }
        /\ exec_state' = "success"
        /\ step' = step + 1
  /\ UNCHANGED << f_set, lf_set, rf_set, msgs, 
                  nxt_finish_id, nxt_task_id, nxt_remote_place,
                  killed, killed_cnt,
                  lost_tasks, lost_f_set, lost_lf_set,
                  rec_child, rec_to, rec_from, rec_from_waiting >>
  
---------------------------------------------------------------------------- 
Next ==
  \/ CreatingFinish
\*  \/ Finish_ForkingLocalTask
  \/ Finish_CreatingRemoteTask
  \/ Finish_TerminatingTask
  \/ Finish_ReceivingPublishDoneSignal
  \/ Finish_ReceivingReleaseSignal
\*  \/ LocalFinish_ForkingLocalTask
  \/ LocalFinish_CreatingRemoteTask
  \/ LocalFinish_TerminatingTask
  \/ LocalFinish_CountingDroppedTasksFromDeadPlace
  \/ SendingTask
  \/ DroppingTask
  \/ ReceivingTask
  \/ Store_ReceivingPublishSignal
  \/ Store_ReceivingTransitSignal
  \/ Store_ReceivingTerminateTaskSignal
  \/ Store_ReceivingTerminateGhostSignal
  \/ Store_MarkingGhostChildrenAsAdopted
  \/ Store_AddingGhostChildren
  \/ Store_CancellingTasksToDeadPlace
  \/ Store_SendingCountDroppedSignalToLocalFinish
  \/ Store_CancellingDroppedTasksFromDeadPlace
  \/ KillingPlace
  \/ Program_Terminating
     
Liveness ==
  /\ WF_Vars( CreatingFinish )
\*  /\ WF_Vars( Finish_ForkingLocalTask )
  /\ WF_Vars( Finish_CreatingRemoteTask )
  /\ WF_Vars( Finish_TerminatingTask )
  /\ WF_Vars( Finish_ReceivingPublishDoneSignal )
  /\ WF_Vars( Finish_ReceivingReleaseSignal )
\*  /\ WF_Vars( LocalFinish_ForkingLocalTask )
  /\ WF_Vars( LocalFinish_CreatingRemoteTask )
  /\ WF_Vars( LocalFinish_TerminatingTask )
  /\ WF_Vars( LocalFinish_CountingDroppedTasksFromDeadPlace )
  /\ WF_Vars( SendingTask )
  /\ WF_Vars( DroppingTask )
  /\ WF_Vars( ReceivingTask )
  /\ WF_Vars( Store_ReceivingPublishSignal )
  /\ WF_Vars( Store_ReceivingTransitSignal )
  /\ WF_Vars( Store_ReceivingTerminateTaskSignal )
  /\ WF_Vars( Store_ReceivingTerminateGhostSignal )
  /\ WF_Vars( Store_MarkingGhostChildrenAsAdopted )
  /\ WF_Vars( Store_AddingGhostChildren )
  /\ WF_Vars( Store_CancellingTasksToDeadPlace )
  /\ WF_Vars( Store_SendingCountDroppedSignalToLocalFinish )
  /\ WF_Vars( Store_CancellingDroppedTasksFromDeadPlace )  
  /\ WF_Vars( KillingPlace )    
  /\ WF_Vars( Program_Terminating )
    
-----------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)          
Spec ==  Init /\ [][Next]_Vars /\ Liveness

THEOREM Spec => []( TypeOK /\ StateOK)
=============================================================================
