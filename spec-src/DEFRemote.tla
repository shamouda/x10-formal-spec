----------------------------- MODULE DEFRemote -----------------------------
(*******************************************************************************)
(* TODO: Root must clean the remote objects. Remote objects should be reusable *)
(*******************************************************************************)
EXTENDS Sequences, Integers
VARIABLES fid, fstates, msgs, thrds
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS
INSTANCE Commons
----------------------------------------------------------------------------
Alloc(type, here, root) == 
   /\ fstates[fid].status \in { "unused", "forgotten" }
   /\ fstates' = [fstates EXCEPT ![fid].id = fid,
                                 ![fid].count = 0, 
                                 ![fid].status = "waiting",
                                 ![fid].type = type,
                                 ![fid].here = here,
                                 ![fid].root = root]

LastActivity ==
   /\ fstates[fid].count = 1
     
NotifySubActivitySpawn(dst) == 
    /\ fstates' = [fstates EXCEPT ![fid].remActs[dst] = @+1]

NotifySubActivitySpawnError(dst) == FALSE
    
NotifyActivityCreation(src, activity) == 
    /\ fstates' = [fstates EXCEPT ![fid].count = @+1] 

NotifyActivitySpawnAndCreation (here, activity) ==
    /\ IF fstates[fid].here = here
       THEN fstates' = [fstates EXCEPT ![fid].count = @+1,
                                       ![fid].remActs[here] = @+1 ] 
       ELSE fstates' = fstates

NotifyActivityTermination ==
    /\ fstates[fid].count > 0 
    /\ LET here == fstates[fid].here
       IN  IF LastActivity 
           THEN  fstates' = [fstates EXCEPT ![fid].count = @-1,
                                            ![fid].remActs[here] = @-1,
                                            ![fid].status = "finished"]
           ELSE  fstates' = [fstates EXCEPT ![fid].count = @-1,
                                            ![fid].remActs[here] = @-1 ] 

PushException(e) == 
    /\ fstates' = [fstates EXCEPT ![fid].excs = Append(@, e)]

SendTermMsg(mid) ==
   LET pid == fstates[fid].root
       pidHome == GetFinishHome(pid) 
       here == fstates[fid].here
   IN  /\ fstates' = [fstates EXCEPT ![fid].status = "forgotten"]
       /\ SendMsg ([ mid |-> mid, 
                     src |-> here, 
                     dst |-> pidHome, 
                     type |-> "asyncTerm", 
                     fid |-> pid, 
                     remActs |-> fstates[fid].remActs, 
                     excs |-> fstates[fid].excs])

ProcessChildTermMsg(msg) == FALSE  \* remote does't need this action

=============================================================================
\* Modification History
\* Last modified Thu Oct 12 20:18:39 AEDT 2017 by u5482878
\* Last modified Tue Sep 26 23:12:25 AEST 2017 by shamouda
\* Created Wed Sep 13 12:17:03 AEST 2017 by u5482878
