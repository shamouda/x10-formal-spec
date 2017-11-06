----------------------------- MODULE P0ResStore -----------------------------
(***************************************************************************)
(* Resilient store hosted at PROG_HOME and is assumed be always available  *) 
(* See FinishResilientPlace0.x10 for the actual implementation             *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS
VARIABLES fstates, msgs, pstate, program, aseq, fseq, mseq, 
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,
           killed, killedCnt, p0fstates, pendingAct, isDead, p0dead, p0adoptSet, p0state, p0convSet
INSTANCE Commons
-----------------------------------------------------------------------------
AddException (fid, pfid, root, rootPlace, src, target) ==
  /\ p0fstates' = [p0fstates EXCEPT ![fid].id = fid,
                                    ![fid].parent = pfid, 
                                    ![fid].gfsRoot = root,
                                    ![fid].gfsRootPlace = rootPlace,
                                    ![fid].excs = Append(@, [err |-> "DPE", from |-> target]) ]

AddTransitAdopted(fid, pfid, root, rootPlace, src, target) ==
   LET adopter == p0fstates[fid].adopterId
   IN  p0fstates' = [p0fstates EXCEPT ![adopter].numActive = @ + 1,
                                      ![adopter].transitAdopted[src][target] = @ + 1 ]

\* initialize parent too if not initialized
AddTransit(fid, pfid, root, rootPlace, src, target) ==
   IF p0fstates[fid].adopterId = NotID           
   THEN IF p0fstates[fid].id = NotID \* not yet initialized
        THEN  IF pfid > NoParent /\ p0fstates[pfid].id = NotID
              THEN p0fstates' = [p0fstates EXCEPT ![fid].id = fid,
                                             ![fid].parent = pfid,
                                             ![fid].gfsRoot = root,
                                             ![fid].gfsRootPlace = rootPlace,
                                             ![fid].numActive = @ + 2,
                                             ![fid].transit[src][target] = @ + 1,
                                             ![fid].live[rootPlace] = @ + 1,
                                             ![pfid].id =  pfid,
                                             ![pfid].parent = fstates[pfid].parent,
                                             ![pfid].gfsRoot = fstates[pfid].root,
                                             ![pfid].gfsRootPlace = fstates[fstates[pfid].root].here,
                                             ![pfid].numActive = 1,
                                             ![pfid].live[fstates[pfid].here] = 1] \* root finish's task
              ELSE p0fstates' = [p0fstates EXCEPT ![fid].id = fid,
                                             ![fid].parent = pfid,
                                             ![fid].gfsRoot = root,
                                             ![fid].gfsRootPlace = rootPlace,
                                             ![fid].numActive = @ + 2,
                                             ![fid].transit[src][target] = @ + 1,
                                             ![fid].live[rootPlace] = @ + 1 ] \* root finish's task
        ELSE  p0fstates' = [p0fstates EXCEPT ![fid].numActive = @ + 1,
                                             ![fid].transit[src][target] = @ + 1 ]
   ELSE AddTransitAdopted(fid, pfid, root, rootPlace, src, target)

TransitToLive(fid, src, target) ==
   IF p0fstates[fid].adopterId = NotID           
   THEN  /\ p0fstates[fid].id # NotID
         /\ p0fstates[fid].transit[src][target] > 0
         /\ p0fstates' = [p0fstates EXCEPT ![fid].transit[src][target] = @ - 1,
                                           ![fid].live[target] = @ + 1 ]
   ELSE LET adopter == p0fstates[fid].adopterId
        IN  /\ p0fstates[adopter].transitAdopted[src][target] > 0
            /\ p0fstates' = [p0fstates EXCEPT ![adopter].transitAdopted[src][target] = @ - 1,
                                              ![adopter].liveAdopted[target] = @ + 1 ]

LiveToCompleted(fid, target) ==
   IF p0fstates[fid].adopterId = NotID           
   THEN /\ p0fstates[fid].numActive > 0
        /\ p0fstates[fid].live[target] > 0
        /\ IF p0fstates[fid].numActive = 1
           THEN p0fstates' = [p0fstates EXCEPT ![fid].live[target] = @ - 1,
                                               ![fid].numActive = @ - 1,
                                               ![fid].isReleased = TRUE ]
           ELSE p0fstates' = [p0fstates EXCEPT ![fid].live[target] = @ - 1,
                                               ![fid].numActive = @ - 1]
   ELSE LET adopter == p0fstates[fid].adopterId
        IN  /\ p0fstates[adopter].liveAdopted[target] > 0
            /\ p0fstates[adopter].numActive > 0
            /\ p0fstates' = [p0fstates EXCEPT ![adopter].liveAdopted[target] = @ - 1,
                                              ![adopter].numActive = @ - 1 ]

Quiescent(fid) ==
   IF p0fstates[fid].adopterId = NotID           
   THEN p0fstates[fid].numActive = 1
   ELSE LET adopter == p0fstates[fid].adopterId
        IN  p0fstates[adopter].numActive = 1

ReleaseFinishMsg(fid, here) ==
   IF p0fstates[fid].adopterId = NotID           
   THEN [ mid |-> mseq,
          src |-> here, 
          dst |-> p0fstates[fid].gfsRootPlace, 
          fid |-> p0fstates[fid].gfsRoot,
         type |-> "releaseFinish" ]
   ELSE LET adopter == p0fstates[fid].adopterId
        IN  [ mid |-> mseq,
              src |-> here, 
              dst |-> p0fstates[adopter].gfsRootPlace, 
              fid |-> p0fstates[adopter].gfsRoot,
             type |-> "releaseFinish" ]

GetLostFIDs(dead) ==
   { m \in Adopter : /\ m.child # NotID
                     /\ m.adopter # NotID
                     /\ p0fstates[m.child].id # NotID
                     /\ p0fstates[m.child].adopterId = NotID
                     /\ fstates[m.adopter].id # NotID
                     /\ fstates[m.child].here = dead
                     /\ m.adopter = GetAdopter(m.child, dead)
                     /\ m.a = LiveAncestors(m.child, dead)
   }

GetAdoptionSeeker ==
    IF p0adoptSet = {} THEN NotAdoptor
    ELSE CHOOSE m \in p0adoptSet : TRUE

GetConvertTasks ==
   { t \in ConvTask :  /\ t.pl # NotPlace
                       /\ t.fid # NotID
                       /\ p0fstates[t.fid].id # NotID
                       /\ p0fstates[t.fid].adopterId = NotID
                       /\ isDead[PROG_HOME][t.pl] = FALSE
   }
   
GetConvertSeeker == 
    IF p0convSet = {} THEN NotConvTask
    ELSE CHOOSE m \in p0convSet : TRUE
    
CreateReleaseMessages ==
   { m \in ReleaseFinishMessages : /\ m.mid = mseq
                                   /\ m.src = PROG_HOME
                                   /\ \E r \in IDRange : /\ m.fid = r
                                                         /\ p0fstates[r].id = r
                                                         /\ p0fstates[r].numActive = 0 
                                                         /\ p0fstates[r].isReleased = FALSE 
                                                         /\ p0fstates[r].adopterId = NotID
                                                         /\ m.dst = fstates[r].here
   }
           
-----------------------------------------------------------------------------
RecvTransit(here) ==
   /\ p0state = "running"
   /\ pstate = "running"
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "transit")
           mid == msg.mid
           fid == msg.fid
           pfid == msg.pfid
           root == msg.rfid
           rootPlace == msg.rpl
           src == msg.src
           target == msg.target
      IN  /\ src # NotPlace
          /\ fid # NotID
          /\ msg # NotMessage
          /\ IF isDead[here][src]
             THEN p0fstates' = p0fstates
             ELSE IF isDead[here][target] 
             THEN AddException (fid, pfid, root, rootPlace, src, target)
             ELSE AddTransit(fid, pfid, root, rootPlace, src, target)
          /\ ReplaceMsg ([  mid |-> mid,
                            src |-> src, 
                            dst |-> here, 
                         target |-> target, 
                            fid |-> fid, 
                           pfid |-> pfid, 
                           rfid |-> root,
                           rpl  |-> rootPlace,
                           type |-> "transit" ],
                        [   mid |-> mseq, 
                            src |-> here,
                            dst |-> src,
                            fid |-> fid,
                           type |-> "transitDone"]) 
          /\ mseq' = mseq + 1
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq,  p0dead,p0convSet,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0adoptSet,p0state,
           killed, killedCnt, pendingAct, isDead >>
               
RecvLive(here) ==
   /\ p0state = "running"
   /\ pstate = "running"
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "live")
           mid == msg.mid
           fid == msg.fid
           src == msg.src
           target == msg.target
           actId == msg.aid
           submit == IF isDead[here][src] \/ isDead[here][target]
                     THEN FALSE
                     ELSE TRUE
      IN  /\ msg # NotMessage
          /\ IF submit 
             THEN TransitToLive(fid, src, target) 
             ELSE p0fstates' = p0fstates
          /\ ReplaceMsg ([ mid |-> mid,
                           src |-> src, 
                           dst |-> here, 
                        target |-> target, 
                           fid |-> fid, 
                           aid |-> actId,
                          type |-> "live" ],
                         [ mid |-> mseq,
                           src |-> here, 
                           dst |-> target, 
                           aid |-> actId,
                        submit |-> submit,
                          type |-> "liveDone" ])
          /\ mseq' = mseq + 1
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq,  p0dead,p0convSet,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0adoptSet,p0state,
           killed, killedCnt, pendingAct, isDead >>
           
RecvCompleted(here) ==
   /\ p0state = "running"
   /\ pstate = "running"
   /\ msgs # {}
   /\ LET  msg == FindIncomingMSG(here, "completed")
           mid == msg.mid
           fid == msg.fid
           src == msg.src
           target == msg.target
      IN  /\ msg # NotMessage
          /\ IF ~isDead[here][target] 
             THEN LiveToCompleted(fid, target)
             ELSE p0fstates' = p0fstates
          /\ IF    /\ Quiescent(fid) 
                   /\ ~isDead[here][target]
             THEN  /\ ReplaceMsg ([ mid |-> mid,
                                    src |-> src, 
                                    dst |-> here, 
                                 target |-> target, 
                                    fid |-> fid, 
                                   type |-> "completed" ],
                                  ReleaseFinishMsg(fid,here))
                   /\ mseq' = mseq + 1
              ELSE /\ RecvMsg([  mid |-> mid,
                                 src |-> src, 
                                 dst |-> here, 
                              target |-> target, 
                                 fid |-> fid, 
                                type |-> "completed" ])
                   /\ mseq' = mseq
     /\ UNCHANGED << fstates, pstate, program, aseq, fseq,  p0dead,p0convSet,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,p0adoptSet,p0state,
           killed, killedCnt, pendingAct, isDead >>
 
SeekAdoption(here) ==
    /\ p0state = "seekAdoption" 
    /\ LET pair == GetAdoptionSeeker
           lost == pair.child
           adopter == pair.adopter
       IN IF pair = NotAdoptor
          THEN /\ p0state' = "convertDead"
               /\ p0fstates' = p0fstates
               /\ p0adoptSet' = p0adoptSet
               /\ p0convSet' = GetConvertTasks
          ELSE /\ p0state' = p0state
               /\ p0fstates' = [ p0fstates EXCEPT ![lost].adopterId = adopter,
                                                  ![adopter].liveAdopted = [ p \in PLACE |->   p0fstates[adopter].liveAdopted[p] 
                                                                                             + p0fstates[lost].live[p]
                                                                                             + p0fstates[lost].liveAdopted[p] 
                                                                           ],
                                                  ![adopter].transitAdopted = [ p \in PLACE |-> 
                                                                                [ q \in PLACE |->  p0fstates[adopter].transitAdopted[p][q] 
                                                                                                 + p0fstates[lost].transit[p][q]
                                                                                                 + p0fstates[lost].transitAdopted[p][q]  
                                                                              ] ],
                                                  ![adopter].numActive = @ + p0fstates[lost].numActive
                               ]
               /\ p0adoptSet' = p0adoptSet \ {pair} 
               /\ p0convSet' = p0convSet                          
    /\ UNCHANGED << fstates, msgs, pstate, program, aseq, fseq, mseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,
           killed, killedCnt, pendingAct, isDead >>

ConvertDeadActivities(here) ==
    /\ p0state = "convertDead"
    /\ LET t == GetConvertSeeker
           pl == t.pl
           fid == t.fid
       IN  IF fid = NotID
           THEN /\ p0convSet' = p0convSet
                /\ p0state' = "release"
                /\ p0fstates' = p0fstates
           ELSE /\ p0convSet' = p0convSet \ {t}
                /\ p0fstates' = [p0fstates  EXCEPT ![fid].numActive = @ - p0fstates[fid].transit[pl][p0dead] 
                                                                        - p0fstates[fid].transit[p0dead][pl]
                                                                        - p0fstates[fid].transitAdopted[pl][p0dead] 
                                                                        - p0fstates[fid].transitAdopted[p0dead][pl]
                                                                        - p0fstates[fid].live[p0dead]
                                                                        - p0fstates[fid].liveAdopted[p0dead],
                                                   ![fid].transit[pl][p0dead]  = 0,
                                                   ![fid].transitAdopted[pl][p0dead]  = 0,
                                                   ![fid].transit[p0dead][pl]  = 0,
                                                   ![fid].transitAdopted[p0dead][pl]  = 0,
                                                   ![fid].live[p0dead] = 0,
                                                   ![fid].liveAdopted[p0dead] = 0                                                                  
                                ]
                /\ p0state' = p0state
    /\ UNCHANGED << fstates, msgs, pstate, program, aseq, fseq, mseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar,
           killed, killedCnt, pendingAct, isDead,p0adoptSet >>
                                     
ReleaseAll(here) ==
    /\ p0state = "release"
    /\ p0fstates' = [r \in IDRange |-> IF p0fstates[r].numActive = 0 /\ p0fstates[r].isReleased = FALSE /\ p0fstates[r].adopterId = NotID
                                       THEN [   id |-> p0fstates[r].id,
                                            parent |-> p0fstates[r].parent,
                                           gfsRoot |-> p0fstates[r].gfsRoot,
                                      gfsRootPlace |-> p0fstates[r].gfsRootPlace,
                                         numActive |-> p0fstates[r].numActive,
                                              live |-> p0fstates[r].live,
                                           transit |-> p0fstates[r].transit,
                                       liveAdopted |-> p0fstates[r].liveAdopted,
                                    transitAdopted |-> p0fstates[r].transitAdopted,
                                              excs |-> p0fstates[r].excs,
                                         adopterId |-> p0fstates[r].adopterId,
                                         isReleased|-> TRUE
                                       ]
                                       ELSE p0fstates[r] ]
    /\ msgs' = msgs \cup CreateReleaseMessages 
    /\ mseq' = mseq + 1
    /\ p0state' = "running"
    /\ UNCHANGED << fstates, pstate, program, aseq, fseq, p0dead,
           readyQ, thrds, ppProgram, ppcurStmt, incPar, decPar, p0convSet,
           killed, killedCnt, pendingAct, isDead,p0adoptSet >>

P0NotifyPlaceDeath(dead) == 
    /\ p0state = "running"
    /\ p0dead' = dead
    /\ p0adoptSet' = GetLostFIDs(dead) 
    /\ p0state' = "seekAdoption"
         
=============================================================================
\* Modification History
\* Last modified Mon Nov 06 19:10:23 AEDT 2017 by u5482878
\* Last modified Mon Nov 06 01:15:25 AEDT 2017 by shamouda
\* Created Fri Oct 13 15:15:59 AEDT 2017 by u5482878
