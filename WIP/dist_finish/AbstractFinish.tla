--------------------------- MODULE AbstractFinish -----------------------
EXTENDS Integers, Sequences
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS, BACKUP
VARIABLES fid, fstates, msgs, thrds, p0fstates, isDead, mseq, pstate, p0adoptSet, waitForMsgs
-------------------------------------------------------------------------
SPMDRemote == INSTANCE SPMDRemote
SPMDRoot == INSTANCE SPMDRoot
DefaultRemote == INSTANCE DEFRemote
DefaultRoot == INSTANCE DEFRoot
P0ResilientFinish == INSTANCE P0Finish
DistributedFinish == INSTANCE DistFinish

-------------------------------------------------------------------------
Alloc(type, here, parent, root) ==
    \/ type = "SPMDroot" /\ SPMDRoot!Alloc(type, here, parent, root)
    \/ type = "SPMDremote" /\ SPMDRemote!Alloc(type, here, parent, root)
    \/ type = "root" /\ SPMDRoot!Alloc(type, here, parent, root)
    \/ type = "remote" /\ DefaultRemote!Alloc(type, here, parent, root)
    \/ type \in {"p0root", "p0remote"} /\ P0ResilientFinish!Alloc(type, here, parent, root)
    \/ type \in {"distroot", "distremote"} /\ DistributedFinish!Alloc(type, here, parent, root)
   
NotifySubActivitySpawn(dst) ==
    /\  fstates[fid].status = "waiting" 
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!NotifySubActivitySpawn(dst)
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!NotifySubActivitySpawn(dst)
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!NotifySubActivitySpawn(dst)
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!NotifySubActivitySpawn(dst)
        \/  /\ fstates[fid].type \in {"p0root", "p0remote"} 
            /\ P0ResilientFinish!NotifySubActivitySpawn(dst)
        \/  /\ fstates[fid].type \in {"distroot", "distremote"} 
            /\ DistributedFinish!NotifySubActivitySpawn(dst)

NotifySubActivitySpawnError(dst) ==
    /\  fstates[fid].status = "waiting" 
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!NotifySubActivitySpawnError(dst)
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!NotifySubActivitySpawnError(dst)
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!NotifySubActivitySpawnError(dst)
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!NotifySubActivitySpawnError(dst)
        \/  /\ fstates[fid].type \in {"p0root", "p0remote"} 
            /\ P0ResilientFinish!NotifySubActivitySpawnError(dst)
        \/  /\ fstates[fid].type \in {"distroot", "distremote"} 
            /\ DistributedFinish!NotifySubActivitySpawnError(dst)

\*needed for the local path of Runtime.runAsync
NotifyLocalActivitySpawnAndCreation (here, act) ==
    /\  fstates[fid].status = "waiting"
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!NotifyLocalActivitySpawnAndCreation(here, act)
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!NotifyLocalActivitySpawnAndCreation(here, act)
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!NotifyLocalActivitySpawnAndCreation(here, act)
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!NotifyLocalActivitySpawnAndCreation(here, act)
        \/  /\ fstates[fid].type \in {"p0root", "p0remote"} 
            /\ P0ResilientFinish!NotifyLocalActivitySpawnAndCreation(here, act)
        \/  /\ fstates[fid].type \in {"distroot", "distremote"} 
            /\ DistributedFinish!NotifyLocalActivitySpawnAndCreation(here, act)

NotifyRemoteActivityCreation(src, act, inMsg) ==
    /\  fstates[fid].status = "waiting" 
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!NotifyRemoteActivityCreation(src, act, inMsg)
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!NotifyRemoteActivityCreation(src, act, inMsg)
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!NotifyRemoteActivityCreation(src, act, inMsg)
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!NotifyRemoteActivityCreation(src, act, inMsg)
        \/  /\ fstates[fid].type \in {"p0root", "p0remote"} 
            /\ P0ResilientFinish!NotifyRemoteActivityCreation(src, act, inMsg)
        \/  /\ fstates[fid].type \in {"distroot", "distremote"} 
            /\ DistributedFinish!NotifyRemoteActivityCreation(src, act, inMsg)
   
NotifyActivityTermination ==
    /\  fstates[fid].status = "waiting" 
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!NotifyActivityTermination
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!NotifyActivityTermination
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!NotifyActivityTermination
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!NotifyActivityTermination
        \/  /\ fstates[fid].type \in {"p0root", "p0remote"} 
            /\ P0ResilientFinish!NotifyActivityTermination
        \/  /\ fstates[fid].type \in {"distroot", "distremote"} 
            /\ DistributedFinish!NotifyActivityTermination

PushException(e) ==
    /\  fstates[fid].status = "waiting" 
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!PushException(e)
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!PushException(e)
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!PushException(e)
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!PushException(e)
        \/  /\ fstates[fid].type \in {"p0root", "p0remote"} 
            /\ P0ResilientFinish!PushException(e)
        \/  /\ fstates[fid].type \in {"distroot", "distremote"} 
            /\ DistributedFinish!PushException(e)
   
Terminated ==
    /\ fstates[fid].status = "forgotten"

Running ==
    /\ fstates[fid].status = "waiting"

IsRoot ==
    /\ fstates[fid].type \in {"root", "SPMDroot", "p0root", "distroot"}

IsResilient ==
    /\ fstates[fid].type \in {"p0root", "p0remote", "distroot", "distremote"}

HasExceptions ==
    /\ Len(fstates[fid].excs) > 0
    
ProcessChildTermMsg(msg) ==
    /\  fstates[fid].status = "waiting"
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!ProcessChildTermMsg(msg)
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!ProcessChildTermMsg(msg)
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!ProcessChildTermMsg(msg)
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!ProcessChildTermMsg(msg)
        \/  /\ fstates[fid].type \in {"p0root", "p0remote"} 
            /\ P0ResilientFinish!ProcessChildTermMsg(msg)
        \/  /\ fstates[fid].type \in {"distroot", "distremote"} 
            /\ DistributedFinish!ProcessChildTermMsg(msg)

=============================================================================
\* Modification History
\* Last modified Sun Nov 12 08:24:06 AEDT 2017 by shamouda
\* Last modified Fri Nov 10 14:16:57 AEDT 2017 by u5482878
\* Created Wed Sep 13 12:15:06 AEST 2017 by u5482878
