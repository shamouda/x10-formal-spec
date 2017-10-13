--------------------------- MODULE AbstractFinish -----------------------
EXTENDS Integers, Sequences
CONSTANTS PLACE, MXFINISHES, PROG_HOME, MXTHREADS, NBLOCKS, MXSTMTS
VARIABLES fid, fstates, msgs, thrds
-------------------------------------------------------------------------
SPMDRemote == INSTANCE SPMDRemote
SPMDRoot == INSTANCE SPMDRoot
DefaultRemote == INSTANCE DEFRemote
DefaultRoot == INSTANCE DEFRoot
-------------------------------------------------------------------------
Alloc(type, here, root) ==
    \/ type = "SPMDroot" /\ SPMDRoot!Alloc(type, here, root)
    \/ type = "SPMDremote" /\ SPMDRemote!Alloc(type, here, root)
    \/ type = "root" /\ SPMDRoot!Alloc(type, here, root)
    \/ type = "remote" /\ DefaultRemote!Alloc(type, here, root)   
   
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

\*needed for the local path of Runtime.runAsync
NotifyActivitySpawnAndCreation (dst, src, act) ==
    /\  fstates[fid].status = "waiting"
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!NotifyActivitySpawnAndCreation(dst, src, act)
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!NotifyActivitySpawnAndCreation(dst, src, act)
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!NotifyActivitySpawnAndCreation(dst, src, act)
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!NotifyActivitySpawnAndCreation(dst, src, act)

NotifyActivityCreation(src, act) ==
    /\  fstates[fid].status = "waiting" 
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!NotifyActivityCreation(src, act)
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!NotifyActivityCreation(src, act)
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!NotifyActivityCreation(src, act)
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!NotifyActivityCreation(src, act)
   
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
   
Terminated ==
    /\ fstates[fid].status = "forgotten"

Running ==
    /\ fstates[fid].status = "waiting"

IsRoot ==
    /\ fstates[fid].type \in {"root", "SPMDroot"}

HasExceptions ==
    /\ Len(fstates[fid].excs) > 0
    
SendTermMsg(mid) ==
    /\  fstates[fid].status = "finished"
    /\  \/  /\ fstates[fid].type = "SPMDroot" 
            /\ SPMDRoot!SendTermMsg(mid)
        \/  /\ fstates[fid].type = "SPMDremote" 
            /\ SPMDRemote!SendTermMsg(mid)
        \/  /\ fstates[fid].type = "root" 
            /\ DefaultRoot!SendTermMsg(mid)
        \/  /\ fstates[fid].type = "remote" 
            /\ DefaultRemote!SendTermMsg(mid)

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

=============================================================================
\* Modification History
\* Last modified Thu Oct 12 20:14:06 AEDT 2017 by u5482878
\* Last modified Tue Sep 26 23:12:01 AEST 2017 by shamouda
\* Created Wed Sep 13 12:15:06 AEST 2017 by u5482878
