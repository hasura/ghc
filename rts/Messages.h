/* ---------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2010
 *
 * Inter-Capability message passing
 *
 * --------------------------------------------------------------------------*/

#pragma once

#include "Capability.h"
#include "Updates.h" // for DEBUG_FILL_SLOP
#include "Schedule.h" // for SCHED_INTERRUPTING
#include "SMPClosureOps.h"

#include "BeginPrivate.h"

uint32_t messageBlackHole(Capability *cap, MessageBlackHole *msg);
StgTSO * blackHoleOwner (StgClosure *bh);

#if defined(THREADED_RTS)
void executeMessage (Capability *cap, Message *m);
void sendMessage    (Capability *from_cap, Capability *to_cap, Message *msg);
#endif

INLINE_HEADER void
doneWithMsgThrowTo (Capability *cap, MessageThrowTo *m)
{
    // The message better be locked (unless we are running single-threaded,
    // where we are a bit more lenient (#19075) or we got here from
    // deleteAllThreads() due to RTS shutdown).
    ASSERT(getNumCapabilities() == 1 || m->header.info == &stg_WHITEHOLE_info || getSchedState() == SCHED_INTERRUPTING);
    IF_NONMOVING_WRITE_BARRIER_ENABLED {
      updateRemembSetPushMessageThrowTo(cap, m);
    }
    OVERWRITING_CLOSURE((StgClosure*)m);
    unlockClosure((StgClosure*)m, &stg_MSG_NULL_info);
    LDV_RECORD_CREATE(m);
}

#include "EndPrivate.h"

#if defined(THREADED_RTS) && defined(PROF_SPIN)
extern volatile StgWord64 whitehole_executeMessage_spin;
#endif
