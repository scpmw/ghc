/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1995-2005
 *
 * Interval timer service for profiling and pre-emptive scheduling.
 *
 * ---------------------------------------------------------------------------*/

/*
 * The interval timer is used for profiling and for context switching in the
 * threaded build. 
 *
 * This file defines the platform-independent view of interval timing, relying
 * on platform-specific services to install and run the timers.
 *
 */

#include "PosixSource.h"
#include "Rts.h"

#include "Timer.h"
#include "Proftimer.h"
#include "Schedule.h"
#include "Ticker.h"
#include "Capability.h"
#include "RtsSignals.h"
#include "Papi.h"

/* ticks left before next pre-emptive context switch */
static int ticks_to_ctxt_switch = 0;

#if defined(THREADED_RTS)
/* idle ticks left before we perform a GC */
static int ticks_to_gc = 0;
#endif

/*
 * Function: handle_tick()
 *
 * At each occurrence of a tick, the OS timer will invoke
 * handle_tick().
 */
static
void
handle_tick(int unused STG_UNUSED)
{
  handleProfTick();
  if (RtsFlags.ConcFlags.ctxtSwitchTicks > 0) {
      ticks_to_ctxt_switch--;
      if (ticks_to_ctxt_switch <= 0) {
	  ticks_to_ctxt_switch = RtsFlags.ConcFlags.ctxtSwitchTicks;
	  setContextSwitches();	/* schedule a context switch */
      }
  }

#if defined(THREADED_RTS)
  /* 
   * If we've been inactive for idleGCDelayTime (set by +RTS
   * -I), tell the scheduler to wake up and do a GC, to check
   * for threads that are deadlocked.
   */
  switch (recent_activity) {
  case ACTIVITY_YES:
      recent_activity = ACTIVITY_MAYBE_NO;
      ticks_to_gc = RtsFlags.GcFlags.idleGCDelayTime /
                    RtsFlags.MiscFlags.tickInterval;
      break;
  case ACTIVITY_MAYBE_NO:
      if (ticks_to_gc == 0) {
          /* 0 ==> no idle GC */
          recent_activity = ACTIVITY_DONE_GC;
          // disable timer signals (see #1623)
          stopTimer();
      } else {
          ticks_to_gc--;
          if (ticks_to_gc == 0) {
              ticks_to_gc = RtsFlags.GcFlags.idleGCDelayTime /
                  RtsFlags.MiscFlags.tickInterval;
              recent_activity = ACTIVITY_INACTIVE;
              wakeUpRts();
          }
      }
      break;
  default:
      break;
  }
#endif

#ifdef TRACING
#ifdef USE_PAPI
  if(RtsFlags.PapiFlags.sampleType) {
	  papi_timer();
  }
#endif
#ifdef USE_PERF_EVENTS
  if(RtsFlags.PerfEventFlags.sampleType) {
	  papi_timer();
  }
#endif
#endif

}

// This global counter is used to allow multiple threads to stop the
// timer temporarily with a stopTimer()/startTimer() pair.  If 
//      timer_enabled  == 0          timer is enabled
//      timer_disabled == N, N > 0   timer is disabled by N threads
// When timer_enabled makes a transition to 0, we enable the timer,
// and when it makes a transition to non-0 we disable it.

static StgWord timer_disabled;

void
initTimer(void)
{
    initProfTimer();
    if (RtsFlags.MiscFlags.tickInterval != 0) {
        initTicker(RtsFlags.MiscFlags.tickInterval, handle_tick);
    }
    timer_disabled = 1;
}

void
startTimer(void)
{
    if (atomic_dec(&timer_disabled) == 0) {
        if (RtsFlags.MiscFlags.tickInterval != 0) {
            startTicker();
        }
    }
}

void
stopTimer(void)
{
    if (atomic_inc(&timer_disabled) == 1) {
        if (RtsFlags.MiscFlags.tickInterval != 0) {
            stopTicker();
        }
    }
}

void
exitTimer (rtsBool wait)
{
    if (RtsFlags.MiscFlags.tickInterval != 0) {
        exitTicker(wait);
    }
}
