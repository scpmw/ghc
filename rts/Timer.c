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
#include "Trace.h"

// TODO...
#include "posix/Itimer.h"

/* ticks left before next pre-emptive context switch */
static int ticks_to_ctxt_switch = 0;

/* idle ticks left before we perform a GC */
static int ticks_to_gc = 0;

#ifdef TRACING
static void handleSamplingTick(StgBool isManual, void *pIP);
#endif

/*
 * Function: handle_tick()
 *
 * At each occurrence of a tick, the OS timer will invoke
 * handle_tick(). If available, we also get information
 * about the thread's instruction pointer when the signal
 * got raised.
 */
static
void
handle_tick(StgBool isManual, void *pIP)
{
#ifdef TRACING
  // Manually replicated signals are for being able to sample the
  // thread state only, ignore them on other threads.
  handleSamplingTick(isManual, pIP);
#else
  (void) pIP;
#endif
  if (isManual) { return; }

  handleProfTick();
  if (RtsFlags.ConcFlags.ctxtSwitchTicks > 0) {
      ticks_to_ctxt_switch--;
      if (ticks_to_ctxt_switch <= 0) {
	  ticks_to_ctxt_switch = RtsFlags.ConcFlags.ctxtSwitchTicks;
          contextSwitchAllCapabilities(); /* schedule a context switch */
      }
  }

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
          if (RtsFlags.GcFlags.doIdleGC) {
              recent_activity = ACTIVITY_INACTIVE;
#ifdef THREADED_RTS
              wakeUpRts();
              // The scheduler will call stopTimer() when it has done
              // the GC.
#endif
          } else {
              recent_activity = ACTIVITY_DONE_GC;
              // disable timer signals (see #1623, #5991)
              // but only if we're not profiling
#ifndef PROFILING
#ifdef TRACING
              if (!RtsFlags.TraceFlags.timerSampling) {
#endif
                  stopTimer();
#ifdef TRACING
              }
#endif
#endif
          }
      } else {
          ticks_to_gc--;
      }
      break;
  default:
      break;
  }

#ifdef TRACING
#ifdef USE_PERF_EVENTS
  if(RtsFlags.PerfEventFlags.sampleType) {
      perf_event_timer();
  }
#endif
#endif

}

#ifdef TRACING
static StgBool do_ticker_sampling = rtsTrue;

static void
flushTickerSamples(Task *task, Capability *cap)
{
    if (task->timer_ip_sample_count <= 0) { return; }
    traceSamples(cap, 1, SAMPLE_BY_TIME, SAMPLE_INSTR_PTR,
                 task->timer_ip_sample_count, task->timer_ip_samples, NULL);
    task->timer_ip_sample_count = 0;
}

static void
handleSamplingTick(StgBool isManual, void *pIP)
{
    (void) isManual; (void) pIP;
    if (!RtsFlags.TraceFlags.timerSampling ||
        !do_ticker_sampling) { return; }

    // Figure out where we are
    Task *task = myTask();
    Capability *cap = (task ? myTask()->cap : NULL);
    if (RtsFlags.TraceFlags.timerSampling && cap) {

        // Take a sample, handle overflow
        task->timer_ip_samples[task->timer_ip_sample_count++] = pIP;
        if (task->timer_ip_sample_count >= TIMER_MAX_SAMPLES) {
            flushTickerSamples(task, cap);
        }
    }

#if defined(THREADED_RTS) && defined(HAVE_PTHREAD_H) && !defined(mingw32_HOST_OS)
    if (!isManual) {
        // Replicate the signal to all other capabilities
        nat i;
        for (i = 0; i < n_capabilities; i++)
            if (capabilities[i] != cap) {
                Task *t = capabilities[i]->running_task;
                if (t && t->timer_ip_samples) {
                    pthread_kill(t->id, ITIMER_SIGNAL);
                }
            }
    }
#else
    (void) isManual;
#endif
}
#endif


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
#ifdef TRACING
            do_ticker_sampling = RtsFlags.TraceFlags.timerSampling;
#endif
            startTicker();
        }
    }
}

void
stopTimer(void)
{
    if (atomic_inc(&timer_disabled, 1) == 1) {
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

#ifdef TRACING
void
stopTickerSampling( void )
{
    do_ticker_sampling = rtsFalse;
    // also flush, if applicable
    Task *task = myTask();
    if (RtsFlags.TraceFlags.timerSampling && task && task->cap) {
        flushTickerSamples(task, task->cap);
    }
}

void
startTickerSampling( void )
{
    do_ticker_sampling = rtsTrue;
}
#endif

// Local Variables:
// mode: C
// fill-column: 80
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// End:
