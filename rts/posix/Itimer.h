/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team 1998-2005
 *
 * Interval timer for profiling and pre-emptive scheduling.
 *
 * ---------------------------------------------------------------------------*/

#ifndef ITIMER_H
#define ITIMER_H

#if defined(USE_TIMER_CREATE)
#  define ITIMER_SIGNAL SIGVTALRM
#elif defined(HAVE_SETITIMER)
#  define ITIMER_SIGNAL  SIGALRM
   // Using SIGALRM can leads to problems, see #850.  But we have no
   // option if timer_create() is not available.
#else
#  error No way to set an interval timer.
#endif

#endif /* ITIMER_H */

// Local Variables:
// mode: C
// fill-column: 80
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// End:
