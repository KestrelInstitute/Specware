#include "private/pthread_support.h"

#if defined(GC_PTHREADS) && !defined(GC_SOLARIS_THREADS) \
     && !defined(GC_IRIX_THREADS) && !defined(GC_WIN32_THREADS) \
     && !defined(GC_DARWIN_THREADS) && !defined(GC_AIX_THREADS)

#include <signal.h>
#include <semaphore.h>
#include <errno.h>
#include <unistd.h>

#if DEBUG_THREADS

#ifndef NSIG
# if defined(MAXSIG)
#  define NSIG (MAXSIG+1)
# elif defined(_NSIG)
#  define NSIG _NSIG
# elif defined(__SIGRTMAX)
#  define NSIG (__SIGRTMAX+1)
# else
  --> please fix it
# endif
#endif

void GC_print_sig_mask()
{
    sigset_t blocked;
    int i;

    if (pthread_sigmask(SIG_BLOCK, NULL, &blocked) != 0)
    	ABORT("pthread_sigmask");
    GC_printf0("Blocked: ");
    for (i = 1; i < NSIG; i++) {
        if (sigismember(&blocked, i)) { GC_printf1("%ld ",(long) i); }
    }
    GC_printf0("\n");
}

#endif

word GC_stop_count;	/* Incremented at the beginning of GC_stop_world. */

#ifdef GC_OSF1_THREADS
  GC_bool GC_retry_signals = TRUE;
#else
  GC_bool GC_retry_signals = FALSE;
#endif

/*
 * We use signals to stop threads during GC.
 * 
 * Suspended threads wait in signal handler for SIG_THR_RESTART.
 * That's more portable than semaphores or condition variables.
 * (We do use sem_post from a signal handler, but that should be portable.)
 *
 * The thread suspension signal SIG_SUSPEND is now defined in gc_priv.h.
 * Note that we can't just stop a thread; we need it to save its stack
 * pointer(s) and acknowledge.
 */

#ifndef SIG_THR_RESTART
#  if defined(GC_HPUX_THREADS) || defined(GC_OSF1_THREADS)
#    ifdef _SIGRTMIN
#      define SIG_THR_RESTART _SIGRTMIN + 5
#    else
#      define SIG_THR_RESTART SIGRTMIN + 5
#    endif
#  else
#   define SIG_THR_RESTART SIGXCPU
#  endif
#endif

sem_t GC_suspend_ack_sem;

void GC_suspend_handler(int sig)
{
    int dummy;
    pthread_t my_thread = pthread_self();
    GC_thread me;
    sigset_t mask;
#   ifdef PARALLEL_MARK
	word my_mark_no = GC_mark_no;
	/* Marker can't proceed until we acknowledge.  Thus this is	*/
	/* guaranteed to be the mark_no correspending to our 		*/
	/* suspension, i.e. the marker can't have incremented it yet.	*/
#   endif
    word my_stop_count = GC_stop_count;

    if (sig != SIG_SUSPEND) ABORT("Bad signal in suspend_handler");

#if DEBUG_THREADS
    GC_printf1("Suspending 0x%lx\n", my_thread);
#endif

    me = GC_lookup_thread(my_thread);
    /* The lookup here is safe, since I'm doing this on behalf  */
    /* of a thread which holds the allocation lock in order	*/
    /* to stop the world.  Thus concurrent modification of the	*/
    /* data structure is impossible.				*/
    if (me -> stop_info.last_stop_count == my_stop_count) {
	/* Duplicate signal.  OK if we are retrying.	*/
	if (!GC_retry_signals) {
	    WARN("Duplicate suspend signal in thread %lx\n",
		 pthread_self());
	}
	return;
    }
#   ifdef SPARC
	me -> stop_info.stack_ptr = (ptr_t)GC_save_regs_in_stack();
#   else
	me -> stop_info.stack_ptr = (ptr_t)(&dummy);
#   endif
#   ifdef IA64
	me -> backing_store_ptr = (ptr_t)GC_save_regs_in_stack();
#   endif

    /* Tell the thread that wants to stop the world that this   */
    /* thread has been stopped.  Note that sem_post() is  	*/
    /* the only async-signal-safe primitive in LinuxThreads.    */
    sem_post(&GC_suspend_ack_sem);
    me -> stop_info.last_stop_count = my_stop_count;

    /* Wait until that thread tells us to restart by sending    */
    /* this thread a SIG_THR_RESTART signal.			*/
    /* SIG_THR_RESTART should be masked at this point.  Thus there	*/
    /* is no race.						*/
    if (sigfillset(&mask) != 0) ABORT("sigfillset() failed");
    if (sigdelset(&mask, SIG_THR_RESTART) != 0) ABORT("sigdelset() failed");
#   ifdef NO_SIGNALS
      if (sigdelset(&mask, SIGINT) != 0) ABORT("sigdelset() failed");
      if (sigdelset(&mask, SIGQUIT) != 0) ABORT("sigdelset() failed");
      if (sigdelset(&mask, SIGTERM) != 0) ABORT("sigdelset() failed");
      if (sigdelset(&mask, SIGABRT) != 0) ABORT("sigdelset() failed");
#   endif
    do {
	    me->stop_info.signal = 0;
	    sigsuspend(&mask);             /* Wait for signal */
    } while (me->stop_info.signal != SIG_THR_RESTART);
    /* If the RESTART signal gets lost, we can still lose.  That should be  */
    /* less likely than losing the SUSPEND signal, since we don't do much   */
    /* between the sem_post and sigsuspend.	   			    */
    /* We'd need more handshaking to work around that, since we don't want  */
    /* to accidentally leave a RESTART signal pending, thus causing us to   */
    /* continue prematurely in a future round.				    */ 

#if DEBUG_THREADS
    GC_printf1("Continuing 0x%lx\n", my_thread);
#endif
}

void GC_restart_handler(int sig)
{
    pthread_t my_thread = pthread_self();
    GC_thread me;

    if (sig != SIG_THR_RESTART) ABORT("Bad signal in suspend_handler");

    /* Let the GC_suspend_handler() know that we got a SIG_THR_RESTART. */
    /* The lookup here is safe, since I'm doing this on behalf  */
    /* of a thread which holds the allocation lock in order	*/
    /* to stop the world.  Thus concurrent modification of the	*/
    /* data structure is impossible.				*/
    me = GC_lookup_thread(my_thread);
    me->stop_info.signal = SIG_THR_RESTART;

    /*
    ** Note: even if we didn't do anything useful here,
    ** it would still be necessary to have a signal handler,
    ** rather than ignoring the signals, otherwise
    ** the signals will not be delivered at all, and
    ** will thus not interrupt the sigsuspend() above.
    */

#if DEBUG_THREADS
    GC_printf1("In GC_restart_handler for 0x%lx\n", pthread_self());
#endif
}

# ifdef IA64
#   define IF_IA64(x) x
# else
#   define IF_IA64(x)
# endif
/* We hold allocation lock.  Should do exactly the right thing if the	*/
/* world is stopped.  Should not fail if it isn't.			*/
void GC_push_all_stacks()
{
    int i;
    GC_thread p;
    ptr_t lo, hi;
    /* On IA64, we also need to scan the register backing store. */
    IF_IA64(ptr_t bs_lo; ptr_t bs_hi;)
    pthread_t me = pthread_self();
    
    if (!GC_thr_initialized) GC_thr_init();
    #if DEBUG_THREADS
        GC_printf1("Pushing stacks from thread 0x%lx\n", (unsigned long) me);
    #endif
    for (i = 0; i < THREAD_TABLE_SZ; i++) {
      for (p = GC_threads[i]; p != 0; p = p -> next) {
        if (p -> flags & FINISHED) continue;
        if (pthread_equal(p -> id, me)) {
#  	    ifdef SPARC
	        lo = (ptr_t)GC_save_regs_in_stack();
#  	    else
 	        lo = GC_approx_sp();
#           endif
	    IF_IA64(bs_hi = (ptr_t)GC_save_regs_in_stack();)
	} else {
	    lo = p -> stop_info.stack_ptr;
	    IF_IA64(bs_hi = p -> backing_store_ptr;)
	}
        if ((p -> flags & MAIN_THREAD) == 0) {
	    hi = p -> stack_end;
	    IF_IA64(bs_lo = p -> backing_store_end);
        } else {
            /* The original stack. */
            hi = GC_stackbottom;
	    IF_IA64(bs_lo = BACKING_STORE_BASE;)
        }
        #if DEBUG_THREADS
            GC_printf3("Stack for thread 0x%lx = [%lx,%lx)\n",
    	        (unsigned long) p -> id,
		(unsigned long) lo, (unsigned long) hi);
        #endif
	if (0 == lo) ABORT("GC_push_all_stacks: sp not set!\n");
#       ifdef STACK_GROWS_UP
	  /* We got them backwards! */
          GC_push_all_stack(hi, lo);
#       else
          GC_push_all_stack(lo, hi);
#	endif
#	ifdef IA64
          if (pthread_equal(p -> id, me)) {
	    GC_push_all_eager(bs_lo, bs_hi);
	  } else {
	    GC_push_all_stack(bs_lo, bs_hi);
	  }
#	endif
      }
    }
}

/* There seems to be a very rare thread stopping problem.  To help us  */
/* debug that, we save the ids of the stopping thread. */
pthread_t GC_stopping_thread;
int GC_stopping_pid;

/* We hold the allocation lock.  Suspend all threads that might	*/
/* still be running.  Return the number of suspend signals that	*/
/* were sent. */
int GC_suspend_all()
{
    int n_live_threads = 0;
    int i;
    GC_thread p;
    int result;
    pthread_t my_thread = pthread_self();
    
    GC_stopping_thread = my_thread;    /* debugging only.      */
    GC_stopping_pid = getpid();                /* debugging only.      */
    for (i = 0; i < THREAD_TABLE_SZ; i++) {
      for (p = GC_threads[i]; p != 0; p = p -> next) {
        if (p -> id != my_thread) {
            if (p -> flags & FINISHED) continue;
            if (p -> stop_info.last_stop_count == GC_stop_count) continue;
	    if (p -> thread_blocked) /* Will wait */ continue;
            n_live_threads++;
	    #if DEBUG_THREADS
	      GC_printf1("Sending suspend signal to 0x%lx\n", p -> id);
	    #endif
        
        result = pthread_kill(p -> id, SIG_SUSPEND);
	    switch(result) {
                case ESRCH:
                    /* Not really there anymore.  Possible? */
                    n_live_threads--;
                    break;
                case 0:
                    break;
                default:
                    ABORT("pthread_kill failed");
            }
        }
      }
    }
    return n_live_threads;
}

/* Caller holds allocation lock.	*/
void GC_stop_world()
{
    int i;
    int n_live_threads;
    int code;

    #if DEBUG_THREADS
    GC_printf1("Stopping the world from 0x%lx\n", pthread_self());
    #endif
       
    /* Make sure all free list construction has stopped before we start. */
    /* No new construction can start, since free list construction is	*/
    /* required to acquire and release the GC lock before it starts,	*/
    /* and we have the lock.						*/
#   ifdef PARALLEL_MARK
      GC_acquire_mark_lock();
      GC_ASSERT(GC_fl_builder_count == 0);
      /* We should have previously waited for it to become zero. */
#   endif /* PARALLEL_MARK */
    ++GC_stop_count;
    n_live_threads = GC_suspend_all();

      if (GC_retry_signals) {
	  unsigned long wait_usecs = 0;  /* Total wait since retry.	*/
#	  define WAIT_UNIT 3000
#	  define RETRY_INTERVAL 100000
	  for (;;) {
	      int ack_count;

	      sem_getvalue(&GC_suspend_ack_sem, &ack_count);
	      if (ack_count == n_live_threads) break;
	      if (wait_usecs > RETRY_INTERVAL) {
		  int newly_sent = GC_suspend_all();

#                 ifdef CONDPRINT
		    if (GC_print_stats) {
		      GC_printf1("Resent %ld signals after timeout\n",
				 newly_sent);
		    }
#                 endif
		  sem_getvalue(&GC_suspend_ack_sem, &ack_count);
		  if (newly_sent < n_live_threads - ack_count) {
		      WARN("Lost some threads during GC_stop_world?!\n",0);
		      n_live_threads = ack_count + newly_sent;
		  }
		  wait_usecs = 0;
	      }
	      usleep(WAIT_UNIT);
	      wait_usecs += WAIT_UNIT;
	  }
      }
    for (i = 0; i < n_live_threads; i++) {
	  if (0 != (code = sem_wait(&GC_suspend_ack_sem))) {
	      GC_err_printf1("Sem_wait returned %ld\n", (unsigned long)code);
	      ABORT("sem_wait for handler failed");
	  }
    }
#   ifdef PARALLEL_MARK
      GC_release_mark_lock();
#   endif
    #if DEBUG_THREADS
      GC_printf1("World stopped from 0x%lx\n", pthread_self());
    #endif
    GC_stopping_thread = 0;  /* debugging only */
}

/* Caller holds allocation lock, and has held it continuously since	*/
/* the world stopped.							*/
void GC_start_world()
{
    pthread_t my_thread = pthread_self();
    register int i;
    register GC_thread p;
    register int n_live_threads = 0;
    register int result;

#   if DEBUG_THREADS
      GC_printf0("World starting\n");
#   endif

    for (i = 0; i < THREAD_TABLE_SZ; i++) {
      for (p = GC_threads[i]; p != 0; p = p -> next) {
        if (p -> id != my_thread) {
            if (p -> flags & FINISHED) continue;
	    if (p -> thread_blocked) continue;
            n_live_threads++;
	    #if DEBUG_THREADS
	      GC_printf1("Sending restart signal to 0x%lx\n", p -> id);
	    #endif
        
        result = pthread_kill(p -> id, SIG_THR_RESTART);
	    switch(result) {
                case ESRCH:
                    /* Not really there anymore.  Possible? */
                    n_live_threads--;
                    break;
                case 0:
                    break;
                default:
                    ABORT("pthread_kill failed");
            }
        }
      }
    }
    #if DEBUG_THREADS
      GC_printf0("World started\n");
    #endif
}

void GC_stop_init() {
    struct sigaction act;
    
    if (sem_init(&GC_suspend_ack_sem, 0, 0) != 0)
        ABORT("sem_init failed");

    act.sa_flags = SA_RESTART;
    if (sigfillset(&act.sa_mask) != 0) {
    	ABORT("sigfillset() failed");
    }
#   ifdef NO_SIGNALS
      if (sigdelset(&act.sa_mask, SIGINT) != 0
	  || sigdelset(&act.sa_mask, SIGQUIT != 0)
	  || sigdelset(&act.sa_mask, SIGABRT != 0)
	  || sigdelset(&act.sa_mask, SIGTERM != 0)) {
        ABORT("sigdelset() failed");
      }
#   endif

    /* SIG_THR_RESTART is unmasked by the handler when necessary. 	*/
    act.sa_handler = GC_suspend_handler;
    if (sigaction(SIG_SUSPEND, &act, NULL) != 0) {
    	ABORT("Cannot set SIG_SUSPEND handler");
    }

    act.sa_handler = GC_restart_handler;
    if (sigaction(SIG_THR_RESTART, &act, NULL) != 0) {
    	ABORT("Cannot set SIG_THR_RESTART handler");
    }

    /* Check for GC_RETRY_SIGNALS.	*/
      if (0 != GETENV("GC_RETRY_SIGNALS")) {
	  GC_retry_signals = TRUE;
      }
      if (0 != GETENV("GC_NO_RETRY_SIGNALS")) {
	  GC_retry_signals = FALSE;
      }
#     ifdef CONDPRINT
          if (GC_print_stats && GC_retry_signals) {
              GC_printf0("Will retry suspend signal if necessary.\n");
	  }
#     endif
}

#endif
