/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*          Xavier Leroy and Damien Doligez, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 2009 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

/* POSIX thread implementation of the "st" interface */

#include <assert.h>
#include "caml/alloc.h"
#include "caml/domain_state.h"
#include "caml/platform.h"
#include "caml/custom.h"
#include "caml/memory.h"
#include "caml/fail.h"
#include "caml/alloc.h"
#include "caml/startup.h"
#include "caml/fiber.h"
#include "caml/callback.h"
#include "caml/weak.h"
#include "caml/finalise.h"
#include "caml/domain.h"
#include "caml/printexc.h"
#include "caml/backtrace.h"
#include <pthread.h>
#include <signal.h>
#include <caml/signals.h>
#ifdef __GNUC__
#undef INLINE
#define INLINE inline
#else
#define INLINE
#endif

typedef int st_retcode;

#define SIGPREEMPTION SIGVTALRM

/* Thread creation.  Created in detached mode if [res] is NULL. */

typedef pthread_t st_thread_id;

static int st_thread_create(st_thread_id * res,
                            void * (*fn)(void *), void * arg)
{
  pthread_t thr;
  pthread_attr_t attr;
  int rc;

  pthread_attr_init(&attr);
  if (res == NULL) pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
  rc = pthread_create(&thr, &attr, fn, arg);
  if (res != NULL) *res = thr;
  return rc;
}

#define ST_THREAD_FUNCTION void *

/* Cleanup at thread exit */

static INLINE void st_thread_cleanup(void)
{
  return;
}

/* Thread termination */

CAMLnoreturn_start
static void st_thread_exit(void)
CAMLnoreturn_end;

static void st_thread_exit(void)
{
  pthread_exit(NULL);
}

/* Thread-specific state */

typedef pthread_key_t st_tlskey;

static int st_tls_newkey(st_tlskey * res)
{
  return pthread_key_create(res, NULL);
}

static INLINE void * st_tls_get(st_tlskey k)
{
  return pthread_getspecific(k);
}

static INLINE void st_tls_set(st_tlskey k, void * v)
{
  pthread_setspecific(k, v);
}

/* The master lock.  This is a mutex that is held most of the time,
   so we implement it in a slightly convoluted way to avoid
   all risks of busy-waiting.  Also, we count the number of waiting
   threads. */

typedef struct st_masterlock_struct {
  caml_plat_mutex lock;
  caml_plat_cond free;
  atomic_uintnat busy;
  atomic_uintnat waiters;
} st_masterlock;

// For both these functions, we decide to signal the backup thread under
// specific conditions. However the domain lock should always be owned
// by the dec currently executing OCaml code.

static void caml_thread_bt_lock_acquire(st_masterlock *m) {

  // We do not want to signal the backup thread is it is not "working"
  // as it may very well not be, because we could have just resumed
  // execution from another dec right away.
  if (caml_bt_is_bt_working()) {
    caml_bt_enter_ocaml();
  }

  caml_bt_acquire_domain_lock();

  return;
}

static void caml_thread_bt_lock_release(st_masterlock *m) {

  // Here we do want to signal the backup thread iff there's
  // no dec waiting to be scheduled, and the backup thread is currently
  // idle.
  if (atomic_load_acq(&m->waiters) == 0 &&
      caml_bt_is_bt_working() == 0) {
    caml_bt_exit_ocaml();
  }

  caml_bt_release_domain_lock();

  return;
}

static void st_masterlock_init(st_masterlock *m) {

  caml_plat_mutex_init(&m->lock);
  caml_plat_cond_init(&m->free, &m->lock);
  atomic_store_rel(&m->busy, 1);
  atomic_store_rel(&m->waiters, 0);

  return;
}

static void st_masterlock_acquire(st_masterlock *m)
{
  caml_plat_lock(&m->lock);
  while (atomic_load_acq(&m->busy)) {
    atomic_fetch_add(&m->waiters, +1);
    caml_plat_wait(&m->free);
    atomic_fetch_add(&m->waiters, -1);
  }
  atomic_store_rel(&m->busy, 1);
  caml_thread_bt_lock_acquire(m);
  caml_plat_unlock(&m->lock);

  return;
}

static void st_masterlock_release(st_masterlock * m)
{
  caml_plat_lock(&m->lock);
  atomic_store_rel(&m->busy, 0);
  caml_thread_bt_lock_release(m);
  caml_plat_signal(&m->free);
  caml_plat_unlock(&m->lock);

  return;
}

/* Scheduling hints */

static void st_masterlock_yield(st_masterlock *m)
{
  uintnat waiters;

  caml_plat_lock(&m->lock);
  /* We must hold the lock to call this. */

  /* We already checked this without the lock, but we might have raced--if
     there's no waiter, there's nothing to do and no one to wake us if we did
     wait, so just keep going. */
  waiters = atomic_load_acq(&m->waiters);

  if (waiters == 0) {
    caml_plat_unlock(&m->lock);
    return;
  }

  atomic_store_rel(&m->busy, 0);

  caml_plat_signal(&m->free);
  // releasing the domain lock but not triggering bt messaging
  // messaging the bt should not be required because yield assumes
  // that a thread will resume execution (be it the yielding thread
  // or a waiting thread
  caml_bt_release_domain_lock();
  atomic_fetch_add(&m->waiters, +1);
  do {
    /* Note: the POSIX spec prevents the above signal from pairing with this
       wait, which is good: we'll reliably continue waiting until the next
       yield() or enter_blocking_section() call (or we see a spurious condvar
       wakeup, which are rare at best.) */
       caml_plat_wait(&m->free);
  } while (atomic_load_acq(&m->busy));

  atomic_store_rel(&m->busy, 1);
  atomic_fetch_add(&m->waiters, -1);

  caml_bt_acquire_domain_lock();

  caml_plat_unlock(&m->lock);

  return;
}


/* Mutexes */

typedef caml_plat_mutex * st_mutex;

static void st_mutex_create(st_mutex * res)
{
  st_mutex m = caml_stat_alloc_noexc(sizeof(caml_plat_mutex));
  caml_plat_mutex_init(m);
  *res = m;
  return ;
}

static void st_mutex_destroy(st_mutex m)
{
  caml_plat_mutex_free(m);
  return ;
}

static INLINE void st_mutex_lock(st_mutex m)
{
  return caml_plat_lock(m);
}

#define PREVIOUSLY_UNLOCKED 0
#define ALREADY_LOCKED EBUSY

static INLINE int st_mutex_trylock(st_mutex m)
{
  return pthread_mutex_trylock(m);
}

static INLINE int st_mutex_unlock(st_mutex m)
{
  return pthread_mutex_unlock(m);
}

/* Condition variables */

typedef caml_plat_cond * st_condvar;

static void st_condvar_create(st_condvar * res)
{
  st_condvar c = caml_stat_alloc_noexc(sizeof(st_condvar));
  caml_plat_cond_init_no_mutex(c);
  *res = c;
  return ;
}

static void st_condvar_destroy(st_condvar c)
{
  caml_plat_cond_free(c);
  caml_stat_free(c);
  return ;
}

// TODO: refactor the condition part in a way that makes the Condition module
// and platform code cohabit.
// thread_cond_broadcast and thread_cond_signals are borrowed from platform
// but do not assert on the mutex.
// The main issue is that platform conditions do rely on explicitly binding a
// mutex to the cond, which is not how Condition work.

void st_condvar_signal(st_condvar cond)
{
  check_err("thread_cond_signal", pthread_cond_signal(&cond->cond));
}

void st_condvar_broadcast(st_condvar cond)
{
  check_err("thread_cond_broadcast", pthread_cond_broadcast(&cond->cond));
}

static INLINE void st_condvar_wait(st_condvar c, st_mutex m)
{
  caml_plat_cond_set_mutex(c, m);
  return caml_plat_wait(c);
}

/* Triggered events */

typedef struct st_event_struct {
  caml_plat_mutex lock;         /* to protect contents */
  int status;                   /* 0 = not triggered, 1 = triggered */
  caml_plat_cond triggered;     /* signaled when triggered */
} * st_event;

static void st_event_create(st_event *res)
{
  st_event e = caml_stat_alloc(sizeof(st_event));
  caml_plat_mutex_init(&e->lock);
  caml_plat_cond_init(&e->triggered, &e->lock);
  e->status = 0;
  return ;
}

static void st_event_destroy(st_event e)
{
  caml_plat_cond_free(&e->triggered);
  caml_plat_mutex_free(&e->lock);
  caml_stat_free(e);
  return;
}

static void st_event_trigger(st_event e)
{
  caml_plat_lock(&e->lock);
  e->status = 1;
  caml_plat_signal(&e->triggered);
  caml_plat_unlock(&e->lock);
  return;
}

static void st_event_wait(st_event e)
{
  caml_plat_lock(&e->lock);
  while(e->status == 0) {
    caml_plat_wait(&e->triggered);
  }
  caml_plat_unlock(&e->lock);
}

/* Reporting errors */

static void st_check_error(int retcode, char * msg)
{
  char * err;
  int errlen, msglen;
  value str;

  if (retcode == 0) return;
  if (retcode == ENOMEM) caml_raise_out_of_memory();
  err = strerror(retcode);
  msglen = strlen(msg);
  errlen = strlen(err);
  str = caml_alloc_string(msglen + 2 + errlen);
  memmove (&Byte(str, 0), msg, msglen);
  memmove (&Byte(str, msglen), ": ", 2);
  memmove (&Byte(str, msglen + 2), err, errlen);
  caml_raise_sys_error(str);
}

/* Variable used to stop the "tick" thread */
static volatile int caml_tick_thread_stop = 0;

/* "At fork" processing */

#if defined(__ANDROID__)
/* Android's libc does not include declaration of pthread_atfork;
   however, it implements it since API level 10 (Gingerbread).
   The reason for the omission is that Android (GUI) applications
   are not supposed to fork at all, however this workaround is still
   included in case OCaml is used for an Android CLI utility. */
int pthread_atfork(void (*prepare)(void), void (*parent)(void),
                   void (*child)(void));
#endif

static int st_atfork(void (*fn)(void))
{
  return pthread_atfork(NULL, NULL, fn);
}

/* Signal handling */

static void st_decode_sigset(value vset, sigset_t * set)
{
  sigemptyset(set);
  while (vset != Val_int(0)) {
    int sig = caml_convert_signal_number(Int_field(vset, 0));
    sigaddset(set, sig);
    vset = Field_imm(vset, 1);
  }
}

#ifndef NSIG
#define NSIG 64
#endif

static value st_encode_sigset(sigset_t * set)
{
  value res = Val_int(0);
  int i;

  Begin_root(res)
    for (i = 1; i < NSIG; i++)
      if (sigismember(set, i) > 0) {
        value newcons = caml_alloc_small(2, 0);
        caml_modify_field(newcons, 0, Val_int(caml_rev_convert_signal_number(i)));
        caml_modify_field(newcons, 1, res);
        res = newcons;
      }
  End_roots();
  return res;
}

static int sigmask_cmd[3] = { SIG_SETMASK, SIG_BLOCK, SIG_UNBLOCK };

value caml_thread_sigmask(value cmd, value sigs) /* ML */
{
  int how;
  sigset_t set, oldset;
  int retcode;

  how = sigmask_cmd[Int_val(cmd)];
  st_decode_sigset(sigs, &set);
  caml_enter_blocking_section();
  retcode = pthread_sigmask(how, &set, &oldset);
  caml_leave_blocking_section();
  st_check_error(retcode, "Thread.sigmask");
  return st_encode_sigset(&oldset);
}

value caml_wait_signal(value sigs) /* ML */
{
#ifdef HAS_SIGWAIT
  sigset_t set;
  int retcode, signo;

  st_decode_sigset(sigs, &set);
  caml_enter_blocking_section();
  retcode = sigwait(&set, &signo);
  caml_leave_blocking_section();
  st_check_error(retcode, "Thread.wait_signal");
  return Val_int(caml_rev_convert_signal_number(signo));
#else
  caml_invalid_argument("Thread.wait_signal not implemented");
  return Val_int(0);            /* not reached */
#endif
}
