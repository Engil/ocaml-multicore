#define CAML_INTERNALS

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

/* ML value for a thread descriptor */

struct caml_thread_descr {
  value id;
  value clos;
  value terminated;
};

#define Threadstatus_val(v) (* ((thread_event *) Data_custom_val(v)))
#define Ident(v) (((struct caml_thread_descr *)(v))->id)
#define Clos(v) (((struct caml_thread_descr *)(v))->clos)
#define Terminated(v) (((struct caml_thread_descr *)(v))->terminated)

/* Event structure */

typedef struct event_struct {
  caml_plat_mutex lock;         /* to protect contents */
  int status;                   /* 0 = not triggered, 1 = triggered */
  caml_plat_cond triggered;     /* signaled when triggered */
} * thread_event;

static value caml_threadstatus_new (value unit);
static int thread_event_create(thread_event * res);
static void caml_threadstatus_terminate (value wrapper);

/* main runtime lock */

struct caml_thread_main_lock {
  caml_plat_mutex lock;
  caml_plat_cond free;
  atomic_uintnat busy;
  atomic_uintnat waiters;
};

#ifdef NATIVE_CODE
extern struct longjmp_buffer caml_termination_jmpbuf;
extern void (*caml_termination_hook)(void);
#endif

/* dec structure holding runtime state */
struct caml_thread_struct {

  value descr;

  struct caml_thread_struct * next;
  struct caml_thread_struct * prev;

  int domain_id;

  struct stack_info* current_stack;
  struct c_stack_link* c_stack;
  struct caml__roots_block *local_roots;
  struct longjmp_buffer *exit_buf;
  int backtrace_pos;
  code_t * backtrace_buffer;
  caml_root backtrace_last_exn;
  value * gc_regs_buckets;
  value ** gc_regs_slot;
  void * exn_handler;

  #ifndef NATIVE_CODE
  intnat trap_sp_off;
  intnat trap_barrier_off;
  struct caml_exception_context* external_raise;
  #endif

};

typedef struct caml_thread_struct* caml_thread_t;

/* overall table for decs accross domains */
struct caml_thread_table {
  caml_thread_t all_decs;
  caml_thread_t current_dec;
  pthread_key_t thread_key;
  struct caml_thread_main_lock thread_lock;
};

/* thread_table instance, up to Max_domains */
static struct caml_thread_table thread_table[Max_domains];

/* unique dec id */
static atomic_uintnat thread_next_id;

#define Thread_main_lock thread_table[Caml_state->id].thread_lock
#define Thread_key thread_table[Caml_state->id].thread_key
#define All_decs thread_table[Caml_state->id].all_decs
#define Current_dec thread_table[Caml_state->id].current_dec

static void (*prev_scan_roots_hook) (scanning_action, void *, struct domain *);

/* main lock's logic, analogous to systhread's master lock. */
/* The main lock is to be held by a dec that is going to execute OCaml code */
/* or interfere with the runtime in any way. */
/* There is one main lock per domain. */

static void caml_thread_main_lock_init(struct caml_thread_main_lock *m) {

  caml_plat_mutex_init(&m->lock);
  caml_plat_cond_init(&m->free, &m->lock);
  atomic_store_rel(&m->busy, 1);
  atomic_store_rel(&m->waiters, 0);

  return;
};

// For both these functions, we decide to signal the backup thread under
// specific conditions. However the domain lock should always be owned
// by the dec currently executing OCaml code.

static void caml_thread_bt_lock_acquire(struct caml_thread_main_lock *m) {

  // We do not want to signal the backup thread is it is not "working"
  // as it may very well not be, because we could have just resumed
  // execution from another dec right away.
  if (caml_bt_is_bt_working()) {
    caml_bt_enter_ocaml();
  }

  caml_bt_acquire_domain_lock();

  return;
}

static void caml_thread_bt_lock_release(struct caml_thread_main_lock *m) {

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

static void caml_thread_main_lock_acquire(struct caml_thread_main_lock *m)
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

static void caml_thread_main_lock_release(struct caml_thread_main_lock * m)
{
  caml_plat_lock(&m->lock);
  atomic_store_rel(&m->busy, 0);
  caml_thread_bt_lock_release(m);
  caml_plat_signal(&m->free);
  caml_plat_unlock(&m->lock);

  return;
}

static void caml_thread_main_lock_yield(struct caml_thread_main_lock * m)
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

static void caml_thread_scan_roots(scanning_action action, void *fdata, struct domain *self)
{
  caml_thread_t dec;

  dec = Current_dec;

  // a GC could be triggered before current_dec is initialized
  if (dec != NULL) {
    do {
      (*action)(fdata, dec->descr, &dec->descr);

      if (dec != Current_dec) {
	if (dec->current_stack != NULL)
	  caml_do_local_roots(action, fdata, dec->local_roots, dec->current_stack, 0);
      }
      dec = dec->next;
    } while (dec != Current_dec);

  };

  if (prev_scan_roots_hook != NULL) (*prev_scan_roots_hook)(action, fdata, self);

  return;
}

void caml_thread_save_runtime_state(void)
{
  Current_dec->current_stack = Caml_state->current_stack;
  Current_dec->c_stack = Caml_state->c_stack;
  Current_dec->gc_regs_buckets = Caml_state->gc_regs_buckets;
  Current_dec->gc_regs_slot = Caml_state->gc_regs_slot;
  Current_dec->exn_handler = Caml_state->exn_handler;
  Current_dec->local_roots = Caml_state->local_roots;
  Current_dec->backtrace_pos = Caml_state->backtrace_pos;
  Current_dec->backtrace_buffer = Caml_state->backtrace_buffer;
  Current_dec->backtrace_last_exn = Caml_state->backtrace_last_exn;
  #ifndef NATIVE_CODE
  Current_dec->trap_sp_off = Caml_state->trap_sp_off;
  Current_dec->trap_barrier_off = Caml_state->trap_barrier_off;
  Current_dec->external_raise = Caml_state->external_raise;
  #endif
}

void caml_thread_restore_runtime_state(void)
{
  Caml_state->current_stack = Current_dec->current_stack;
  Caml_state->c_stack = Current_dec->c_stack;
  Caml_state->gc_regs_buckets = Current_dec->gc_regs_buckets;
  Caml_state->gc_regs_slot = Current_dec->gc_regs_slot;
  Caml_state->exn_handler = Current_dec->exn_handler;
  Caml_state->local_roots = Current_dec->local_roots;
  Caml_state->backtrace_pos = Current_dec->backtrace_pos;
  Caml_state->backtrace_buffer = Current_dec->backtrace_buffer;
  Caml_state->backtrace_last_exn = Current_dec->backtrace_last_exn;
  #ifndef NATIVE_CODE
  Caml_state->trap_sp_off = Current_dec->trap_sp_off;
  Caml_state->trap_barrier_off = Current_dec->trap_barrier_off;
  Caml_state->external_raise = Current_dec->external_raise;
  #endif
}

static void caml_thread_enter_blocking_section(void)
{
  Current_dec = pthread_getspecific(Thread_key);
  caml_thread_save_runtime_state();
  pthread_setspecific(Thread_key, Current_dec);
  caml_thread_main_lock_release(&Thread_main_lock);
}

static void caml_thread_leave_blocking_section(void)
{
  caml_thread_main_lock_acquire(&Thread_main_lock);
  Current_dec = pthread_getspecific(Thread_key);
  caml_thread_restore_runtime_state();
}

static caml_thread_t caml_thread_new_info(void)
{
  caml_thread_t dec;
  struct domain *d;

  d = caml_domain_self();
  dec = NULL;
  dec = (caml_thread_t) caml_stat_alloc_noexc(sizeof(struct caml_thread_struct));
  if (dec == NULL) return NULL;

  dec->descr = Val_unit;
  dec->current_stack = caml_alloc_main_stack(Stack_size / sizeof(value));;
  dec->c_stack = NULL;
  dec->exn_handler = NULL;
  dec->local_roots = NULL;
  dec->exit_buf = NULL;
  dec->backtrace_pos = 0;
  dec->backtrace_buffer = NULL;
  dec->backtrace_last_exn = caml_create_root(Val_unit);
  dec->domain_id = d->state->id;

  #ifndef NATIVE_CODE
  dec->trap_sp_off = 1;
  dec->trap_barrier_off = 2;
  dec->external_raise = NULL;
  #endif

  return dec;
}

static value caml_thread_new_descriptor(value clos)
{
  CAMLparam1(clos);
  CAMLlocal2(descr, mu);

  mu = Val_unit;
  mu = caml_threadstatus_new(Val_unit);
  descr = caml_alloc_small(3, 0);
  Ident(descr) = Val_long(atomic_load_acq(&thread_next_id));
  Clos(descr) = clos;
  Terminated(descr) = mu;
  atomic_fetch_add(&thread_next_id, +1);

  CAMLreturn (descr);
}

// used to clean context after fork.
static void caml_thread_reinitialize(void)
{
  caml_thread_t dec, next;

  dec = Current_dec->next;
  while (dec != Current_dec) {
    next = dec->next;
    caml_stat_free(dec);
    dec = next;
  }
  Current_dec->next = Current_dec;
  Current_dec->prev = Current_dec;
  All_decs = Current_dec;

  // within the child, the domain_lock needs to be reset
  // and acquired.
  caml_reset_domain_lock();
  caml_bt_acquire_domain_lock();
  // main_lock needs to be initialized and released.
  caml_thread_main_lock_init(&Thread_main_lock);
  caml_thread_main_lock_release(&Thread_main_lock);
}

static int thread_atfork(void (*fn)(void))
{
  return pthread_atfork(NULL, NULL, fn);
}

CAMLprim value caml_thread_initialize(value unit);

static void caml_thread_domain_start_hook(void) {
  caml_thread_initialize(Val_unit);
}

CAMLprim value caml_thread_initialize(value unit)
{
  CAMLparam0();

  caml_thread_t new_dec;

  caml_thread_main_lock_init(&Thread_main_lock);

  new_dec =
    (caml_thread_t) caml_stat_alloc_noexc(sizeof(struct caml_thread_struct));

  new_dec->descr = caml_thread_new_descriptor(Val_unit);
  new_dec->next = new_dec;
  new_dec->prev = new_dec;

  #ifdef NATIVE_CODE
  new_dec->exit_buf = &caml_termination_jmpbuf;
  #endif

  // Hooks setup, if caml_scan_roots_hook is set, it was done already
  // by another domain.
  if (caml_scan_roots_hook != caml_thread_scan_roots) {
    prev_scan_roots_hook = caml_scan_roots_hook;
    caml_scan_roots_hook = caml_thread_scan_roots;
    caml_enter_blocking_section_hook = caml_thread_enter_blocking_section;
    caml_leave_blocking_section_hook = caml_thread_leave_blocking_section;
    caml_domain_start_hook = caml_thread_domain_start_hook;
  };

  pthread_key_create(&Thread_key, NULL);
  pthread_setspecific(Thread_key, (void *) new_dec);

  All_decs = new_dec;
  Current_dec = new_dec;

  thread_atfork(caml_thread_reinitialize);

  CAMLreturn(Val_unit);
}

static void caml_thread_remove_info(caml_thread_t dec)
{
  if (dec->next == dec)
    All_decs = NULL;
  else if (All_decs == dec)
    All_decs = dec->next;

  dec->next->prev = dec->prev;
  dec->prev->next = dec->next;
  caml_stat_free(dec->current_stack);
  return;
}

static void caml_thread_stop(void)
{
  caml_threadstatus_terminate(Terminated(Current_dec->descr));
  caml_thread_remove_info(Current_dec);
  // FIXME: tricky bit with backup thread
  // Normally we expect the next thread to kick in and resume operation
  // by first setting Current_dec to the right TLS dec data.
  // However it may very well be that there's no runnable dec next
  // (eg: next dec is blocking.), so we set it to next for now to give a
  // valid state to the backup thread.
  Current_dec = Current_dec->next;
  caml_thread_restore_runtime_state();
  caml_thread_main_lock_release(&Thread_main_lock);
}

static void * caml_thread_start(void * v)
{
  caml_thread_t dec = (caml_thread_t) v;
  value clos;
#ifdef NATIVE_CODE
  struct longjmp_buffer termination_buf;
#endif

  caml_init_domain_self(dec->domain_id);

  pthread_setspecific(Thread_key, dec);

  caml_thread_main_lock_acquire(&Thread_main_lock);
  Current_dec = pthread_getspecific(Thread_key);
  caml_thread_restore_runtime_state();

#ifdef NATIVE_CODE
  /* Setup termination handler (for caml_thread_exit) */
  if (sigsetjmp(termination_buf.buf, 0) == 0) {
    Current_dec->exit_buf = &termination_buf;
#endif
  clos = Clos(Current_dec->descr);
  caml_modify(&(Clos(Current_dec->descr)), Val_unit);
  caml_callback_exn(clos, Val_unit);
  caml_thread_stop();
#ifdef NATIVE_CODE
  }
#endif
  return 0;
}

CAMLprim value caml_thread_new(value clos)
{
  CAMLparam1(clos);
  pthread_t th;
  pthread_attr_t attr;
  caml_thread_t dec;

  pthread_attr_init(&attr);
  pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);

  dec = caml_thread_new_info();
  dec->descr = caml_thread_new_descriptor(clos);

  dec->next = Current_dec->next;
  dec->prev = Current_dec;

  Current_dec->next->prev = dec;
  Current_dec->next = dec;

  pthread_create(&th, &attr, caml_thread_start, (void *) dec);

  CAMLreturn(dec->descr);
}

CAMLprim value caml_thread_self(value unit)
{
  return Current_dec->descr;
}

CAMLprim value caml_thread_id(value th)
{
  return Val_long(Ident(th));
}

CAMLprim value caml_thread_yield(value unit)
{
  if (atomic_load_acq(&Thread_main_lock.waiters) == 0) return Val_unit;

  caml_thread_save_runtime_state();
  caml_thread_main_lock_yield(&Thread_main_lock);
  Current_dec = pthread_getspecific(Thread_key);
  caml_thread_restore_runtime_state();

  return Val_unit;
}

CAMLprim value caml_thread_exit(value unit)
{
  struct longjmp_buffer * exit_buf = NULL;

  if (Current_dec == NULL)
    caml_invalid_argument("Thread.exit: not initialized");

  #ifdef NATIVE_CODE
    exit_buf = Current_dec->exit_buf;
  #endif

    caml_thread_stop();

  if (exit_buf != NULL) {
    /* Native-code and (main thread or thread created by OCaml) */
    siglongjmp(exit_buf->buf, 1);
  } else {
    pthread_exit(NULL);
  };

  return Val_unit;
}

/* events */

static void caml_threadstatus_destroy(thread_event e)
{
  caml_plat_cond_free(&e->triggered);
  caml_plat_mutex_free(&e->lock);
  caml_stat_free(e);
}

static void caml_threadstatus_finalize(value wrapper)
{
  caml_threadstatus_destroy(Threadstatus_val(wrapper));
}

CAMLprim value caml_thread_uncaught_exception(value exn)
{
  char * msg = caml_format_exception(exn);
  fprintf(stderr, "Thread %d killed on uncaught exception %s\n",
          Int_val(Ident(Current_dec->descr)), msg);
  caml_stat_free(msg);
  if (Caml_state->backtrace_active) caml_print_exception_backtrace();
  fflush(stderr);
  return Val_unit;
}

static int caml_threadstatus_compare(value wrapper1, value wrapper2)
{
  thread_event ts1 = Threadstatus_val(wrapper1);
  thread_event ts2 = Threadstatus_val(wrapper2);
  return ts1 == ts2 ? 0 : ts1 < ts2 ? -1 : 1;
}

static struct custom_operations caml_threadstatus_ops = {
  "_decstatus",
  caml_threadstatus_finalize,
  caml_threadstatus_compare,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default,
  custom_fixed_length_default
};

static value caml_threadstatus_new (value unit);

static int thread_event_create(thread_event * res)
{
  thread_event e = caml_stat_alloc_noexc(sizeof(struct event_struct));
  if (e == NULL) return ENOMEM;
  caml_plat_mutex_init(&e->lock);
  caml_plat_cond_init(&e->triggered, &e->lock);
  e->status = 0;
  *res = e;
  return 0;
}

static value caml_threadstatus_new (value unit)
{
  CAMLparam0();
  CAMLlocal1(wrapper);

  thread_event ts = NULL;           /* suppress warning */
  thread_event_create(&ts);
  wrapper = caml_alloc_custom(&caml_threadstatus_ops, sizeof(thread_event *),
                              0, 1);
  Threadstatus_val(wrapper) = ts;

  CAMLreturn (wrapper);
}

static void thread_event_trigger(thread_event e)
{
  caml_plat_lock(&e->lock);
  e->status = 1;
  caml_plat_signal(&e->triggered);
  caml_plat_unlock(&e->lock);
  return;
}

static void caml_threadstatus_terminate (value wrapper)
{
  thread_event_trigger(Threadstatus_val(wrapper));
}

static void thread_event_wait(thread_event e)
{
  caml_plat_lock(&e->lock);
  while(e->status == 0) {
    caml_plat_wait(&e->triggered);
  }
  caml_plat_unlock(&e->lock);
}

static void caml_threadstatus_wait (value wrapper)
{
  thread_event ts = Threadstatus_val(wrapper);

  Begin_roots1(wrapper)         /* prevent deallocation of ts */
    caml_enter_blocking_section();
    thread_event_wait(ts);
    caml_leave_blocking_section();
  End_roots();

  return;
}

CAMLprim value caml_thread_join(value th)          /* ML */
{
  CAMLparam1(th);
  caml_threadstatus_wait(Terminated(th));
  CAMLreturn(Val_unit);
}

/* mutex */

typedef caml_plat_mutex * thread_mutex;

#define Mutex_val(v) (* ((thread_mutex *) Data_custom_val(v)))

static void caml_mutex_finalize(value wrapper)
{
  caml_plat_mutex_free(Mutex_val(wrapper));
}

static int caml_mutex_compare(value wrapper1, value wrapper2)
{
  thread_mutex mut1 = Mutex_val(wrapper1);
  thread_mutex mut2 = Mutex_val(wrapper2);
  return mut1 == mut2 ? 0 : mut1 < mut2 ? -1 : 1;
}

static intnat caml_mutex_hash(value wrapper)
{
  return (intnat) (Mutex_val(wrapper));
}

static struct custom_operations caml_mutex_ops = {
  "_mutex",
  caml_mutex_finalize,
  caml_mutex_compare,
  caml_mutex_hash,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default,
  custom_fixed_length_default
};

CAMLprim value caml_mutex_new(value unit)        /* ML */
{
  CAMLparam0();
  CAMLlocal1(wrapper);
  thread_mutex mut = caml_stat_alloc_noexc(sizeof(caml_plat_mutex));

  caml_plat_mutex_init(mut);
  wrapper = caml_alloc_custom(&caml_mutex_ops, sizeof(caml_plat_mutex *),
                              0, 1);
  Mutex_val(wrapper) = mut;
  CAMLreturn(wrapper);
}

CAMLprim value caml_mutex_lock(value wrapper)     /* ML */
{
  thread_mutex mut = Mutex_val(wrapper);

  /* PR#4351: first try to acquire mutex without releasing the master lock */
  if (caml_plat_try_lock(mut)) return Val_unit;
  /* If unsuccessful, block on mutex */
  Begin_root(wrapper)
    caml_enter_blocking_section();
    caml_plat_lock(mut);
    caml_leave_blocking_section();
  End_roots();
  return Val_unit;
}

CAMLprim value caml_mutex_unlock(value wrapper)           /* ML */
{
  thread_mutex mut = Mutex_val(wrapper);
  /* PR#4351: no need to release and reacquire master lock */
  caml_plat_unlock(mut);
  return Val_unit;
}

CAMLprim value caml_mutex_try_lock(value wrapper)           /* ML */
{
  thread_mutex mut = Mutex_val(wrapper);
  int retcode = caml_plat_try_lock(mut);
  if (retcode == 1) return Val_false;
  return Val_true;
}


/* Cond */

typedef caml_plat_cond * thread_cond;

// TODO: refactor the condition part in a way that makes the Condition module
// and platform code cohabit.
// thread_cond_broadcast and thread_cond_signals are borrowed from platform
// but do not assert on the mutex.
// The main issue is that platform conditions do rely on explicitly binding a
// mutex to the cond, which is not how Condition work.

void caml_thread_cond_broadcast(caml_plat_cond* cond)
{
  check_err("thread_cond_broadcast", pthread_cond_broadcast(&cond->cond));
}

void caml_thread_cond_signal(caml_plat_cond* cond)
{
  check_err("thread_cond_signal", pthread_cond_signal(&cond->cond));
}

#define Condition_val(v) (* (thread_cond *) Data_custom_val(v))

static void caml_condition_finalize(value wrapper)
{
  caml_plat_cond_free(Condition_val(wrapper));
}

static int caml_condition_compare(value wrapper1, value wrapper2)
{
  thread_cond cond1 = Condition_val(wrapper1);
  thread_cond cond2 = Condition_val(wrapper2);
  return cond1 == cond2 ? 0 : cond1 < cond2 ? -1 : 1;
}

static intnat caml_condition_hash(value wrapper)
{
  return (intnat) (Condition_val(wrapper));
}

static struct custom_operations caml_condition_ops = {
  "_condition",
  caml_condition_finalize,
  caml_condition_compare,
  caml_condition_hash,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default,
  custom_fixed_length_default
};

CAMLprim value caml_condition_new(value unit)        /* ML */
{
  value wrapper;
  thread_cond cond;

  cond = caml_stat_alloc_noexc(sizeof(caml_plat_cond));
  caml_plat_cond_init_no_mutex(cond);
  wrapper = caml_alloc_custom(&caml_condition_ops, sizeof(caml_plat_cond *),
                              0, 1);
  Condition_val(wrapper) = cond;
  return wrapper;
}

CAMLprim value caml_condition_wait(value wcond, value wmut)           /* ML */
{
  thread_cond cond = Condition_val(wcond);
  thread_mutex mut = Mutex_val(wmut);

  Begin_roots2(wcond, wmut)
    caml_enter_blocking_section();
    caml_plat_cond_set_mutex(cond, mut);
    caml_plat_wait(cond);
    caml_leave_blocking_section();
  End_roots();

  return Val_unit;
}

CAMLprim value caml_condition_signal(value wrapper)           /* ML */
{
  caml_thread_cond_signal(Condition_val(wrapper));
  return Val_unit;
}

CAMLprim value caml_condition_broadcast(value wrapper)           /* ML */
{
  caml_thread_cond_broadcast(Condition_val(wrapper));
  return Val_unit;
}

/* Signal handling */

static void thread_decode_sigset(value vset, sigset_t * set)
{
  sigemptyset(set);
  while (vset != Val_int(0)) {
    int sig = caml_convert_signal_number(Int_field(vset, 0));
    sigaddset(set, sig);
    vset = Field_imm(vset, 1);
  }
}

static value thread_encode_sigset(sigset_t * set)
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

CAMLprim value caml_thread_sigmask(value cmd, value sigs)
{
  int how;
  sigset_t set, oldset;

  how = sigmask_cmd[Int_val(cmd)];
  thread_decode_sigset(sigs, &set);
  caml_enter_blocking_section();
  pthread_sigmask(how, &set, &oldset);
  caml_leave_blocking_section();

  return thread_encode_sigset(&oldset);
}

value caml_wait_signal(value sigs) /* ML */
{
#ifdef HAS_SIGWAIT
  sigset_t set;
  int signo;

  thread_decode_sigset(sigs, &set);
  caml_enter_blocking_section();
  sigwait(&set, &signo);
  caml_leave_blocking_section();
  return Val_int(caml_rev_convert_signal_number(signo));
#else
  caml_invalid_argument("Thread.wait_signal not implemented");
  return Val_int(0);            /* not reached */
#endif
}
