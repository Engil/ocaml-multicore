/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*              Damien Doligez, projet Para, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <stddef.h>
#include "caml/config.h"
#include "caml/misc.h"
#include "caml/fail.h"
#include "caml/memory.h"
#include "caml/major_gc.h"
#include "caml/shared_heap.h"
#include "caml/domain.h"
#include "caml/addrmap.h"
#include "caml/roots.h"
#include "caml/alloc.h"
#include "caml/fiber.h"
#include "caml/platform.h"
#include "caml/eventlog.h"

/* The write barrier does not read or write the heap, it just
   modifies domain-local data structures. */
static void write_barrier(value obj, int field, value old_val, value new_val)
{
  caml_domain_state* domain_state = Caml_state;

  Assert (Is_block(obj));

  if (!Is_young(obj)) {

    caml_darken(0, old_val, 0);

    if (Is_block(new_val) && Is_young(new_val)) {

      /* If old_val is young, then `Op_val(obj)+field` is already in
       * major_ref. We can safely skip adding it again. */
       if (Is_block(old_val) && Is_young(old_val))
         return;

      /* Add to remembered set */
      Ref_table_add(&domain_state->minor_tables->major_ref, Op_val(obj) + field);
    }
  } else if (Is_young(new_val) && new_val < obj) {

    /* Both obj and new_val are young and new_val is more recent than obj.
      * If old_val is also young, and younger than obj, then it must be the
      * case that `Op_val(obj)+field` is already in minor_ref. We can safely
      * skip adding it again. */
    if (Is_block(old_val) && Is_young(old_val) && old_val < obj)
      return;

    /* Add to remembered set */
    Ref_table_add(&domain_state->minor_tables->minor_ref, Op_val(obj) + field);
  }
}

CAMLexport void caml_modify_field (value obj, int field, value val)
{
  Assert (Is_block(obj));
  Assert (!Is_foreign(obj));
  Assert (!Is_block(val) || Wosize_hd (Hd_val (val)) < (1 << 20)); /* !! */

  Assert(field >= 0 && field < Wosize_val(obj));

  write_barrier(obj, field, Op_val(obj)[field], val);
#if defined(COLLECT_STATS) && defined(NATIVE_CODE)
  Caml_state->mutable_stores++;
#endif
  __atomic_exchange_n(&Op_val(obj)[field], val, __ATOMIC_SEQ_CST);
  //Op_val(obj)[field] = val;
}

CAMLexport void caml_initialize_field (value obj, int field, value val)
{
  Assert(Is_block(obj));
  Assert(!Is_foreign(obj));
  Assert(0 <= field && field < Wosize_val(obj));
#ifdef DEBUG
  /* caml_initialize_field can only be used on just-allocated objects */
  if (Is_young(obj))
    Assert(Op_val(obj)[field] == Debug_uninit_minor ||
           Op_val(obj)[field] == Val_unit);
  else
    Assert(Op_val(obj)[field] == Debug_uninit_major ||
           Op_val(obj)[field] == Val_unit);
#endif

  if (!Is_young(obj) && Is_young(val)) {
    Begin_root(obj);
    val = caml_promote(caml_domain_self(), val);
    End_roots();
  }
  write_barrier(obj, field, Op_val(obj)[field], val);
  Op_val(obj)[field] = val;
}

CAMLexport int caml_atomic_cas_field (value obj, int field, value oldval, value newval)
{
  value* p = &Op_val(obj)[field];
  if (Is_young(obj) || caml_domain_alone()) {
    /* non-atomic CAS since only this thread can access the object */
    if (*p == oldval) {
      *p = newval;
      write_barrier(obj, field, oldval, newval);
      return 1;
    } else {
      return 0;
    }
  } else {
    /* need a real CAS */
    if (__sync_bool_compare_and_swap(p, oldval, newval)) {
      write_barrier(obj, field, oldval, newval);
      return 1;
    } else {
      return 0;
    }
  }
}


/* FIXME: is __sync_synchronize a C11 SC fence? Is that enough? */

CAMLprim value caml_atomic_load (value ref)
{
  if (Is_young(ref)) {
    return Op_val(ref)[0];
  } else {
    CAMLparam1(ref);
    CAMLlocal1(v);
    __sync_synchronize();
    caml_read_field(ref, 0, &v);
    __sync_synchronize();
    CAMLreturn (v);
  }
}

CAMLprim value caml_atomic_store (value ref, value v)
{
  __sync_synchronize();
  caml_modify_field(ref, 0, v);
  __sync_synchronize();
  return Val_unit;
}

CAMLprim value caml_atomic_cas (value ref, value oldv, value newv)
{
  value* p = Op_val(ref);
  if (Is_young(ref) || caml_domain_alone()) {
    if (*p == oldv) {
      *p = newv;
      write_barrier(ref, 0, oldv, newv);
      return Val_int(1);
    } else {
      return Val_int(0);
    }
  } else {
    int r = __sync_bool_compare_and_swap(p, oldv, newv);
    if (r) write_barrier(ref, 0, oldv, newv);
    return Val_int(r);
  }
}

int caml_atomic_cas_raw (value* p, value oldv, value newv)
{
  if (caml_domain_alone()) {
    if (*p == oldv) {
      *p = newv;
      return 1;
    } else {
      return 0;
    }
  } else {
    return __sync_bool_compare_and_swap(p, oldv, newv);
  }
}

CAMLexport void caml_set_fields (value obj, value v)
{
  int i;
  Assert (Is_block(obj));

  for (i = 0; i < Wosize_val(obj); i++) {
    caml_modify_field(obj, i, v);
  }
}

CAMLexport void caml_blit_fields (value src, int srcoff, value dst, int dstoff, int n)
{
  CAMLparam2(src, dst);
  CAMLlocal1(x);
  int i;
  Assert(Is_block(src));
  Assert(Is_block(dst));
  Assert(srcoff + n <= Wosize_val(src));
  Assert(dstoff + n <= Wosize_val(dst));
  Assert(Tag_val(src) != Infix_tag);
  Assert(Tag_val(dst) != Infix_tag);

  /* we can't use memcpy/memmove since they may not do atomic word writes.
     for instance, they may copy a byte at a time */
  if (src == dst && srcoff < dstoff) {
    /* copy descending */
    if (Is_young(dst)) {
      /* dst is young, we copy fields directly. This cannot create old->young
         ptrs, nor break incremental GC of the shared heap */
      for (i = n; i > 0; i--) {
        Op_val(dst)[dstoff + i - 1] = Op_val(src)[srcoff + i - 1];
      }
    } else {
      for (i = n; i > 0; i--) {
        caml_read_field(src, srcoff + i - 1, &x);
        caml_modify_field(dst, dstoff + i - 1, x);
      }
    }
  } else {
    /* copy ascending */
    if (Is_young(dst)) {
      /* see comment above */
      for (i = 0; i < n; i++) {
        caml_read_field(src, srcoff + i, &x);
        Op_val(dst)[dstoff + i] = x;
      }
    } else {
      for (i = 0; i < n; i++) {
        caml_read_field(src, srcoff + i, &x);
        caml_modify_field(dst, dstoff + i, x);
      }
    }
  }
  CAMLreturn0;
}

CAMLexport value caml_alloc_shr (mlsize_t wosize, tag_t tag)
{
  caml_domain_state* dom_st = Caml_state;
  value* v = caml_shared_try_alloc(dom_st->shared_heap, wosize, tag, 0);
  if (v == NULL) {
    caml_raise_out_of_memory ();
  }
  dom_st->allocated_words += Whsize_wosize (wosize);
  if (dom_st->allocated_words > Wsize_bsize (dom_st->minor_heap_size)) {
    caml_urge_major_slice();
  }

  if (tag < No_scan_tag) {
    mlsize_t i;
    for (i = 0; i < wosize; i++) {
      value init_val = Val_unit;
      #ifdef DEBUG
      init_val = Debug_uninit_major;
      #endif
      Op_hp(v)[i] = init_val;
    }
  }
#if defined(COLLECT_STATS) && defined(NATIVE_CODE)
  dom_st->allocations++;
#endif
  return Val_hp(v);
}

struct read_fault_req {
  value obj;
  int field;
  value* ret;
};

static void send_read_fault(struct read_fault_req*);

static void handle_read_fault(struct domain* target, void* reqp, interrupt* done) {
  struct read_fault_req* req = reqp;
  value v = Op_val(req->obj)[req->field];
  if (Is_minor(v) && caml_owner_of_young_block(v) == target) {
    // caml_gc_log("Handling read fault for domain [%02d]", target->id);
    *req->ret = caml_promote(target, v);
    Assert (!Is_minor(req->ret));
    /* Update the field so that future requests don't fault. We must
       use a CAS here, since another thread may modify the field and
       we must avoid overwriting its update */
    caml_atomic_cas_field(req->obj, req->field, v, *req->ret);
  } else {
    /* Race condition: by the time we handled the fault, the field was
       already modified and no longer points to our heap.  We recurse
       into the read barrier. This always terminates: in the worst
       case, all domains get tied up servicing one fault and then
       there are no more left running to win the race */
    // caml_gc_log("Stale read fault for domain [%02d]", target->id);
    send_read_fault(req);
  }
  caml_acknowledge_interrupt(done);
}

static void send_read_fault(struct read_fault_req* req)
{
  value v = Op_val(req->obj)[req->field];
  if (Is_minor(v)) {
    // caml_gc_log("Read fault to domain [%02d]", caml_owner_of_young_block(v)->id);
    if (!caml_domain_rpc(caml_owner_of_young_block(v), &handle_read_fault, req)) {
      send_read_fault(req);
    }
    Assert(!Is_minor(*req->ret));
    // caml_gc_log("Read fault returned (%p)", (void*)req->ret);
  } else {
    // caml_gc_log("Stale read fault: already promoted");
    *req->ret = v;
  }
}

CAMLexport value caml_read_barrier(value obj, int field)
{
  /* A GC may occur just before or just after sending a fault.
     The obj and ret values must be roots, because if a GC occurs
     just after a fault is handled they must be preserved.
     The orig value must *not* be a root, since it may contain
     a foreign value, which the GC must not see even if it runs
     just before the fault is handled. */
  CAMLparam1(obj);
  CAMLlocal1(ret);
  value orig = Op_val(obj)[field];
  if (Is_foreign(orig)) {
    struct read_fault_req req = {obj, field, &ret};
    caml_ev_begin("fault/read");
    send_read_fault(&req);
    caml_ev_end("fault/read");
    Assert (!Is_foreign(ret));
  } else {
    ret = orig;
  }
  CAMLreturn (ret);
}

#ifdef DEBUG
header_t hd_val (value v) {
  return (header_t)Hd_val(v);
}

int is_minor(value v) {
  return Is_minor(v);
}

int is_foreign(value v) {
  return Is_foreign(v);
}

int is_young(value v) {
  return Is_young(v);
}

int has_status(value v, status s) {
  return Has_status_hd(Hd_val(v),s);
}

int tag_val(value v) {
  return (int)Tag_val(v);
}
#endif

/* Global memory pool.

   The pool is structured as a ring of blocks, where each block's header
   contains two links: to the previous and to the next block. The data
   structure allows for insertions and removals of blocks in constant time,
   given that a pointer to the operated block is provided.

   Initially, the pool contains a single block -- a pivot with no data, the
   guaranteed existence of which makes for a more concise implementation.

   The API functions that operate on the pool receive not pointers to the
   block's header, but rather pointers to the block's "data" field. This
   behaviour is required to maintain compatibility with the interfaces of
   [malloc], [realloc], and [free] family of functions, as well as to hide
   the implementation from the user.
*/

/* A type with the most strict alignment requirements */
union max_align {
  char c;
  short s;
  long l;
  int i;
  float f;
  double d;
  void *v;
  void (*q)(void);
};

struct pool_block {
#ifdef DEBUG
  long magic;
#endif
  struct pool_block *next;
  struct pool_block *prev;
  union max_align data[1];  /* not allocated, used for alignment purposes */
};

#define SIZEOF_POOL_BLOCK offsetof(struct pool_block, data)

static struct pool_block *pool = NULL;
static caml_plat_mutex pool_mutex = CAML_PLAT_MUTEX_INITIALIZER;

/* Returns a pointer to the block header, given a pointer to "data" */
static struct pool_block* get_pool_block(caml_stat_block b)
{
  if (b == NULL)
    return NULL;

  else {
    struct pool_block *pb =
      (struct pool_block*)(((char*)b) - SIZEOF_POOL_BLOCK);
#ifdef DEBUG
    CAMLassert(pb->magic == Debug_pool_magic);
#endif
    return pb;
  }
}

CAMLexport void caml_stat_create_pool(void)
{
  if (pool == NULL) {
    pool = malloc(SIZEOF_POOL_BLOCK);
    if (pool == NULL)
      caml_fatal_error("Fatal error: out of memory.\n");
#ifdef DEBUG
    pool->magic = Debug_pool_magic;
#endif
    pool->next = pool;
    pool->prev = pool;
  }
}

CAMLexport void caml_stat_destroy_pool(void)
{
  caml_plat_lock(&pool_mutex);
  if (pool != NULL) {
    pool->prev->next = NULL;
    while (pool != NULL) {
      struct pool_block *next = pool->next;
      free(pool);
      pool = next;
    }
    pool = NULL;
  }
  caml_plat_unlock(&pool_mutex);
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_alloc_noexc(asize_t sz)
{
  /* Backward compatibility mode */
  if (pool == NULL)
    return malloc(sz);
  else {
    struct pool_block *pb = malloc(sz + SIZEOF_POOL_BLOCK);
    if (pb == NULL) return NULL;
#ifdef DEBUG
    memset(&(pb->data), Debug_uninit_stat, sz);
    pb->magic = Debug_pool_magic;
#endif

    /* Linking the block into the ring */
    caml_plat_lock(&pool_mutex);
    pb->next = pool->next;
    pb->prev = pool;
    pool->next->prev = pb;
    pool->next = pb;
    caml_plat_unlock(&pool_mutex);

    return &(pb->data);
  }
}

/* [sz] and [modulo] are numbers of bytes */
CAMLexport void* caml_stat_alloc_aligned_noexc(asize_t sz, int modulo,
                                               caml_stat_block *b)
{
  char *raw_mem;
  uintnat aligned_mem;
  CAMLassert (modulo < Page_size);
  raw_mem = (char *) caml_stat_alloc_noexc(sz + Page_size);
  if (raw_mem == NULL) return NULL;
  *b = raw_mem;
  raw_mem += modulo;                /* Address to be aligned */
  aligned_mem = (((uintnat) raw_mem / Page_size + 1) * Page_size);
#ifdef DEBUG
  {
    uintnat *p;
    uintnat *p0 = (void *) *b;
    uintnat *p1 = (void *) (aligned_mem - modulo);
    uintnat *p2 = (void *) (aligned_mem - modulo + sz);
    uintnat *p3 = (void *) ((char *) *b + sz + Page_size);
    for (p = p0; p < p1; p++) *p = Debug_filler_align;
    for (p = p1; p < p2; p++) *p = Debug_uninit_align;
    for (p = p2; p < p3; p++) *p = Debug_filler_align;
  }
#endif
  return (char *) (aligned_mem - modulo);
}

/* [sz] and [modulo] are numbers of bytes */
CAMLexport void* caml_stat_alloc_aligned(asize_t sz, int modulo,
                                         caml_stat_block *b)
{
  void *result = caml_stat_alloc_aligned_noexc(sz, modulo, b);
  /* malloc() may return NULL if size is 0 */
  if ((result == NULL) && (sz != 0))
    caml_raise_out_of_memory();
  return result;
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_alloc(asize_t sz)
{
  void *result = caml_stat_alloc_noexc(sz);
  /* malloc() may return NULL if size is 0 */
  if ((result == NULL) && (sz != 0))
    caml_raise_out_of_memory();
  return result;
}

CAMLexport void caml_stat_free(caml_stat_block b)
{
  /* Backward compatibility mode */
  if (pool == NULL)
    free(b);
  else {
    struct pool_block *pb = get_pool_block(b);
    if (pb == NULL) return;

    /* Unlinking the block from the ring */
    caml_plat_lock(&pool_mutex);
    pb->prev->next = pb->next;
    pb->next->prev = pb->prev;
    caml_plat_unlock(&pool_mutex);

    free(pb);
  }
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_resize_noexc(caml_stat_block b, asize_t sz)
{
  /* Backward compatibility mode */
  if (pool == NULL)
    return realloc(b, sz);
  else {
    struct pool_block *pb = get_pool_block(b);
    struct pool_block *pb_new = realloc(pb, sz + SIZEOF_POOL_BLOCK);
    if (pb_new == NULL) return NULL;

    /* Relinking the new block into the ring in place of the old one */
    caml_plat_lock(&pool_mutex);
    pb_new->prev->next = pb_new;
    pb_new->next->prev = pb_new;
    caml_plat_unlock(&pool_mutex);

    return &(pb_new->data);
  }
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_resize(caml_stat_block b, asize_t sz)
{
  void *result = caml_stat_resize_noexc(b, sz);
  if (result == NULL)
    caml_raise_out_of_memory();
  return result;
}

/* [sz] is a number of bytes */
CAMLexport caml_stat_block caml_stat_calloc_noexc(asize_t num, asize_t sz)
{
  uintnat total;
  if (caml_umul_overflow(sz, num, &total))
    return NULL;
  else {
    caml_stat_block result = caml_stat_alloc_noexc(total);
    if (result != NULL)
      memset(result, 0, total);
    return result;
  }
}

CAMLexport caml_stat_string caml_stat_strdup_noexc(const char *s)
{
  size_t slen = strlen(s);
  caml_stat_block result = caml_stat_alloc_noexc(slen + 1);
  if (result == NULL)
    return NULL;
  memcpy(result, s, slen + 1);
  return result;
}

CAMLexport caml_stat_string caml_stat_strdup(const char *s)
{
  caml_stat_string result = caml_stat_strdup_noexc(s);
  if (result == NULL)
    caml_raise_out_of_memory();
  return result;
}

#ifdef _WIN32

CAMLexport wchar_t * caml_stat_wcsdup(const wchar_t *s)
{
  int slen = wcslen(s);
  wchar_t* result = caml_stat_alloc((slen + 1)*sizeof(wchar_t));
  if (result == NULL)
    caml_raise_out_of_memory();
  memcpy(result, s, (slen + 1)*sizeof(wchar_t));
  return result;
}

#endif

CAMLexport caml_stat_string caml_stat_strconcat(int n, ...)
{
  va_list args;
  char *result, *p;
  size_t len = 0;
  int i;

  va_start(args, n);
  for (i = 0; i < n; i++) {
    const char *s = va_arg(args, const char*);
    len += strlen(s);
  }
  va_end(args);

  result = caml_stat_alloc(len + 1);

  va_start(args, n);
  p = result;
  for (i = 0; i < n; i++) {
    const char *s = va_arg(args, const char*);
    size_t l = strlen(s);
    memcpy(p, s, l);
    p += l;
  }
  va_end(args);

  *p = 0;
  return result;
}

#ifdef _WIN32

CAMLexport wchar_t* caml_stat_wcsconcat(int n, ...)
{
  va_list args;
  wchar_t *result, *p;
  size_t len = 0;
  int i;

  va_start(args, n);
  for (i = 0; i < n; i++) {
    const wchar_t *s = va_arg(args, const wchar_t*);
    len += wcslen(s);
  }
  va_end(args);

  result = caml_stat_alloc((len + 1)*sizeof(wchar_t));

  va_start(args, n);
  p = result;
  for (i = 0; i < n; i++) {
    const wchar_t *s = va_arg(args, const wchar_t*);
    size_t l = wcslen(s);
    memcpy(p, s, l*sizeof(wchar_t));
    p += l;
  }
  va_end(args);

  *p = 0;
  return result;
}

#endif
