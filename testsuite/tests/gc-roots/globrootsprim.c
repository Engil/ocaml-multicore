/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 2001 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* For testing global root registration */

#include "caml/mlvalues.h"
#include "caml/memory.h"
#include "caml/alloc.h"
#include "caml/gc.h"
#include "caml/callback.h"

struct block { value header; caml_root v; };

#define Root_val(v) *((caml_root*) Data_abstract_val(v))

value gb_get(value vblock)
{
  CAMLparam1 (vblock);
  CAMLreturn (caml_read_root(Root_val(vblock)));
}

value gb_classic_register(value v)
{
  CAMLparam1(v);
  CAMLlocal1(b);
  caml_root r;
  b = caml_alloc(1, Abstract_tag);
  r = caml_create_root(v);
  Root_val(b) = r;
  CAMLreturn (b);
}

value gb_classic_set(value vblock, value newval)
{
  CAMLparam2(vblock, newval);
  caml_modify_root(Root_val(vblock), newval);
  CAMLreturn (Val_unit);
}

value gb_classic_remove(value vblock)
{
  CAMLparam1(vblock);
  caml_delete_root(Root_val(vblock));
  CAMLreturn (Val_unit);
}

value gb_generational_register(value v)
{
  return gb_classic_register(v);
}

value gb_generational_set(value vblock, value newval)
{
  return gb_classic_set(vblock, newval);
}

value gb_generational_remove(value vblock)
{
  return gb_classic_remove(vblock);
}

value gb_static2young(value static_value, value full_major) {
  CAMLparam2 (static_value, full_major);
  CAMLlocal1(v);
  int i;

  root = Val_unit;
  caml_register_generational_global_root(&root);

  /* Write a static value in the root. */
  caml_modify_generational_global_root(&root, static_value);

  /* Overwrite it with a young value. */
  v = caml_alloc_small(1, 0);
  Field(v, 0) = Val_long(0x42);
  caml_modify_generational_global_root(&root, v);

  /* Promote the young value */
  caml_callback(full_major, Val_unit);

  /* Fill the minor heap to make sure the old block is overwritten */
  for(i = 0; i < 1000000; i++)
    caml_alloc_small(1, 0);

  v = Field(root, 0);
  caml_remove_generational_global_root(&root);

  CAMLreturn(v);
}
