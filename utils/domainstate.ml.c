
#define CAML_CONFIG_H_NO_TYPEDEFS
#include "config.h"
let minor_heap_sel_bits = Minor_heap_sel_bits
let minor_heap_align_bits = Minor_heap_align_bits
let stack_ctx_words = Stack_ctx_words

type t =
#define DOMAIN_STATE(type, name) | Domain_##name
#include "domain_state.tbl"
#undef DOMAIN_STATE

let idx_of_field =
  let curr = 0 in
#define DOMAIN_STATE(type, name) \
  let idx__##name = curr in \
  let curr = curr + 1 in
#include "domain_state.tbl"
#undef DOMAIN_STATE
  let _ = curr in
  function
#define DOMAIN_STATE(type, name) \
  | Domain_##name -> idx__##name
#include "domain_state.tbl"
#undef DOMAIN_STATE
