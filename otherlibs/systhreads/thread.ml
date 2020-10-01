type t

external thread_initialize : unit -> unit = "caml_thread_initialize"

external thread_new : (unit -> unit) -> t = "caml_thread_new"

external thread_join : t -> unit = "caml_thread_join"

external self : unit -> t = "caml_thread_self" [@@noalloc]
external id : t -> int = "caml_thread_id" [@@noalloc]

external exit : unit -> unit = "caml_thread_exit"

external thread_yield : unit -> unit = "caml_thread_yield"

external thread_uncaught_exception : exn -> unit =
            "caml_thread_uncaught_exception"

let create fn arg =
  thread_new
    (fun () ->
      try
        fn arg; ()
      with exn ->
             flush stdout; flush stderr;
             thread_uncaught_exception exn)

let join = thread_join
let yield = thread_yield
let preempt signal = yield ()
let delay = Unix.sleepf

let () = thread_initialize ()

let kill th = invalid_arg "Thread.kill: not implemented"

let wait_read fd = ()
let wait_write fd = ()

let wait_timed_read fd d =
  match Unix.select [fd] [] [] d with ([], _, _) -> false | (_, _, _) -> true
let wait_timed_write fd d =
  match Unix.select [] [fd] [] d with (_, [], _) -> false | (_, _, _) -> true
let select = Unix.select

let wait_pid p = Unix.waitpid [] p

external sigmask : Unix.sigprocmask_command -> int list -> int list
   = "caml_thread_sigmask"
external wait_signal : int list -> int = "caml_wait_signal"
