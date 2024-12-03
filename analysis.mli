(** Debloating analysis. *)

(** creates a new project containing debloated code. *)
val debloat: unit -> unit

(** checks whether a function might be called from the main entry point. *)
val function_called: Kernel_function.t -> bool
