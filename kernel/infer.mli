(** This is the core entry point of the kernel, containing type inference, reduction,
    definitional equality, and other functions relevant to basic kernel functionality. *)
open Term

(** [reduce env ctx term] reduces a term to normal form *)
val reduce : environment -> localcontext -> term -> term

(** [isDefEq env ctx term1 term2] checks if two terms are definitionally equal *)
val isDefEq : environment -> localcontext -> term -> term -> bool

(** [inferType env ctx term] infers the type of a term. When this fails, throws a
    [TypeError]. *)
val inferType : environment -> localcontext -> term -> term

(** [add_theorem env name ty tm] Type-checks and adds a theorem to the environment,
    throwing a TypeError on failure. *)
val add_theorem : environment -> string -> term -> term -> unit

(** [add_axiom env name ty] Type-checks and adds an axiom to the environment, throwing a
    TypeError on failure. *)
val add_axiom : environment -> string -> term -> unit

(** The internal kernel functionality is exposed in an [Internals] module for testing
    purposes. These functions are not meant to be interacted with by non-kernel code
    otherwise, but OCaml does not have a good way to enforce this. *)
module Internals : sig
  (* Substitution *)
  val subst_bvar : term -> int -> term -> term

  (* Conversion of free variables to bound variables *)
  val rebind_bvar : term -> int -> string -> term

  (* Determine if a term is a Sort *)
  val isSort : environment -> term -> bool
end
