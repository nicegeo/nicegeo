(** This is the core entry point of the kernel, allowing the addition of type-checked
    theorems and axioms into a kernel environment. *)
open Term

(** A kernel environment holds type-checked theorems and axioms. *)
type environment

(** [create ()] Creates a new, empty kernel environment. *)
val create : unit -> environment

(** [check_theorem env ty tm] Checks that [tm] has type [ty], throwing a TypeError on
    failure. *)
val check_theorem : environment -> term -> term -> unit

(** [add_theorem env name ty tm] Type-checks and adds a theorem to the environment,
    throwing a TypeError on failure. *)
val add_theorem : environment -> string -> term -> term -> unit

(** [add_axiom env name ty] Type-checks and adds an axiom to the environment, throwing a
    TypeError on failure. *)
val add_axiom : environment -> string -> term -> unit

(** [add_definition env name ty tm] Type-checks and adds a definition to the environment,
    throwing a TypeError on failure. *)
val add_definition : environment -> string -> term -> term -> unit

(** Returns a copy of the types registered in a kernel environment *)
val get_types : environment -> (string, term) Hashtbl.t

(** Returns a copy of the definition bodies registered in a kernel environment *)
val get_definitions : environment -> (string, term) Hashtbl.t

(** The internal kernel functionality is exposed in an [Internals] module for testing
    purposes. These functions are not meant to be interacted with by non-kernel code
    otherwise, but OCaml does not have a good way to enforce this. *)
module Internals : sig
  (** [reduce env ctx term] reduces a term to normal form *)
  val reduce : environment -> localcontext -> term -> term

  (** [isDefEq env ctx term1 term2] checks if two terms are definitionally equal *)
  val isDefEq : environment -> localcontext -> term -> term -> bool

  (** [inferType env ctx term] infers the type of a term. When this fails, throws a
      [TypeError]. *)
  val inferType : environment -> localcontext -> term -> term

  (* Substitution *)
  val subst_bvar : term -> int -> term -> term

  (* Conversion of free variables to bound variables *)
  val rebind_bvar : term -> int -> string -> term

  (* Determine if a term is a Sort *)
  val isSort : environment -> term -> bool
end
