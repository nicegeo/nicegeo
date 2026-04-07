(** This is the core entry point of the kernel, containing type inference, reduction,
    definitional equality, and other functions relevant to basic kernel functionality. *)
open Term

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
