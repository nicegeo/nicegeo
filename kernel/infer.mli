open Term
(** This is the core entry point of the kernel, containing type inference, reduction,
    definitional equality, and other functions relevant to basic kernel functionality. *)

(* Substitution *)
val subst_bvar : term -> int -> term -> term

(* Conversion of free variables to bound variables *)
val rebind_bvar : term -> int -> string -> term

val reduce : environment -> localcontext -> term -> term
(** Reduce a term to normal form *)

(* Determine if a term is a Sort *)
val isSort : environment -> term -> bool

val isDefEq : environment -> localcontext -> term -> term -> bool
(** Definitional equality: reduce and check exact equality *)

val inferType : environment -> localcontext -> term -> term
(** Core type inference algorithm. When this fails, throws a TypeError. *)
