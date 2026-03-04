(*
 * This is the core entry point of the kernel, containing type inference,
 * reduction, definitional equality, and other functions relevant to basic
 * kernel functionality.
 *)
open Term

(* Substitution *)
val subst_bvar : term -> int -> term -> term

(* Conversion of free variables to bound variables *)
val rebind_bvar : term -> int -> string -> term 

(* Reduce a term to normal form *)
val reduce : environment -> localcontext -> term -> term

(* Determine if a term is a Sort *)
val isSort : environment -> term -> bool

(* Definitional equality: reduce and check exact equality *)
val isDefEq : environment -> localcontext -> term -> term -> bool

(* Core type inference algorithm. When this fails, throws a TypeError. *)
val inferType : environment -> localcontext -> term -> term


