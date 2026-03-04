(**
   This module includes the type definitions for kernel terms, as well as for
   the environment of constants and the local context.
 *)

(** Kernel representation of terms *)
type term =
  | Const of string (* constants *)
  | Bvar of int (* bound variables *)
  | Fvar of string (* free variables *)
  | Lam of term * term (* functions *)
  | Forall of term * term (* function types *)
  | App of term * term (* function application *)
  | Sort of int (* sorts *)

(** Maps constants to their types *)
type environment = (string, term) Hashtbl.t

(** Maps free variable names to their types *)
type localcontext = (string, term) Hashtbl.t
