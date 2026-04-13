(** This module includes the type definitions for kernel terms, as well as for the
    environment of constants and the local context. *)

(** Kernel representation of terms *)
type term =
  | Const of string  (** [Const(name)] represents a constant named [name]. *)
  | Bvar of int  (** [Bvar(idx)] represents a bound variable with index [idx]. *)
  | Fvar of string  (** [Fvar(name)] represents a free variable named [name]. *)
  | Lam of term * term  (** [Lam(domain_type, body)] represents a lambda abstraction. *)
  | Forall of term * term
      (** [Forall(domain_type, return_type)] represents a dependent function type. *)
  | App of term * term  (** [App(func, arg)] represents applying [func] to [arg]. *)
  | Sort of int  (** [Sort(level)] represents a universe level. **)

(** Maps constants to their types and definitions. *)
type environment = {
  types : (string, term) Hashtbl.t;
  defs : (string, term) Hashtbl.t;
}

(** Maps free variable names to their types *)
type localcontext = (string, term) Hashtbl.t
