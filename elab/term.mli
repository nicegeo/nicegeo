(** Elaboration-level term representation. Terms are represented in "binder id" form,
    which are like names but unique: every Fun and Arrow has an associated binder id, and
    a [Bvar id] refers to the variable bound with that id. They still also have the
    original source code name for error reporting. *)

(** Source location range. *)
type range = {
  start : Lexing.position;
  end_ : Lexing.position;
}

(** A dummy range for when no location information is available. *)
val dummy_range : range

(** Elaboration-level terms. *)
type term = {
  inner : termkind;  (** The kind of a term, along with its data. *)
  loc : range;  (** The source location (for precision in error messages). *)
}

(** The kind of a term. *)
and termkind =
  | Name of string
      (** [Name(name)] represents a name from the source (resolved to a constant or the
          nearest bound variable of the same name during parsing). *)
  | Bvar of int
      (** [Bvar(id)] represents a bound variable, referring to the binder with the same
          id. *)
  | Hole of int
      (** [Hole(idx)] represents a hole (underscore) to be filled by elaboration. [idx] is
          a unique id. *)
  | Fun of string option * int * term * term
      (** [Fun(arg_name, arg_id, arg_ty, body)] represents a function (lambda). [arg_name]
          is the optional original source name, [arg_id] is the binder id of the lambda,
          [arg_ty] is the type of the argument, and [body] is the body of the function.
          Any [Bvar arg_id] in [body] refers to this lambda's argument. *)
  | Arrow of string option * int * term * term
      (** [Arrow(arg_name, arg_id, arg_ty, ret_ty)] represents an arrow (Pi/function
          type). [arg_name] is the optional original source name, [arg_id] is the binder
          id of the argument, [arg_ty] is the type of the argument, and [ret_ty] is the
          return type. Any [Bvar arg_id] in [ret_ty] refers to this argument (and would be
          a dependent arrow). *)
  | App of term * term  (** [App(func, arg)] represents applying [func] to [arg]. *)
  | Sort of int
      (** [Sort(level)] represents a universe level. Sort 0 = Prop, Sort 1 = Type. *)

(** [gen_hole_id ()] generates a fresh hole id. *)
val gen_hole_id : unit -> int

(** [gen_binder_id ()] generates a fresh binder id. Aliased to [gen_hole_id]. *)
val gen_binder_id : unit -> int

(** [subst tm pat replacement] substitutes [replacement] for [pat] in [tm], if [pat] is a
    Name or Bvar. Note that this recurses into subterms but not into metavariable
    solutions. *)
val subst : term -> termkind -> termkind -> term

(** [uniquify_bids tm] generates fresh binder ids for all binders in [tm]. *)
val uniquify_bids : term -> term
