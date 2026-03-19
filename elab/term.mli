(** Elaboration-level term representation. *)

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
  | Hole of int
      (** [Hole(idx)] represents a hole (underscore) to be filled by elaboration. [idx] is
          a unique id. *)
  | Fun of string option * int * term * term
  | Arrow of string option * int * term * term
  | App of term * term  (** [App(func, arg)] represents applying [func] to [arg]. *)
  | Sort of int
      (** [Sort(level)] represents a universe level. Sort 0 = Prop, Sort 1 = Type. *)

(** [gen_hole_id ()] generates a fresh hole id. *)
val gen_hole_id : unit -> int

val gen_binder_id : unit -> int
val subst : term -> term -> term -> term

(** [is_sort] returns [true] if the term is literally a [Sort _]. *)
val is_sort : term -> bool
