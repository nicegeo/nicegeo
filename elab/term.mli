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
  | Bvar of int  (** [Bvar(idx)] represents a De Bruijn indexed bound variable. *)
  | Fvar of int
      (** [Fvar(idx)] represents a free variable (introduced during internal processing).
          [idx] is a unique id. *)
  | Hole of int
      (** [Hole(idx)] represents a hole (underscore) to be filled by elaboration. [idx] is
          a unique id. *)
  | Fun of string option * term * term
      (** [Fun(name, domain_type, body)] represents a lambda abstraction, where [name] is
          the optional parameter name. *)
  | Arrow of string option * term * term
      (** [Arrow(name, domain_type, return_type)] represents a dependent function type,
          where [name] is the optional parameter name. *)
  | App of term * term  (** [App(func, arg)] represents applying [func] to [arg]. *)
  | Sort of int
      (** [Sort(level)] represents a universe level. Sort 0 = Prop, Sort 1 = Type. *)

(** [gen_hole_id ()] generates a fresh hole id. *)
val gen_hole_id : unit -> int

(** [gen_fvar_id ()] generates a fresh free-variable id. Alias for [gen_hole_id]. *)
val gen_fvar_id : unit -> int

(** [bind_bvar tm bvar_idx pat] replaces all occurrences of [pat] in [tm] with a reference
    to the bound variable at de Bruijn depth [bvar_idx]. *)
val bind_bvar : term -> int -> term -> term

(** [replace_bvar tm bvar_idx replacement] substitutes the bound variable at de Bruijn
    index [bvar_idx] (relative to the top of [tm]) with [replacement]. *)
val replace_bvar : term -> int -> term -> term

(** [is_sort] returns [true] if the term is literally a [Sort _]. *)
val is_sort : term -> bool
