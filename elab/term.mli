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
      (** A name as written in source code (resolved to a constant or the nearest bound
          variable of the same name during parsing). *)
  | Bvar of int  (** De Bruijn index for bound variables. *)
  | Fvar of int
      (** Free variable introduced during internal processing; the int is a unique id. *)
  | Hole of int
      (** A hole (underscore) to be filled by elaboration; the int is a unique id. *)
  | Fun of string option * term * term
      (** A lambda abstraction, containing an optional parameter name, the input type, and
          the body. *)
  | Arrow of string option * term * term
      (** A dependent function type, containing an optional parameter name, the input
          type, and the return type. *)
  | App of term * term  (** Apply a term (ideally a function) to an argument. *)
  | Sort of int  (** Universe level. Sort 0 = Prop, Sort 1 = Type. *)

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
