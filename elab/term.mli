(** Elaboration-level term representation. *)

(** Source location range. *)
type range = {
  start : Lexing.position;
  end_ : Lexing.position;
}

(** A dummy position for when no location information is available. *)
val dummy_pos : Lexing.position

(** A dummy range for when no location information is available. *)
val dummy_range : range

(** Elaboration-level terms. Contains location information for precision in error
    messages. *)
type term = {
  inner : termkind;
  loc : range;
}

(** Actual term variants. *)
and termkind =
  | Name of string
      (** A name as written in source code (resolved to a constant or the nearest bound
          variable of the same name during parsing). *)
  | Bvar of int  (** De Bruijn index for bound variables. *)
  | Fvar of int
      (** Free variable introduced during internal processing; the int is a unique id. *)
  | Hole of int
      (** A hole (underscore) to be filled by elaboration; the int is a unique id. *)
  | Fun of string option * term * term  (** [Fun(name, ty, body)]: lambda abstraction. *)
  | Arrow of string option * term * term
      (** [Arrow(name, ty, ret)]: dependent function type. *)
  | App of term * term  (** [App (f, arg)]: Function application. *)
  | Sort of int  (** Universe level. Sort 0 = Prop, Sort 1 = Type. *)

(** Generate a fresh unique hole id. *)
val gen_hole_id : unit -> int

(** Generate a fresh unique free-variable id. Alias for [gen_hole_id]. *)
val gen_fvar_id : unit -> int

(** [bind_bvar tm bvar_idx pat] replaces all occurrences of [pat] in [tm] with a reference
    to the bound variable at de Bruijn depth [bvar_idx]. *)
val bind_bvar : term -> int -> term -> term

(** [replace_bvar tm bvar_idx replacement] substitutes the bound variable at de Bruijn
    index [bvar_idx] (relative to the top of [tm]) with [replacement]. *)
val replace_bvar : term -> int -> term -> term

(** Returns [true] if the term is literally a [Sort _]. *)
val is_sort : term -> bool
