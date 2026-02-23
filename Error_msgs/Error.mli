(* error.mli *)

type loc = {
  file : string;
  line : int;
  column  : int;
}

type error_context = {
  loc      : loc option;        (* where it happened *)
  decl_name     : string option;     (* declaration / theorem / def name *)
  term_name     : string option;     (* pretty-printed term, if available *)
  expected_type : string option;     (* expected type / goal, if available *)
  actual_type   : string option;     (* actual type, if available *)
  local_context   : (string * string) list; (* local context: x : A, y : B ... *)
  note     : string option;     (* extra hint *)
}

val empty_context : error_context
val with_loc : loc -> error_context -> error_context
val with_decl_name : string -> error_context -> error_context
val with_term_name : string -> error_context -> error_context
val with_expected_type : string -> error_context -> error_context
val with_actual_type : string -> error_context -> error_context
val with_local_context : (string * string) list -> error_context -> error_context
val with_note : string -> error_context -> error_context

exception TypeError of string * error_context
exception UnknownConstant of string * error_context
exception UnknownVariable of string * error_context
exception InvalidProof of string * error_context
exception ParseError of string * error_context
exception ElaboratorError of string * error_context
exception KernelError of string * error_context
exception InternalError of string * error_context

val raise_type_error : ?error_context:error_context -> string -> 'a
val raise_unknown_constant : ?error_context:error_context -> string -> 'a
val raise_unknown_variable : ?error_context:error_context -> string -> 'a
val raise_invalid_proof : ?error_context:error_context -> string -> 'a
val raise_parse_error : ?error_context:error_context -> string -> 'a
val raise_elab_error : ?error_context:error_context -> string -> 'a
val raise_kernel_error : ?error_context:error_context -> string -> 'a
val raise_internal : ?error_context:error_context -> string -> 'a

val add_ctx : error_context -> exn -> exn
val pp_loc : loc option -> string
val pp_kv : string -> string option -> string
val pp_locals : (string * string) list -> string

val pp_exn : exn -> string

(* convenience wrappers: replace failwith *)
val fail_type : ?error_context:error_context -> string -> 'a
val fail_kernel : ?error_context:error_context -> string -> 'a
val fail_elab : ?error_context:error_context -> string -> 'a
