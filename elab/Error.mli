(** Error types and reporting for the elaborator. *)

open Term

type error_context = {
  loc : range option;  (** Source location of the offending term, if available. *)
  decl_name : string option;
      (** Name of the declaration being processed when the error occurred, if known. *)
}
(** Location and declaration context attached to every error. *)

type parse_error_info = {
  input : string;  (** The source text that could not be parsed. *)
  error_msg : string;  (** The error message produced by the parser. *)
}
(** Payload for a parse failure. *)

type type_mismatch_info = {
  term : term;  (** The term whose type was checked. *)
  inferred_type : term;  (** The type that was inferred for [term]. *)
  expected_type : term;  (** The type that [term] was required to have. *)
}
(** Payload for a type-mismatch error. *)

type kernel_error_info = {
  kernel_exn : Kernel.Exceptions.type_error_info;
      (** The raw error record produced by the kernel. *)
}
(** Payload for an error originating in the trusted kernel. *)

type unknown_name_info = { name : string  (** The name that could not be resolved. *) }
(** Payload for an unbound-name error. *)

type function_expected_info = {
  not_func : term;  (** The term that was applied as if it were a function. *)
  not_func_type : term;  (** The inferred type of [not_func]. *)
  arg : term;  (** The argument that was passed to [not_func]. *)
}
(** Payload for a function-expected error. *)

type type_expected_info = {
  not_type : term;  (** The term that was used in a type position. *)
  not_type_infer : term;  (** The inferred type of [not_type]. *)
}
(** Payload for a type-expected error. *)

(** The type of error raised in an ElabError. *)
type error_type =
  | ParseError of parse_error_info
      (** The input failed to parse; carries the offending source text and the parser's
          error message. *)
  | AlreadyDefined of string
      (** A declaration with this name was already added to the environment. *)
  | TypeMismatch of type_mismatch_info
      (** A term's inferred type does not match its expected type. *)
  | CannotInferHole
      (** A hole ([_]) was encountered that could not be solved or its type inferred. *)
  | KernelError of kernel_error_info
      (** The trusted kernel rejected a term; wraps the kernel's own error info. *)
  | UnknownName of unknown_name_info
      (** A name was used that is not bound in the current environment. *)
  | InternalError of string
      (** An invariant was violated inside the elaborator; indicates a bug. *)
  | FunctionExpected of function_expected_info
      (** A non-function term was applied to an argument. *)
  | TypeExpected of type_expected_info
      (** A term that is not a type was used in a position that requires a type. *)

type elab_error_info = {
  context : error_context;  (** Source location and declaration context of the error. *)
  error_type : error_type;  (** The specific kind of error that occurred. *)
}
(** The complete error record raised by the elaborator. *)

exception ElabError of elab_error_info
(** Exception raised for any elaboration-level error. *)

val pp_exn : Types.ctx -> elab_error_info -> string
(** [pp_exn ctx info] formats [info] as a human-readable error message, using [ctx] to
    pretty-print any terms that appear in the error. *)
