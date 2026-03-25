(** Error types and reporting for the elaborator. *)

open Term

(** Location and declaration context attached to every error. *)
type error_context = {
  loc : range option;  (** Source location of the offending term, if available. *)
  decl_name : string option;
      (** Name of the declaration being processed when the error occurred, if known. *)
  term_name : string option;  (** Name of the nearest useful term/binder, if known. *)
}

(** Payload for a parse failure. *)
type parse_error_info = {
  input : string;  (** The source text that could not be parsed. *)
  error_msg : string;  (** The error message produced by the parser. *)
}

(** Payload for a type-mismatch error. *)
type type_mismatch_info = {
  term : term;  (** The term whose type was checked. *)
  inferred_type : term;  (** The type that was inferred for [term]. *)
  expected_type : term;  (** The type that [term] was required to have. *)
}

(** Payload for an error originating in the trusted kernel. *)
type kernel_error_info = {
  kernel_exn : Kernel.Exceptions.type_error_info;
      (** The raw error record produced by the kernel. *)
}

(** Payload for an unbound-name error. *)
type unknown_name_info = { name : string  (** The name that could not be resolved. *) }

(** Payload for a function-expected error. *)
type function_expected_info = {
  not_func : term;  (** The term that was applied as if it were a function. *)
  not_func_type : term;  (** The inferred type of [not_func]. *)
  arg : term;  (** The argument that was passed to [not_func]. *)
}

(** Payload for a type-expected error. *)
type type_expected_info = {
  not_type : term;  (** The term that was used in a type position. *)
  not_type_infer : term;  (** The inferred type of [not_type]. *)
}

(** Payload for a unification failure. *)
type unification_failure_info = {
  left : term;  (** Left-hand side of the failed unification. *)
  right : term;  (** Right-hand side of the failed unification. *)
}

(** The type of error raised in an [ElabError]. *)
type error_type =
  | ParseError of parse_error_info
      (** [ParseError(info)] indicated a parsing failure. [info] carries the offending
          source and the error message. *)
  | AlreadyDefined of string
      (** [AlreadyDefined(name)] indicates that a declaration [name] already exists in the
          environment. *)
  | TypeMismatch of type_mismatch_info
      (** [TypeMismatch(info)] indicates a type mismatch. [info] carries details about the
          term, its inferred type, and the expected type. *)
  | CannotInferHole
      (** [CannotInferHole] indicates that a hole ([_]) was encountered that could not be
          solved or its type inferred. *)
  | KernelError of kernel_error_info
      (** [KernelError(info)] indicates that the trusted kernel rejected a term. [info]
          contains the error received from the kernel. *)
  | UnknownName of unknown_name_info
      (** [UnknownName(info)] indicates that a name was used that is not bound in the
          current environment. [info] carries the unknown name. *)
  | InternalError of string
      (** [InternalError(info)] indicates that an invariant was violated inside the
          elaborator (indicates a bug). *)
  | FunctionExpected of function_expected_info
      (** [FunctionExpected(info)] indicates that a non-function term was applied to an
          argument. [info] carries details about the term, its type and the argument. *)
  | TypeExpected of type_expected_info
      (** [TypeExpected(info)] indicates that a non-type term was used in a position that
          requires a type. [info] carries details about the term and its type. *)
  | UnificationFailure of unification_failure_info

(** The complete error record raised by the elaborator. *)
type elab_error_info = {
  context : error_context;  (** Source location and declaration context of the error. *)
  error_type : error_type;  (** The specific kind of error that occurred. *)
}

(** Exception raised for any elaboration-level error. *)
exception ElabError of elab_error_info

(** [pp_exn ctx info] formats [info] as a human-readable error message, using [ctx] to
    pretty-print any terms that appear in the error. *)
val pp_exn : Types.ctx -> elab_error_info -> string
