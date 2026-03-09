(** Error types and reporting for the elaborator. *)

open Term

type error_context = {
  loc : range option;
  decl_name : string option;
}
(** Location and declaration context attached to every error. *)

type parse_error_info = {
  input : string;
  error_msg : string;
}

type type_mismatch_info = {
  term : term;
  inferred_type : term;
  expected_type : term;
}

type kernel_error_info = { kernel_exn : Kernel.Exceptions.type_error_info }
type unknown_name_info = { name : string }

type function_expected_info = {
  not_func : term;
  not_func_type : term;
  arg : term;
}

type type_expected_info = {
  not_type : term;
  not_type_infer : term;
}

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
  context : error_context;
  error_type : error_type;
}

exception ElabError of elab_error_info

val pp_exn : Types.ctx -> elab_error_info -> string
(** Format a complete elaboration error for display. *)
