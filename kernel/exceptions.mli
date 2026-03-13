(** This file contains the kernel-side exception types, to be passed to the elaborator for
    processing. *)
open Term

(* --- Exception types --- *)

(** Kinds of type errors that the kernel can throw. *)
type type_error_kind =
  | UnknownConstError of string
      (** [UnknownConstError(name)] indicates an unknown constant [name]. *)
  | UnknownFreeVarError of string
      (** [UnknownFreeVarError(name)] indicates an unknown free variable [name]. *)
  | BoundVarScopeError of int
      (** [BoundVarScopeError(idx)] indicates a bound variable scope error at index [idx].
      *)
  | AppArgTypeError of term * term * term * term * term
      (** [AppArgTypeError(func, arg, func_type, expected_arg_type, actual_arg_type)]
          indicates a type error in the argument of a function application. *)
  | AppNonFuncError of term
      (** [AppNonFuncError(func_type)] indicates an attempt to apply with a non-function
          term. *)
  | LamDomainError of term
      (** [LamDomainError(domain_type_type)] indicates that the domain of a lambda
          abstraction is not a valid type. *)
  | ForallSortError of term * term
      (** [ForallSortError(domain_type_type, return_type_type)] indicates that either the
          domain type or the return type is not a valid sort. *)
  | AlreadyDefined of string
      (** [AlreadyDefined(name)] indicates an attempt to declare a name that is already
          defined in the environment. *)
  | DeclarationTypeError of term
      (** [DeclarationTypeError(decl_type)] indicates that the type of a declaration is
          not a valid sort. *)
  | ProofTypeMismatch of term * term
      (** [ProofTypeMismatch(expected, actual)] indicates that a proof term has an
          unexpected type. *)

(** Type error information that the kernel passes on. *)
type type_error_info = {
  env : environment;
  ctx : localcontext;
  trm : term;
  err_kind : type_error_kind;
}

(** Exceptions that the kernel may raise, using the above information. *)
exception TypeError of type_error_info
