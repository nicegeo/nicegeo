open Term
(** This file contains the kernel-side exception types, to be passed to the elaborator for
    processing. *)

(* --- Exception types --- *)

(** Kinds of type errors that the kernel can throw.

    UnknownConstError: Unknown constant where the string encodes the name
    UnknownFreeVarError: Unknown free variable where the string encodes the name
    BoundVarScopeError: Bound variable scope error, where the int is the index
    AppArgTypeError: Type error for the argument of a function application, where the
    terms represent (1) the function, (2) the argument, (3) the type of the function, (4)
    the expected type of the argument, and (5) the actual type of the argument. *)
type type_error_kind =
  | UnknownConstError of string
  | UnknownFreeVarError of string
  | BoundVarScopeError of int
  | AppArgTypeError of term * term * term * term * term
  | AppNonFuncError
  | LamDomainError
  | ForallSortError of term * term

type type_error_info = {
  env : environment;
  ctx : localcontext;
  trm : term;
  err_kind : type_error_kind;
}
(** Type error information that the kernel passes on. *)

exception TypeError of type_error_info
(** Exceptions that the kernel may raise, using the above information. *)
