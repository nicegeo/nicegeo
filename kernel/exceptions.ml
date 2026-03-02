(*
 * This file contains the kernel-side exceptions.
 * The goal is for this to contain just the relevant information to
 * displaying exceptions related to kernel functionality like type
 * errors and reduction, but no funny string business.
 *)
open Term

(* --- Exception types --- *)

(*
 * Kinds of type errors
 * (Note that the details of these may change in the future as we improve
 * error messages, but this matches the old behavior for now)
 *)
type type_error_kind =
  | UnknownConstError of string
  | UnknownFreeVarError of string
  | BoundVarScopeError of int
  | AppArgTypeError of term * term * term * term * term
  | AppNonFuncError
  | LamDomainError
  | ForallSortError of term * term

(*
 * Type error information
 *)
type type_error_info =
  {
    env : environment;
    ctx : localcontext;
    trm : term;
    err_kind : type_error_kind
  }

(* Exceptions that the kernel may raise, using the above information *)
exception TypeError of type_error_info
