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

(*
 * Types of reduction errors
 * (Note there is only one for now because the kernel does not raise others,
 * but this will likely change.)
 *)
type red_error_kind =
  | AppArgRedError 

(* 
 * Reduction error information
 *)
type red_error_info =
  {
    env : environment;
    ctx : localcontext;
    trm : term;
    err_kind : red_error_kind
  }

(* Exceptions that the kernel may raise, using the above information *)
exception TypeError of type_error_info
exception RedError of red_error_info

(* --- Printing errors ---*)

(*
 * In the long run, all of the funny string business here will move outside
 * of the kernel, ideally into the elaborator. This will require interfacing
 * with the yellow team. For now, for backwards compatibility, I include all
 * of the old stirng conversion behavior here. Ideally, after interfacing
 * with yellow, none of the below code will live in the kernel at all.
 *)

(*
 * Convert a term to a string
 *)
let rec term_to_string (t : term) : string =
  match t with
  | Const name -> name
  | Sort level -> "Sort " ^ string_of_int level
  | Fvar name -> name
  | Bvar idx -> "Bvar " ^ string_of_int idx
  | Lam (dom, body) -> "fun " ^ term_to_string dom ^ " => (" ^ term_to_string body ^ ")"
  | Forall (dom, body) -> term_to_string dom ^ " -> " ^ term_to_string body
  | App (f, a) -> "(" ^ term_to_string f ^ " " ^ term_to_string a ^ ")"

(*
 * Convert a local context to a string
 *)
let context_to_string (ctx : localcontext) : string =
  Hashtbl.fold (fun k v acc -> acc ^ k ^ " : " ^ term_to_string v ^ "\n") ctx ""

(*
 * Convert a type error to a string for printing
 *)
let type_err_to_string (info : type_error_info) : string =
  match info.err_kind with
  | UnknownConstError name -> "unknown constant: " ^ name
  | UnknownFreeVarError name -> "unknown free variable: " ^ name
  | BoundVarScopeError idx ->
     "bound variable index out of scope: " ^ string_of_int idx
  | AppArgTypeError (f, a, f_type, expected_a_type, inferred_a_type) ->
      Printf.sprintf 
        "Function called with invalid argument type.\n\
         Local Context:\n%s\n\
         Term: %s\n\
         Func: %s\n\
         Arg: %s\n\n\
         Func Type: %s\n\
         Expected Arg Type: %s\n\
         Inferred Arg Type: %s\n"
        (context_to_string info.ctx)
        (term_to_string info.trm)
        (term_to_string f)
        (term_to_string a)
        (term_to_string f_type)
        (term_to_string expected_a_type)
        (term_to_string inferred_a_type)
  | AppNonFuncError ->
     "Tried to apply non-function to an argument"
  | LamDomainError ->
     "Invalid domain type for lambda"
  | ForallSortError (domainTypeType, returnTypeType) ->
      Printf.sprintf 
        "Domain and return types of a Forall must be sorts.\n\
         Local Context:\n%s\n\
         Term: %s\n\
         Domain Type Sort: %s\n\
         Return Type Sort: %s\n\n"
        (context_to_string info.ctx)
        (term_to_string info.trm)
        (term_to_string domainTypeType)
        (term_to_string returnTypeType)

(*
 * Convert a reduction error to a string for printing
 *)
let red_err_to_string (info : red_error_info) : string =
  match info.err_kind with
  | AppArgRedError ->
     "Function called with invalid argument type during reduction"
