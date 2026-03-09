open Term
module KTerm = Kernel.Term
module KExceptions = Kernel.Exceptions

type error_context = {
  loc : range option; (* loc - where the error is happening *)
  decl_name : string option; (* decl_name - name of the declaration that caused the error *)
  term_name : string option; (* term_name - nearest useful term/binder if any *)
      
}

type parse_error_info = {
  input : string; (* the input that failed to parse *)
  error_msg : string; (* the error message from the parser *)
}

type type_mismatch_info = {
  term : term;
  inferred_type : term;
  expected_type : term;
}

type kernel_error_info = { kernel_exn : KExceptions.type_error_info }
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
  | AlreadyDefined of string
  | TypeMismatch of type_mismatch_info
  | CannotInferHole
  | KernelError of kernel_error_info
  | UnknownName of unknown_name_info
  | InternalError of string
  | FunctionExpected of function_expected_info
  | TypeExpected of type_expected_info

type elab_error_info = {
  context : error_context;
  error_type : error_type;
}

exception ElabError of elab_error_info

(* kernel error handling *)

(*
 * Convert a local context to a string
 *)
let context_to_string (ctx : KTerm.localcontext) : string =
  Hashtbl.fold
    (fun k v acc -> acc ^ k ^ " : " ^ Kernel_pretty.term_to_string_pretty v ^ "\n")
    ctx
    ""

(*
 * Convert a type error to a string for printing
 *)
let ktype_err_to_string (info : KExceptions.type_error_info) : string =
  match info.err_kind with
  | UnknownConstError name -> "unknown constant: " ^ name
  | UnknownFreeVarError name -> "unknown free variable: " ^ name
  | BoundVarScopeError idx -> "bound variable index out of scope: " ^ string_of_int idx
  | AppArgTypeError (f, a, f_type, expected_a_type, inferred_a_type) ->
      Printf.sprintf
        "Function called with invalid argument type.\n\
         Local Context:\n\
         %s\n\
         Term: %s\n\
         Func: %s\n\
         Arg: %s\n\n\
         Func Type: %s\n\
         Expected Arg Type: %s\n\
         Inferred Arg Type: %s\n"
        (context_to_string info.ctx)
        (Kernel_pretty.term_to_string_pretty info.trm)
        (Kernel_pretty.term_to_string_pretty f)
        (Kernel_pretty.term_to_string_pretty a)
        (Kernel_pretty.term_to_string_pretty f_type)
        (Kernel_pretty.term_to_string_pretty expected_a_type)
        (Kernel_pretty.term_to_string_pretty inferred_a_type)
  | AppNonFuncError -> "Tried to apply non-function to an argument"
  | LamDomainError -> "Invalid domain type for lambda"
  | ForallSortError (domainTypeType, returnTypeType) ->
      Printf.sprintf
        "Domain and return types of a Forall must be sorts.\n\
         Local Context:\n\
         %s\n\
         Term: %s\n\
         Domain Type Sort: %s\n\
         Return Type Sort: %s\n\n"
        (context_to_string info.ctx)
        (Kernel_pretty.term_to_string_pretty info.trm)
        (Kernel_pretty.term_to_string_pretty domainTypeType)
        (Kernel_pretty.term_to_string_pretty returnTypeType)

let pp_loc (r : range) =
  if r.start.pos_lnum = r.end_.pos_lnum then
    Printf.sprintf
      "%s:%d:%d-%d"
      r.start.pos_fname
      r.start.pos_lnum
      (r.start.pos_cnum - r.start.pos_bol + 1)
      (r.end_.pos_cnum - r.end_.pos_bol + 1)
  else
    Printf.sprintf
      "%s:%d:%d to %d:%d"
      r.start.pos_fname
      r.start.pos_lnum
      (r.start.pos_cnum - r.start.pos_bol + 1)
      r.end_.pos_lnum
      (r.end_.pos_cnum - r.end_.pos_bol + 1)

let pp_context (ctx : error_context) : string =
  let parts = ref [] in
  (match ctx.decl_name with
  | Some n -> parts := !parts @ [Printf.sprintf "in declaration '%s'" n]
  | None -> ());
  (match ctx.term_name with
  | Some n -> parts := !parts @ [Printf.sprintf "while checking '%s'" n]
  | None -> ());
  (match ctx.loc with
  | Some r -> parts := !parts @ [Printf.sprintf "at %s" (pp_loc r)]
  | None -> ());
  match !parts with
  | [] -> ""
  | xs -> " " ^ String.concat " " xs

let pp_local_ctx (e : Types.ctx) : string =
  Hashtbl.fold
    (fun k v acc ->
      acc
      ^ Pretty.term_to_string e { inner = Fvar k; loc = dummy_range }
      ^ " : "
      ^ Pretty.term_to_string e (snd v)
      ^ "\n")
    e.lctx
    ""

let pp_exn (e : Types.ctx) (info : elab_error_info) : string =
  let ctx_str = pp_context info.context in
  let local_ctx_str = pp_local_ctx e in
  match info.error_type with
  | ParseError { input; error_msg } ->
      Printf.sprintf
        "Parse error%s: %s (input: '%s')"
        ctx_str
        error_msg
        input
  | AlreadyDefined name ->
      Printf.sprintf
        "Error%s: %s is already defined"
        ctx_str
        name
  | TypeMismatch { term; inferred_type; expected_type } ->
      Printf.sprintf
        "Local context:\n\
         %s\n\
         Type mismatch%s: term\n\
         %s\n\
         has type\n\
         %s\n\
         but expected\n\
         %s\n"
        local_ctx_str
        ctx_str
        (Pretty.term_to_string e term)
        (Pretty.term_to_string e inferred_type)
        (Pretty.term_to_string e expected_type)
  | CannotInferHole ->
      Printf.sprintf
        "Local context:\n%s\nCannot infer hole%s"
        local_ctx_str
        ctx_str
  | KernelError { kernel_exn } ->
      Printf.sprintf
        "Kernel error%s: %s"
        ctx_str
        (ktype_err_to_string kernel_exn)
  | UnknownName { name } ->
      Printf.sprintf
        "Unknown name '%s'%s"
        name
        ctx_str
  | InternalError msg ->
      Printf.sprintf
        "Local context:\n%s\nInternal error%s: %s"
        local_ctx_str
        ctx_str
        msg
  | FunctionExpected { not_func; not_func_type; arg } ->
      Printf.sprintf
        "Local context:\n\
         %s\n\
         Expected a function%s, but got\n\
         %s\n\
         of type\n\
         %s\n\
         when applying to argument\n\
         %s\n"
        local_ctx_str
        ctx_str
        (Pretty.term_to_string e not_func)
        (Pretty.term_to_string e not_func_type)
        (Pretty.term_to_string e arg)
  | TypeExpected { not_type; not_type_infer } ->
      Printf.sprintf
        "Local context:\n\
         %s\n\
         Expected a type%s, but got\n\
         %s\n\
         which has type\n\
         %s\n"
        local_ctx_str
        ctx_str
        (Pretty.term_to_string e not_type)
        (Pretty.term_to_string e not_type_infer)
