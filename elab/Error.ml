(* Error.ml ; will hav eerror context, comment label, exception types, raise fields, and pretty print fields*)
open Term
module KExceptions = System_e_kernel.Exceptions

(*comment label*)

(*error context*)
type error_context = { 
  loc: range option; (*loc - where the error is happening*)
  decl_name: string option; (*decl_name - name of the declaration that caused the error*)
}

type parse_error_info = {
  input : string; (* the input that failed to parse *)
  error_msg : string; (* the error message from the parser *)
}

type type_mismatch_info = {
  term: term;
  inferred_type: term;
  expected_type: term;
}

type kernel_error_info = {
  kernel_exn : KExceptions.type_error_info;
}

type unknown_name_info = {
  name : string;
}

type function_expected_info = {
  not_func: term;
  not_func_type: term;
  arg: term;
}

type type_expected_info = {
  not_type: term;
  not_type_infer: term;
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

let pp_loc (r: range) =
  Printf.sprintf "%s:%d:%d-%d:%d" r.start.pos_fname r.start.pos_lnum (r.start.pos_cnum - r.start.pos_bol) r.end_.pos_lnum (r.end_.pos_cnum - r.end_.pos_bol)

let pp_kv k = function
  | None -> ""
  | Some v -> Printf.sprintf "%s: %s\n" k v

let pp_locals locals =
  if locals = [] then ""
  else
    let lines =
      locals
      |> List.map (fun (x, ty) -> Printf.sprintf "  %s : %s" x ty)
      |> String.concat "\n"
    in
    "locals:\n" ^ lines ^ "\n"

let pp_exn (e: Types.ctx) (info: elab_error_info) : string =
  let loc_str = match info.context.loc with
    | Some r -> pp_loc r
    | None -> "unknown location"
  in
  let decl_str = match info.context.decl_name with
    | Some n -> Printf.sprintf "declaration '%s'" n
    | None -> "a declaration"
   in
  match info.error_type with
  | ParseError { input; error_msg } ->
      Printf.sprintf "Parse error in %s at %s: %s (input: '%s')" decl_str loc_str error_msg input
  | AlreadyDefined name ->
      Printf.sprintf "Error in %s: %s is already defined" decl_str name
  | TypeMismatch { term; inferred_type; expected_type } ->
      Printf.sprintf "Type mismatch in %s at %s: term '%s' has type '%s' but expected '%s'" decl_str loc_str (Pretty.term_to_string e term) (Pretty.term_to_string e inferred_type) (Pretty.term_to_string e expected_type)
  | CannotInferHole ->
      Printf.sprintf "Cannot infer type of hole in %s at %s" decl_str loc_str
  | KernelError { kernel_exn } ->
      Printf.sprintf "Kernel error in %s at %s: %s" decl_str loc_str (KExceptions.type_err_to_string kernel_exn)
  | UnknownName { name } ->
      Printf.sprintf "Unknown name '%s' in %s at %s" name decl_str loc_str
  | InternalError msg ->
      Printf.sprintf "Internal error in %s at %s: %s" decl_str loc_str msg
  | FunctionExpected { not_func; not_func_type; arg } ->
      Printf.sprintf "Expected a function in %s at %s, but got '%s' of type '%s' when applying to argument '%s'" decl_str loc_str (Pretty.term_to_string e not_func) (Pretty.term_to_string e not_func_type) (Pretty.term_to_string e arg)
  | TypeExpected { not_type; not_type_infer } ->
      Printf.sprintf "Expected a type in %s at %s, but got '%s' which has type '%s'" decl_str loc_str (Pretty.term_to_string e not_type) (Pretty.term_to_string e not_type_infer)

