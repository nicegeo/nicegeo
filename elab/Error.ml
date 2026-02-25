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
  local_context: (string * term) list;
}

type kernel_error_info = {
  kernel_exn : KExceptions.type_error_info;
}

type unknown_name_info = {
  name : string;
}

type error_type =
| ParseError of parse_error_info
| TypeMismatch of type_mismatch_info
| CannotInferHole
| KernelError of kernel_error_info
| UnknownName of unknown_name_info

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

let pp_exn (e: elab_error_info) : string =
  match e.error_type with
  | ParseError { input; error_msg } ->
      let loc_str = match e.context.loc with
        | Some r -> pp_loc r
        | None -> "unknown location"
      in
      Printf.sprintf "Parse error at %s: %s (input: '%s')" loc_str error_msg input
  | _ -> failwith "todo"

