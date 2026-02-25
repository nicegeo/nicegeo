(* Error.ml ; will hav eerror context, comment label, exception types, raise fields, and pretty print fields*)

(*comment label*)
type loc = { file :string; line :int; column :int }

(*error context*)
type error_context = { 
loc :loc option; (*loc - where the error is happening*)
decl_name :string option; (*decl_name - name of the declaration that caused the error*)
term_name :string option; (*term_name - name of the term that caused the error*)
expected_type :string option; (*expected_type - the expected type of the term*)
actual_type :string option; (*actual_type - the actual inferred type of the term*)
local_context : (string * string) list; (*local_context - the local context of the term*)
note :string option; (*note - a note about the error*)
}

(*empty default context*)
let empty_context = {
loc = None;
decl_name = None;
term_name = None;
expected_type = None;
actual_type = None;
local_context = [];
note = None;
}

(*helper functions to add information to the context*)
let with_loc l c = { c with loc = Some l }
let with_decl_name d c = { c with decl_name = Some d }
let with_term_name t c = { c with term_name = Some t }
let with_expected_type e c = { c with expected_type = Some e }
let with_actual_type a c = { c with actual_type = Some a }
let with_local_context ls c = { c with local_context = ls }
let with_note n c = { c with note = Some n }

(*exception types*)
exception TypeError of string * error_context
exception ParseError of string * error_context
exception UnknownConstant of string * error_context
exception UnknownVariable of string * error_context
exception InvalidProof of string * error_context
exception ElaboratorError of string * error_context
exception KernelError of string * error_context
exception InternalError of string * error_context

let raise_type_error ?(error_context=empty_context) msg = raise (TypeError (msg, error_context))
let raise_unknown_constant ?(error_context=empty_context) name = raise (UnknownConstant (name, error_context))
let raise_unknown_variable ?(error_context=empty_context) name = raise (UnknownVariable (name, error_context))
let raise_invalid_proof ?(error_context=empty_context) msg = raise (InvalidProof (msg, error_context))
let raise_parse_error ?(error_context=empty_context) msg = raise (ParseError (msg, error_context))
let raise_elab_error ?(error_context=empty_context) msg = raise (ElaboratorError (msg, error_context))
let raise_kernel_error ?(error_context=empty_context) msg = raise (KernelError (msg, error_context))
let raise_internal ?(error_context=empty_context) msg = raise (InternalError (msg, error_context))


let merge_ctx (newc : error_context) (oldc : error_context) : error_context =
  {
    loc      = (match newc.loc with Some _ -> newc.loc | None -> oldc.loc);
    decl_name     = (match newc.decl_name with Some _ -> newc.decl_name | None -> oldc.decl_name);
    term_name     = (match newc.term_name with Some _ -> newc.term_name | None -> oldc.term_name);
    expected_type = (match newc.expected_type with Some _ -> newc.expected_type | None -> oldc.expected_type);
    actual_type   = (match newc.actual_type with Some _ -> newc.actual_type | None -> oldc.actual_type);
    local_context = (if newc.local_context <> [] then newc.local_context else oldc.local_context);
    note     = (match newc.note with Some _ -> newc.note | None -> oldc.note);
  }

let add_ctx (c : error_context) (e : exn) : exn =
  match e with
  | TypeError (m, c0) -> TypeError (m, merge_ctx c c0)
  | UnknownConstant (n, c0) -> UnknownConstant (n, merge_ctx c c0)
  | UnknownVariable (n, c0) -> UnknownVariable (n, merge_ctx c c0)
  | InvalidProof (m, c0) -> InvalidProof (m, merge_ctx c c0)
  | ParseError (m, c0) -> ParseError (m, merge_ctx c c0)
  | ElaboratorError (m, c0) -> ElaboratorError (m, merge_ctx c c0)
  | KernelError (m, c0) -> KernelError (m, merge_ctx c c0)
  | InternalError (m, c0) -> InternalError (m, merge_ctx c c0)
  | _ ->
      (* wrap unknown exceptions into InternalError *)
      InternalError (Printexc.to_string e, c)
let pp_loc = function
  | None -> ""
  | Some {file; line; column} -> Printf.sprintf "%s:%d:%d" file line column

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

let pp_ctx (c:error_context) =
  let locs = pp_loc c.loc in
  let loc_line = if locs = "" then "" else ("at " ^ locs ^ "\n") in
  loc_line
  ^ pp_kv "decl" c.decl_name
  ^ pp_kv "term" c.term_name
  ^ pp_kv "expected" c.expected_type
  ^ pp_kv "actual" c.actual_type
  ^ pp_locals c.local_context
  ^ pp_kv "note" c.note

let pp_exn (e:exn) : string =
  match e with
  | TypeError (m, c) -> "Type error: " ^ m ^ "\n" ^ pp_ctx c
  | UnknownConstant (n, c) -> "Unknown constant: " ^ n ^ "\n" ^ pp_ctx c
  | UnknownVariable (n, c) -> "Unknown variable: " ^ n ^ "\n" ^ pp_ctx c
  | InvalidProof (m, c) -> "Invalid proof: " ^ m ^ "\n" ^ pp_ctx c
  | ParseError (m, c) -> "Parse error: " ^ m ^ "\n" ^ pp_ctx c
  | ElaboratorError (m, c) -> "Elaboration error: " ^ m ^ "\n" ^ pp_ctx c
  | KernelError (m, c) -> "Kernel error: " ^ m ^ "\n" ^ pp_ctx c
  | InternalError (m, c) -> "Internal error: " ^ m ^ "\n" ^ pp_ctx c
  | _ -> "Unhandled exception: " ^ Printexc.to_string e

(* convenience wrappers (so you can do Error.fail_type "..." instead of failwith) *)
let fail_type ?(error_context=empty_context) msg = raise (TypeError (msg, error_context))
let fail_kernel ?(error_context=empty_context) msg = raise (KernelError (msg, error_context))
let fail_elab ?(error_context=empty_context) msg = raise (ElaboratorError (msg, error_context))