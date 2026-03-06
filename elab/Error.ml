open Term
module KTerm = Kernel.Term
module KExceptions = Kernel.Exceptions

type error_context = {
  loc : range option; (* loc - where the error is happening *)
  decl_name : string option;
      (* decl_name - name of the declaration that caused the error *)
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

(*
 * Suggestions and pretty-printing helpers
 *)

let levenshtein_distance (s : string) (t : string) : int =
  let m = String.length s in
  let n = String.length t in
  let dp = Array.make_matrix (m + 1) (n + 1) 0 in
  for i = 0 to m do
    dp.(i).(0) <- i
  done;
  for j = 0 to n do
    dp.(0).(j) <- j
  done;
  for i = 1 to m do
    for j = 1 to n do
      let cost = if s.[i - 1] = t.[j - 1] then 0 else 1 in
      dp.(i).(j) <-
        min (min (dp.(i - 1).(j) + 1) (dp.(i).(j - 1) + 1)) (dp.(i - 1).(j - 1) + cost)
    done
  done;
  dp.(m).(n)

let suggest_similar_names (unknown : string) (env : Types.ctx) : string list =
  let candidates = ref [] in
  Hashtbl.iter
    (fun name _entry ->
      let dist = levenshtein_distance unknown name in
      let score =
        if String.length unknown > 0 && String.length name > 0 && unknown.[0] = name.[0]
        then dist - 1
        else dist
      in
      candidates := (name, score) :: !candidates)
    env.env;
  let sorted = List.sort (fun (_, d1) (_, d2) -> compare d1 d2) !candidates in
  sorted |> List.filter (fun (_, d) -> d <= 3) |> List.map fst |> fun names ->
  let rec take k xs =
    match (k, xs) with 0, _ | _, [] -> [] | k, x :: xs' -> x :: take (k - 1) xs'
  in
  take 3 names

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
  let loc_str =
    match info.context.loc with Some r -> pp_loc r | None -> "unknown location"
  in
  let decl_str =
    match info.context.decl_name with
    | Some n -> Printf.sprintf "declaration '%s'" n
    | None -> "unknown declaration"
  in
  let local_ctx_str = pp_local_ctx e in
  match info.error_type with
  | ParseError { input; error_msg } ->
      Printf.sprintf
        "Parse error in %s at %s: %s (input: '%s')"
        decl_str
        loc_str
        error_msg
        input
  | AlreadyDefined name ->
      Printf.sprintf "Error in %s: %s is already defined" decl_str name
  | TypeMismatch { term; inferred_type; expected_type } ->
      Printf.sprintf
        "Local context:\n\
         %s\n\
         Type mismatch in %s at %s: term\n\
         %s\n\
         has type\n\
         %s\n\
         but expected\n\
         %s\n"
        local_ctx_str
        decl_str
        loc_str
        (Pretty.term_to_string e term)
        (Pretty.term_to_string e inferred_type)
        (Pretty.term_to_string e expected_type)
  | CannotInferHole ->
      Printf.sprintf
        "Local context:\n%s\nCannot infer hole in %s at %s"
        local_ctx_str
        decl_str
        loc_str
  | KernelError { kernel_exn } ->
      Printf.sprintf
        "Kernel error in %s at %s: %s"
        decl_str
        loc_str
        (ktype_err_to_string kernel_exn)
  | UnknownName { name } -> (
      let base = Printf.sprintf "Unknown name '%s' in %s at %s" name decl_str loc_str in
      let suggestions = suggest_similar_names name e in
      match suggestions with
      | [] -> base
      | _ ->
          let sugg_str = String.concat ", " suggestions in
          base ^ Printf.sprintf "\nDid you mean: %s?" sugg_str)
  | InternalError msg ->
      Printf.sprintf
        "Local context:\n%s\nInternal error in %s at %s: %s"
        local_ctx_str
        decl_str
        loc_str
        msg
  | FunctionExpected { not_func; not_func_type; arg } ->
      Printf.sprintf
        "Local context:\n\
         %s\n\
         Expected a function in %s at %s, but got\n\
         %s\n\
         of type\n\
         %s\n\
         when applying to argument\n\
         %s\n"
        local_ctx_str
        decl_str
        loc_str
        (Pretty.term_to_string e not_func)
        (Pretty.term_to_string e not_func_type)
        (Pretty.term_to_string e arg)
  | TypeExpected { not_type; not_type_infer } ->
      Printf.sprintf
        "Local context:\n\
         %s\n\
         Expected a type in %s at %s, but got\n\
         %s\n\
         which has type\n\
         %s\n"
        local_ctx_str
        decl_str
        loc_str
        (Pretty.term_to_string e not_type)
        (Pretty.term_to_string e not_type_infer)
