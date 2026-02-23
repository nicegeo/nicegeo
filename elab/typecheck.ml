open Decl
open Term
open Convert
open Types
module KInfer = System_e_kernel.Infer

exception InferHole

type normterm =
  | Fun of string option * term * term
  | Arrow of string option * term * term
  | VarSpine of term * term list
  | MetaSpine of term * term list
  | Sort of int

let rec term_to_string (e: ctx) (tm: term) : string =
  match tm with
  | Name name -> name
  | Bvar idx -> "Bvar(" ^ string_of_int idx ^ ")"
  | Fvar idx -> 
    Hashtbl.find_opt e.lctx idx |> (function
      | Some (Some name, _) -> name
      | _ -> "Fvar(" ^ string_of_int idx ^ ")")
  | Hole idx -> 
    (match Hashtbl.find_opt e.metas idx with
    | Some {sol=Some tm_sol; _} -> "(hole " ^ string_of_int idx ^ " = " ^ term_to_string e tm_sol ^ ")"
    | _ -> "Hole(" ^ string_of_int idx ^ ")" )
  | Fun (arg, ty_arg, body) ->
      let arg_str = match arg with Some a -> a | None -> "_" in
      "(fun (" ^ arg_str ^ " : " ^ term_to_string e ty_arg ^ ") => " ^ term_to_string e body ^ ")"
  | Arrow (arg, ty_arg, ty_ret) ->
      let arg_str = match arg with Some a -> a | None -> "_" in
      "(" ^ arg_str ^ " : " ^ term_to_string e ty_arg ^ " -> " ^ term_to_string e ty_ret ^ ")"
  | App (f, arg) ->
      "(" ^ term_to_string e f ^ " " ^ term_to_string e arg ^ ")"
  | Sort n -> "Sort(" ^ string_of_int n ^ ")"

let rec whnf_beta (e: ctx) (tm: term) : term =
  match tm with
  | App (f, arg) -> 
    let fn = whnf_beta e f in
    (match fn with
    | Fun (_, _, body) -> whnf_beta e (replace_bvar body 0 arg)
    | _ -> App (fn, arg))
  (* do we need to recurse into holes? possibly *)
  | Hole m -> (match Hashtbl.find_opt e.metas m with
    | Some {sol=Some tm_sol; _} -> whnf_beta e tm_sol
    | _ -> tm)
  | _ -> tm

(* precondition: tm is already in whnf (call whnf_beta) *)
let rec to_norm (e: ctx) (tm : term) : normterm =
  match tm with
  | Fun (arg, ty_arg, body) -> Fun (arg, ty_arg, body)
  | Arrow (arg, ty_arg, ty_ret) -> Arrow (arg, ty_arg, ty_ret)
  | App (f, arg) -> 
    let f_norm = to_norm e f in
    (match f_norm with
    | VarSpine (head, args) -> VarSpine (head, args @ [arg])
    | MetaSpine (head, args) -> MetaSpine (head, args @ [arg])
    | Fun _ | Arrow _ -> failwith "to_norm input should already be in whnf"
    | Sort _ -> failwith "to_norm: cannot apply a sort")
  | Name _ | Bvar _ | Fvar _ -> VarSpine (tm, [])
  | Sort n -> Sort n
  | Hole _ -> MetaSpine (tm, [])


let valid_pattern_args (args: term list) : bool =
  if List.exists (fun arg -> match arg with | Fvar _ -> false | _ -> true) args then false else
  let rec check_args seen_args args =
    match args with
    | [] -> true
    | arg :: rest ->
      if List.exists (fun seen_arg -> match (seen_arg, arg) with
        | (Fvar idx1, Fvar idx2) when idx1 = idx2 -> true
        | _ -> false) seen_args then false
      else check_args (arg :: seen_args) rest
  in check_args [] args

let rec valid_pattern (e: ctx) (m: int) (args: term list) (tm: term) : bool =
  match tm with
  | Hole m' -> if m = m' then ((*print_endline "hole contains itself";*) false) else (match Hashtbl.find_opt e.metas m' with
    | Some {sol=Some tm_sol; _} -> valid_pattern e m args tm_sol
    | _ -> true)
  | Fun (_, ty, body) -> valid_pattern e m args ty && valid_pattern e m args body
  | Arrow (_, ty, ret) -> valid_pattern e m args ty && valid_pattern e m args ret
  | App (f, arg) -> valid_pattern e m args f && valid_pattern e m args arg
  | Fvar _ -> List.exists (fun arg -> arg = tm) args
  | _ -> true

let rec last = function
| [] -> failwith "empty list"
| [x] -> x
| _ :: xs -> last xs

let rec pattern_match_meta (e: ctx) (m: int) (args: term list) (tm: term) : unit =
  (* print_endline ("pattern matching meta " ^ string_of_int m ^ " with args " ^ String.concat " " (List.map (term_to_string e) args) ^ " against term " ^ term_to_string e tm); *)
  (* uhh get rid of the last matching args? *)
  if List.length (Hashtbl.find e.metas m).vartypes < List.length args then
    match tm with
    | App (f, arg) when last args = arg -> 
      pattern_match_meta e m (List.rev (List.tl (List.rev args))) f
    | _ -> failwith "too many arguments in pattern match for meta"
  else
  if not (valid_pattern_args args) then print_endline "invalid arguments for pattern matching" else
  if not (valid_pattern e m args tm) then (*print_endline "invalid solution for meta"*) () else

  (* just need to bind them now how hard can it be clueless *)
  (* could basically walk down term,  *)
  (* actually let's just do the args one at a time. for each arg, do fun arg => (replace tm with bvar) *)
  let rec fold (tm: term) (args: term list) (types: term list) : term = (* args and types in reverse order lol *)
    match args with
    | [] -> tm
    | arg :: rest ->
      let tm_with_arg = bind_bvar tm 0 arg in
      let tm_fun = Term.Fun (None, List.hd types, tm_with_arg) in
      fold tm_fun rest (List.tl types)
  in

  Hashtbl.replace e.metas m { (Hashtbl.find e.metas m) with sol = Some (fold tm (List.rev args) (List.rev (Hashtbl.find e.metas m).vartypes)) }

let rec unify (e: ctx) (t1: term) (t2: term) : unit =
  let t1 = whnf_beta e t1 in
  let t2 = whnf_beta e t2 in
  (* print_endline ("unifying " ^ term_to_string e t1 ^ " and " ^ term_to_string e t2); *)
  let nt1 = to_norm e t1 in
  let nt2 = to_norm e t2 in
  (* t1 and t2 should be closed under the current e *)
  match (nt1, nt2) with
  | MetaSpine (Hole m1, args1), MetaSpine (Hole m2, args2) -> 
    (* could theoretically do some freaky stuff here *)
    if List.length args1 != List.length args2 then print_endline "tried to unify different length meta spines" else
    if m1 = m2 then () else
    let (m1, m2) = if m1 < m2 then (m1, m2) else (m2, m1) in
    Hashtbl.replace e.metas m1 { (Hashtbl.find e.metas m1) with sol = Some (Hole m2) };
    List.iter2 (fun arg1 arg2 -> unify e arg1 arg2) args1 args2
  | MetaSpine (Hole m, args), _ ->
    pattern_match_meta e m args t2
  | _, MetaSpine (Hole m, args) ->
    pattern_match_meta e m args t1
  | VarSpine (h1, args1), VarSpine (h2, args2) when h1 = h2 ->
    if List.length args1 != List.length args2 then failwith "tried to unify different length var spines" else
    List.iter2 (fun arg1 arg2 -> unify e arg1 arg2) args1 args2
  | Arrow (_, ty_arg1, ty_ret1), Arrow (_, ty_arg2, ty_ret2) ->
    unify e ty_arg1 ty_arg2;
    let x = gen_fvar_id () in
    let ty_ret1_fvar = replace_bvar ty_ret1 0 (Fvar x) in
    let ty_ret2_fvar = replace_bvar ty_ret2 0 (Fvar x) in
    unify e ty_ret1_fvar ty_ret2_fvar
  | Fun (_, ty_arg1, body1), Fun (_, ty_arg2, body2) -> (* todo: eta i think here? *)
    unify e ty_arg1 ty_arg2;
    let x = gen_fvar_id () in
    let body1_fvar = replace_bvar body1 0 (Fvar x) in
    let body2_fvar = replace_bvar body2 0 (Fvar x) in
    unify e body1_fvar body2_fvar
  | Sort n1, Sort n2 when n1 = n2 -> ()
  | _ -> failwith ("failed to unify non-matching terms " ^ term_to_string e t1 ^ " and " ^ term_to_string e t2)

(* checks that tm has expected type ty, trying to fill in metas? *)
(* if it fails it throws an exception. todo: use actual exceptions *)
let rec checktype (e: ctx) (tm: term) (ty: term) : unit =
  (* print_endline ("checking " ^ term_to_string e tm ^ " has type " ^ term_to_string e ty); *)
  match tm with 
  | Hole m ->
    (match Hashtbl.find_opt e.metas m with
    | Some {ty=ty1; vartypes; sol} -> 
      (match ty1 with
      | Some ty1 -> unify e ty ty1
      | None -> Hashtbl.replace e.metas m {ty = Some ty; vartypes; sol})
    | None -> failwith "unknown metavar in checktype")
  | App (f, arg) ->
    (try unify e ty (infertype e tm) with InferHole ->
      let argtype = infertype e arg in
      checktype e f (Arrow (None, argtype, ty)))
  | Name _ | Fun _ | Arrow _ | Sort _ | Fvar _ ->
    unify e ty (infertype e tm)
  | Bvar _ -> failwith "unexpected bound variable in checktype"
  
and infertype (e: ctx) (tm: term) : term =
  (* print_endline ("inferring type of " ^ term_to_string e tm); *)
  let res = match tm with
  | Hole _ -> raise InferHole
  | Name name ->
    (match Hashtbl.find_opt e.env name with
      | Some ty -> ty      
      | None -> failwith ("unknown identifier: " ^ name))
  | Fun (arg, ty_arg, body) ->
    check_is_type e ty_arg;
    let x = gen_fvar_id () in
    let body_fvar = replace_bvar body 0 (Fvar x) in
    Hashtbl.add e.lctx x (arg, ty_arg);
    let ty_body = infertype e body_fvar in
    let ty_body = bind_bvar ty_body 0 (Fvar x) in
    Hashtbl.remove e.lctx x;
    Arrow (arg, ty_arg, ty_body)
  | Arrow (arg, ty_arg, ty_ret) ->
    check_is_type e ty_arg;
    let ty_arg_ty = infertype e ty_arg in
    let x = gen_fvar_id () in
    let ty_ret_fvar = replace_bvar ty_ret 0 (Fvar x) in
    Hashtbl.add e.lctx x (arg, ty_arg);
    check_is_type e ty_ret_fvar;
    let ty_ret_ty = infertype e ty_ret_fvar in
    Hashtbl.remove e.lctx x;
    (match ty_arg_ty, ty_ret_ty with
    | Sort n1, Sort n2 -> Sort (max n1 n2)
    | _ -> failwith "expected types of arrow to be sorts")
  | App (f, arg) ->
    let f_type = infertype e f in
    (match f_type with
    | Arrow (_, ty_arg, ty_ret) ->
      check_is_type e ty_arg;
      checktype e arg ty_arg;
      replace_bvar ty_ret 0 arg
    | _ -> failwith "expected a function type in application")
  | Bvar _ -> failwith "unexpected bound variable in infertype"
  | Fvar fvar ->
    (match Hashtbl.find_opt e.lctx fvar with
    | Some (_, ty) -> ty
    | None -> failwith "unknown free variable in infertype")
  | Sort n -> Sort (n + 1)
  in 
  (* print_endline ("inferred type " ^ term_to_string e res ^ " for term " ^ term_to_string e tm); *)
  res


and check_is_type (e: ctx) (tm: term) : unit =
  (* print_endline ("checking " ^ term_to_string e tm ^ " is a type"); *)
  match tm with
  | Hole m ->
    (match Hashtbl.find_opt e.metas m with
    | Some {ty=Some ty; _} -> if not (is_sort ty) then failwith "expected hole to be a sort" else ()
    | _ -> ())
  | Name name ->
    (match Hashtbl.find_opt e.env name with
      | Some ty -> if not (is_sort ty) then failwith ("expected " ^ name ^ " to be a type") else ()
      | None -> failwith ("unknown identifier: " ^ name))
  | Fun _ ->
    failwith "a function cannot be a type"
  | Arrow (arg, ty_arg, ty_ret) ->
    check_is_type e ty_arg;
    let x = gen_fvar_id () in
    let ty_ret_fvar = replace_bvar ty_ret 0 (Fvar x) in
    Hashtbl.add e.lctx x (arg, ty_arg);
    check_is_type e ty_ret_fvar;
    Hashtbl.remove e.lctx x
  | App (f, arg) ->
    let f_type = try Some (infertype e f) with InferHole -> None in

    (match f_type with
    | Some (Arrow (_, ty_arg, ty_ret)) -> 
      (* print_endline ("app checktype: checking that " ^ term_to_string e arg ^ " has type " ^ term_to_string e ty_arg);
      print_endline ("because f is " ^ term_to_string e f ^ " and has type " ^ term_to_string e f_type); *)
      checktype e arg ty_arg;
      if not (is_sort ty_ret) then failwith "expected return type of function to be a sort"
    | Some _ -> failwith "expected a function type in application"
    | None -> ())
  | Sort _ -> ()
  | Bvar _ -> failwith "unexpected bound variable in check_is_type"
  | Fvar fvar ->
    (match Hashtbl.find_opt e.lctx fvar with
    | Some (_, ty) -> 
      let ty = whnf_beta e ty in
      if not (is_sort ty || match ty with | Hole _ -> true | _ -> false) then failwith ("expected type " ^ (term_to_string e ty) ^ " of free variable to be a sort") else ()
    | None -> failwith "unknown free variable in check_is_type")


let rec contains_fvar (tm: term) : bool =
  match tm with
  | Fvar _ -> true
  | Fun (_, ty_arg, body) -> contains_fvar ty_arg || contains_fvar body
  | Arrow (_, ty_arg, ty_ret) -> contains_fvar ty_arg || contains_fvar ty_ret
  | App (f, arg) -> contains_fvar f || contains_fvar arg
  | _ -> false

let rec replace_metas (e: ctx) (tm: term) : term =
  match tm with
  | Hole m -> (match Hashtbl.find_opt e.metas m with
    | Some {sol=Some tm_sol; _} -> 
      if contains_fvar tm_sol then failwith "hole contains free variables, should have been bound" else
      replace_metas e tm_sol
    | _ -> failwith ("unfilled hole in replace_metas: " ^ term_to_string e tm))
  | Fun (arg, ty_arg, body) ->
    let ty_arg_filled = replace_metas e ty_arg in
    let body_filled = replace_metas e body in
    Fun (arg, ty_arg_filled, body_filled)
  | Arrow (arg, ty_arg, ty_ret) ->
    let ty_arg_filled = replace_metas e ty_arg in
    let ty_ret_filled = replace_metas e ty_ret in
    Arrow (arg, ty_arg_filled, ty_ret_filled)
  | App (f, arg) ->
    let f_filled = replace_metas e f in
    let arg_filled = replace_metas e arg in
    App (f_filled, arg_filled)
  | _ -> tm

let rec hole_to_meta (e: ctx) (stack: term list) (tm: term): term = 
  match tm with
  | Hole m ->
    let types = List.rev stack in
    let meta = { ty = None; vartypes = types; sol = None } in
    Hashtbl.add e.metas m meta;
    (* App(App(App(tm, Bvar 2), Bvar 1), Bvar 0) *)
    let rec fold (tm: term) (level: int) : term =
      (match level with
      | 0 -> tm
      | n ->
        fold (App (tm, Bvar (n - 1))) (n - 1))
    in
    fold (Hole m) (List.length stack)
  | Fun (arg, ty_arg, body) ->
    let ty_arg_meta = hole_to_meta e stack ty_arg in
    let body_meta = hole_to_meta e (ty_arg_meta :: stack) body in
    Fun (arg, ty_arg_meta, body_meta)
  | Arrow (arg, ty_arg, ty_ret) ->
    let ty_arg_meta = hole_to_meta e stack ty_arg in
    let ty_ret_meta = hole_to_meta e (ty_arg_meta :: stack) ty_ret in
    Arrow (arg, ty_arg_meta, ty_ret_meta)
  | App (f, arg) ->
    let f_meta = hole_to_meta e stack f in
    let arg_meta = hole_to_meta e stack arg in
    App (f_meta, arg_meta)
  | _ -> tm


let process_decl (e: ctx) (d: declaration) : unit =
  match d with
  | Theorem (name, ty, proof) ->
    if Hashtbl.mem e.env name then failwith ("theorem " ^ name ^ " already defined.\n") else
    let ty_meta = hole_to_meta e [] ty in
    check_is_type e ty_meta;
    let ty_filled = replace_metas e ty_meta in
    Hashtbl.clear e.metas;
    let proof_meta = hole_to_meta e [] proof in
    checktype e proof_meta ty_filled;
    let proof_filled = replace_metas e proof_meta in
    Hashtbl.clear e.metas;
    let ty_k = conv_to_kterm ty_filled in
    let proof_k = conv_to_kterm proof_filled in
    let inferredType = KInfer.inferType e.kenv (Hashtbl.create 0) proof_k in
    let isValidProof = KInfer.isDefEq e.kenv (Hashtbl.create 0) inferredType ty_k in

    if isValidProof then
      (Hashtbl.add e.env name ty_filled;
      Hashtbl.add e.kenv name ty_k)
    else
      failwith ("invalid proof of " ^ name ^ ".\n")
  | Axiom (name, ty) ->
    (* print_endline ("processing axiom " ^ name ^ " of type " ^ term_to_string e ty); *)
    if Hashtbl.mem e.env name then failwith ("axiom " ^ name ^ " already defined.\n") else
    let ty_meta = hole_to_meta e [] ty in
    check_is_type e ty_meta;
    let ty_filled = try replace_metas e ty_meta with Failure msg -> failwith ("failed to replace metas in axiom " ^ name ^ " of type " ^ term_to_string e ty_meta ^ ": " ^ msg) in

    Hashtbl.clear e.metas;
    let ty_k = conv_to_kterm ty_filled in
    Hashtbl.add e.env name ty_filled;
    Hashtbl.add e.kenv name ty_k 
