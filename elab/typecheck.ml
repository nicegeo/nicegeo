open Decl
open Term
open Convert
open Types
module KInfer = System_e_kernel.Infer
module KExceptions = System_e_kernel.Exceptions

let raise_at (tm: term) (e: Error.error_type) : 'a =
  let loc = Some tm.loc in
  raise (Error.ElabError { context = { loc; decl_name = None }; error_type = e })

type normterm =
  | Fun of string option * term * term
  | Arrow of string option * term * term
  | VarSpine of term * term list
  | MetaSpine of term * term list
  | Sort of int

let rec term_to_string (e: ctx) (tm: term) : string =
  match tm.inner with
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
  match tm.inner with
  | App (f, arg) -> 
    let fn = whnf_beta e f in
    (match fn.inner with
    | Fun (_, _, body) -> whnf_beta e (replace_bvar body 0 arg)
    | _ -> {inner=App (fn, arg); loc=tm.loc})
  (* do we need to recurse into holes? possibly *)
  | Hole m -> (match Hashtbl.find_opt e.metas m with
    | Some {sol=Some tm_sol; _} -> whnf_beta e tm_sol
    | _ -> tm)
  | _ -> tm

(* precondition: tm is already in whnf (call whnf_beta) *)
let rec to_norm (e: ctx) (tm : term) : normterm =
  match tm.inner with
  | Fun (arg, ty_arg, body) -> Fun (arg, ty_arg, body)
  | Arrow (arg, ty_arg, ty_ret) -> Arrow (arg, ty_arg, ty_ret)
  | App (f, arg) -> 
    let f_norm = to_norm e f in
    (match f_norm with
    | VarSpine (head, args) -> VarSpine (head, args @ [arg])
    | MetaSpine (head, args) -> MetaSpine (head, args @ [arg])
    | Fun _ -> raise_at tm (Error.InternalError "to_norm input should already be in whnf")
    | Arrow (n, ty_arg, ty_ret) -> raise_at tm (Error.FunctionExpected { not_func = tm; not_func_type = {inner=Arrow (n, ty_arg, ty_ret); loc=tm.loc}; arg = arg })
    | Sort n -> raise_at tm (Error.FunctionExpected { not_func = tm; not_func_type = {inner=Sort n; loc=tm.loc}; arg = arg }))
  | Name _ | Bvar _ | Fvar _ -> VarSpine (tm, [])
  | Sort n -> Sort n
  | Hole _ -> MetaSpine (tm, [])


let valid_pattern_args (args: term list) : bool =
  if List.exists (fun arg -> match arg.inner with | Fvar _ -> false | _ -> true) args then false else
  let rec check_args seen_args args =
    match args with
    | [] -> true
    | arg :: rest ->
      if List.exists (fun seen_arg -> match (seen_arg, arg.inner) with
        | (Fvar idx1, Fvar idx2) when idx1 = idx2 -> true
        | _ -> false) seen_args then false
      else check_args (arg.inner :: seen_args) rest
  in check_args [] args

let rec valid_pattern (e: ctx) (m: int) (args: term list) (tm: term) : bool =
  match tm.inner with
  | Hole m' -> if m = m' then ((*print_endline "hole contains itself";*) false) else (match Hashtbl.find_opt e.metas m' with
    | Some {sol=Some tm_sol; _} -> valid_pattern e m args tm_sol
    | _ -> true)
  | Fun (_, ty, body) -> valid_pattern e m args ty && valid_pattern e m args body
  | Arrow (_, ty, ret) -> valid_pattern e m args ty && valid_pattern e m args ret
  | App (f, arg) -> valid_pattern e m args f && valid_pattern e m args arg
  | Fvar _ -> List.exists (fun arg -> arg.inner = tm.inner) args
  | _ -> true

let rec last = function
| [] -> failwith "empty list"
| [x] -> x
| _ :: xs -> last xs

let rec pattern_match_meta (e: ctx) (m: int) (args: term list) (tm: term) : unit =
  (* print_endline ("pattern matching meta " ^ string_of_int m ^ " with args " ^ String.concat " " (List.map (term_to_string e) args) ^ " against term " ^ term_to_string e tm); *)
  (* uhh get rid of the last matching args? *)
  if List.length (Hashtbl.find e.metas m).vartypes < List.length args then
    match tm.inner with
    | App (f, arg) when (last args).inner = arg.inner -> 
      pattern_match_meta e m (List.rev (List.tl (List.rev args))) f
    | _ -> () (* we could like, infer the type of the rest of the args *)
  else
  if not (valid_pattern_args args) then print_endline "invalid arguments for pattern matching" else
  if not (valid_pattern e m args tm) then (*print_endline "invalid solution for meta";*) () else

  (* just need to bind them now how hard can it be clueless *)
  (* could basically walk down term,  *)
  (* actually let's just do the args one at a time. for each arg, do fun arg => (replace tm with bvar) *)
  let rec fold (tm: term) (args: term list) (types: term list) : term = (* args and types in reverse order lol *)
    match args with
    | [] -> tm
    | arg :: rest ->
      let tm_with_arg = bind_bvar tm 0 arg in
      let tm_fun = Term.Fun (None, List.hd types, tm_with_arg) in
      fold {inner=tm_fun; loc=tm.loc} rest (List.tl types)
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
  | MetaSpine ({inner=Hole m1; _}, args1), MetaSpine ({inner=Hole m2; loc=l2}, args2) -> 
    (* could theoretically do some freaky stuff here *)
    if List.length args1 != List.length args2 then print_endline "tried to unify different length meta spines" else
    if m1 = m2 then () else
    let (m1, m2) = if m1 < m2 then (m1, m2) else (m2, m1) in
    Hashtbl.replace e.metas m1 { (Hashtbl.find e.metas m1) with sol = Some {inner=Hole m2; loc=l2} };
    List.iter2 (fun arg1 arg2 -> unify e arg1 arg2) args1 args2
  | MetaSpine ({inner=Hole m; _}, args), _ ->
    pattern_match_meta e m args t2
  | _, MetaSpine ({inner=Hole m; _}, args) ->
    pattern_match_meta e m args t1
  | VarSpine (h1, args1), VarSpine (h2, args2) when h1.inner = h2.inner ->
    if List.length args1 != List.length args2 then failwith "tried to unify different length var spines" else
    List.iter2 (fun arg1 arg2 -> unify e arg1 arg2) args1 args2
  | Arrow (_, ty_arg1, ty_ret1), Arrow (_, ty_arg2, ty_ret2) ->
    unify e ty_arg1 ty_arg2;
    let x = gen_fvar_id () in
    let ty_ret1_fvar = replace_bvar ty_ret1 0 {inner=Fvar x; loc=ty_ret1.loc} in
    let ty_ret2_fvar = replace_bvar ty_ret2 0 {inner=Fvar x; loc=ty_ret2.loc} in
    unify e ty_ret1_fvar ty_ret2_fvar
  | Fun (_, ty_arg1, body1), Fun (_, ty_arg2, body2) -> (* todo: eta i think here? *)
    unify e ty_arg1 ty_arg2;
    let x = gen_fvar_id () in
    let body1_fvar = replace_bvar body1 0 {inner=Fvar x; loc=body1.loc} in
    let body2_fvar = replace_bvar body2 0 {inner=Fvar x; loc=body2.loc} in
    unify e body1_fvar body2_fvar
  | Sort n1, Sort n2 when n1 = n2 -> ()
  | _ -> failwith ("failed to unify non-matching terms " ^ term_to_string e t1 ^ " and " ^ term_to_string e t2)

(* checks that tm has expected type ty, trying to fill in metas? *)
(* if it fails it throws an exception. todo: use actual exceptions *)
let rec checktype (e: ctx) (tm: term) (ty: term) : unit =
  (* print_endline ("checking " ^ term_to_string e tm ^ " has type " ^ term_to_string e ty); *)
  match tm.inner with 
  | Hole m ->
    (match Hashtbl.find_opt e.metas m with
    | Some {ty=ty1; vartypes; sol} -> 
      (match ty1 with
      | Some ty1 -> unify e ty ty1
      | None -> Hashtbl.replace e.metas m {ty = Some ty; vartypes; sol})
    | None -> raise_at tm (Error.InternalError ("unknown meta: " ^ string_of_int m)))
  | App (f, arg) ->
    (try (let tm_type = infertype e tm in
      try unify e ty tm_type
      with Failure _ -> raise_at tm (Error.TypeMismatch { term = tm; inferred_type = tm_type; expected_type = ty }))
    with Error.ElabError {error_type = Error.CannotInferHole; _} ->
      let argtype = infertype e arg in
      checktype e f {inner=Arrow (None, argtype, ty); loc=ty.loc})
  | Name _ | Fun _ | Arrow _ | Sort _ | Fvar _ ->
    let infer_ty = infertype e tm in
    (try unify e infer_ty ty with
    | Failure _ -> raise_at tm (Error.TypeMismatch { term = tm; inferred_type = infer_ty; expected_type = ty }))
  | Bvar _ -> raise_at tm (Error.InternalError "unexpected bound variable in checktype")
  
and infertype (e: ctx) (tm: term) : term =
  (* print_endline ("inferring type of " ^ term_to_string e tm); *)
  let res = match tm.inner with
  | Hole _ -> raise_at tm (Error.CannotInferHole)
  | Name name ->
    (match Hashtbl.find_opt e.env name with
      | Some entry -> entry.ty
      | None -> raise_at tm (Error.UnknownName { name }))
  | Fun (arg, ty_arg, body) ->
    check_is_type e ty_arg;
    let x = gen_fvar_id () in
    let body_fvar = replace_bvar body 0 {inner=Fvar x; loc=body.loc} in
    Hashtbl.add e.lctx x (arg, ty_arg);
    let ty_body = infertype e body_fvar in
    let ty_body = bind_bvar ty_body 0 {inner=Fvar x; loc=body.loc} in
    Hashtbl.remove e.lctx x;
    {inner=Arrow (arg, ty_arg, ty_body); loc=tm.loc}
  | Arrow (arg, ty_arg, ty_ret) ->
    check_is_type e ty_arg;
    let ty_arg_ty = infertype e ty_arg in
    let x = gen_fvar_id () in
    let ty_ret_fvar = replace_bvar ty_ret 0 {inner=Fvar x; loc=ty_ret.loc} in
    Hashtbl.add e.lctx x (arg, ty_arg);
    check_is_type e ty_ret_fvar;
    let ty_ret_ty = infertype e ty_ret_fvar in
    Hashtbl.remove e.lctx x;
    (match ty_arg_ty.inner, ty_ret_ty.inner with
    | Sort n1, Sort n2 -> {inner=Sort (if n2 = 0 then 0 else max n1 n2); loc=tm.loc}
    | Sort _, _ -> raise_at ty_ret (Error.TypeExpected { not_type = ty_ret; not_type_infer = ty_ret_ty })
    | _ -> raise_at ty_arg (Error.TypeExpected { not_type = ty_arg; not_type_infer = ty_arg_ty }))
  | App (f, arg) ->
    let f_type = infertype e f in
    (match f_type.inner with
    | Arrow (_, ty_arg, ty_ret) ->
      check_is_type e ty_arg;
      checktype e arg ty_arg;
      replace_bvar ty_ret 0 arg
    | _ -> raise_at f (Error.FunctionExpected { not_func = f; not_func_type = f_type; arg }))
  | Bvar _ -> raise_at tm (Error.InternalError "unexpected bound variable in infertype")
  | Fvar fvar ->
    (match Hashtbl.find_opt e.lctx fvar with
    | Some (_, ty) -> ty
    | None -> raise_at tm (Error.InternalError "unknown free variable in infertype"))
  | Sort n -> {inner=Sort (n + 1); loc=tm.loc}
  in 
  (* print_endline ("inferred type " ^ term_to_string e res ^ " for term " ^ term_to_string e tm); *)
  res


and check_is_type (e: ctx) (tm: term) : unit =
  (* print_endline ("checking " ^ term_to_string e tm ^ " is a type"); *)
  match tm.inner with
  | Hole m ->
    (match Hashtbl.find_opt e.metas m with
    | Some {ty=Some ty; _} -> if not (is_sort ty) then raise_at tm (Error.TypeExpected { not_type = tm; not_type_infer = ty }) else ()
    | _ -> ())
  | Name name ->
    (match Hashtbl.find_opt e.env name with
      | Some entry -> if not (is_sort entry.ty) then raise_at tm (Error.TypeExpected { not_type = tm; not_type_infer = entry.ty }) else ()
      | None -> raise_at tm (Error.UnknownName { name }))
  | Fun _ ->
    raise_at tm (Error.TypeExpected { not_type = tm; not_type_infer = tm })
  | Arrow (arg, ty_arg, ty_ret) ->
    check_is_type e ty_arg;
    let x = gen_fvar_id () in
    let ty_ret_fvar = replace_bvar ty_ret 0 {inner=Fvar x; loc=tm.loc} in
    Hashtbl.add e.lctx x (arg, ty_arg);
    check_is_type e ty_ret_fvar;
    Hashtbl.remove e.lctx x
  | App (f, arg) ->
    let f_type = try Some (infertype e f) with Error.ElabError {error_type = Error.CannotInferHole; _} -> None in

    (match f_type with
    | Some {inner=Arrow (_, ty_arg, ty_ret); _} -> 
      (* print_endline ("app checktype: checking that " ^ term_to_string e arg ^ " has type " ^ term_to_string e ty_arg);
      print_endline ("because f is " ^ term_to_string e f ^ " and has type " ^ term_to_string e f_type); *)
      checktype e arg ty_arg;
      if not (is_sort ty_ret) then raise_at tm (Error.TypeExpected { not_type = tm; not_type_infer = ty_ret }) else ()
    | Some v -> raise_at f (Error.FunctionExpected { not_func = f; not_func_type = v; arg })
    | None -> ())
  | Sort _ -> ()
  | Bvar _ -> raise_at tm (Error.InternalError "unexpected bound variable in check_is_type")
  | Fvar fvar ->
    (match Hashtbl.find_opt e.lctx fvar with
    | Some (_, ty) -> 
      let ty = whnf_beta e ty in
      if not (is_sort ty || match ty.inner with | Hole _ -> true | _ -> false) then raise_at tm (Error.TypeExpected { not_type = tm; not_type_infer = ty }) else ()
    | None -> raise_at tm (Error.InternalError "unknown free variable in check_is_type"))


let rec contains_fvar (tm: term) : bool =
  match tm.inner with
  | Fvar _ -> true
  | Fun (_, ty_arg, body) -> contains_fvar ty_arg || contains_fvar body
  | Arrow (_, ty_arg, ty_ret) -> contains_fvar ty_arg || contains_fvar ty_ret
  | App (f, arg) -> contains_fvar f || contains_fvar arg
  | _ -> false

(* Needs to be trusted for faithfulness of meaning. This returns tm unchanged
except for replacing metavariables with terms. *)
let rec replace_metas (e: ctx) (tm: term) : term =
  match tm.inner with
  | Hole m -> (match Hashtbl.find_opt e.metas m with
    | Some {sol=Some tm_sol; _} -> 
      if contains_fvar tm_sol then raise_at tm (Error.InternalError "hole contains free variables, should have been bound") else
      replace_metas e tm_sol
    | _ -> raise_at tm (Error.CannotInferHole))
  | Fun (arg, ty_arg, body) ->
    let ty_arg_filled = replace_metas e ty_arg in
    let body_filled = replace_metas e body in
    {inner=Fun (arg, ty_arg_filled, body_filled); loc=tm.loc}
  | Arrow (arg, ty_arg, ty_ret) ->
    let ty_arg_filled = replace_metas e ty_arg in
    let ty_ret_filled = replace_metas e ty_ret in
    {inner=Arrow (arg, ty_arg_filled, ty_ret_filled); loc=tm.loc}
  | App (f, arg) ->
    let f_filled = replace_metas e f in
    let arg_filled = replace_metas e arg in
    {inner=App (f_filled, arg_filled); loc=tm.loc}
  | _ -> tm

(* Needs to be trusted for faithfulness of meaning. This returns tm unchanged
except for replacing holes with metavariable spines. *)
let rec hole_to_meta (e: ctx) (stack: term list) (tm: term): term = 
  match tm.inner with
  | Hole m ->
    let types = List.rev stack in
    let meta = { ty = None; vartypes = types; sol = None } in
    Hashtbl.add e.metas m meta;
    (* App(App(App(tm, Bvar 2), Bvar 1), Bvar 0) *)
    let rec fold (tm: term) (level: int) : term =
      (match level with
      | 0 -> tm
      | n ->
        fold {inner=App (tm, {inner=Bvar (n - 1); loc=tm.loc}); loc=tm.loc} (n - 1))
    in
    fold {inner=Hole m; loc=tm.loc} (List.length stack)
  | Fun (arg, ty_arg, body) ->
    let ty_arg_meta = hole_to_meta e stack ty_arg in
    let body_meta = hole_to_meta e (ty_arg_meta :: stack) body in
    {inner=Fun (arg, ty_arg_meta, body_meta); loc=tm.loc}
  | Arrow (arg, ty_arg, ty_ret) ->
    let ty_arg_meta = hole_to_meta e stack ty_arg in
    let ty_ret_meta = hole_to_meta e (ty_arg_meta :: stack) ty_ret in
    {inner=Arrow (arg, ty_arg_meta, ty_ret_meta); loc=tm.loc}
  | App (f, arg) ->
    let f_meta = hole_to_meta e stack f in
    let arg_meta = hole_to_meta e stack arg in
    {inner=App (f_meta, arg_meta); loc=tm.loc}
  | _ -> tm

let union (l1: string list) (l2: string list) : string list =
  let set = Hashtbl.create 0 in
  List.iter (fun x -> Hashtbl.replace set x ()) l1;
  List.iter (fun x -> Hashtbl.replace set x ()) l2;
  Hashtbl.fold (fun key _ acc -> key :: acc) set []

let rec list_axioms_used (e: ctx) (tm: term) : string list =
  match tm.inner with
  | Name name -> 
    (match Hashtbl.find_opt e.env name with
    | Some {data = Theorem axioms; _} -> axioms
    | Some {data = Axiom; _} -> [name]
    | None -> raise_at tm (Error.UnknownName { name }))
  | Fun (_, ty_arg, body) -> union (list_axioms_used e ty_arg) (list_axioms_used e body)
  | Arrow (_, ty_arg, ty_ret) -> union (list_axioms_used e ty_arg) (list_axioms_used e ty_ret)
  | App (f, arg) -> union (list_axioms_used e f) (list_axioms_used e arg)
  | _ -> []

(* Needs to be trusted for faithfulness of meaning *)
let process_decl (e: ctx) (d: declaration) : unit =
  try match d.kind with
  | Theorem proof ->
    if Hashtbl.mem e.env d.name then raise (Error.ElabError { context = { loc = Some d.name_loc; decl_name = Some d.name }; error_type = Error.AlreadyDefined d.name }) else
    (* hole_to_meta only replaces holes explicitly typed in by the user as "_" with metavariable spines *)
    let ty_meta = hole_to_meta e [] d.ty in
    check_is_type e ty_meta;
    (* replace_metas only fills in metavariables *)
    let ty_filled = replace_metas e ty_meta in
    Hashtbl.clear e.metas;
    let proof_meta = hole_to_meta e [] proof in
    checktype e proof_meta ty_filled;
    let proof_filled = replace_metas e proof_meta in
    Hashtbl.clear e.metas;
    (* conv_to_kterm does a straightforward variant-to-variant conversion *)
    let ty_k = conv_to_kterm ty_filled in
    let proof_k = conv_to_kterm proof_filled in

    (try 
      let inferredType = KInfer.inferType e.kenv (Hashtbl.create 0) proof_k in
      let isValidProof = KInfer.isDefEq e.kenv (Hashtbl.create 0) inferredType ty_k in

      if isValidProof then
        (Hashtbl.add e.env d.name {name = d.name; ty = ty_filled; data = Theorem (list_axioms_used e proof_filled)};
        Hashtbl.add e.kenv d.name ty_k)
      else
        raise (Error.ElabError { context = { loc = Some d.name_loc; decl_name = Some d.name }; error_type = Error.InternalError ("kernel did not accept proof\n") })
    with KExceptions.TypeError msg ->
      raise (Error.ElabError { context = { loc = Some d.name_loc; decl_name = Some d.name }; error_type = Error.KernelError { kernel_exn = msg } }))
  | Axiom -> 
    if Hashtbl.mem e.env d.name then raise (Error.ElabError { context = { loc = Some d.name_loc; decl_name = Some d.name }; error_type = Error.AlreadyDefined d.name }) else
    (* hole_to_meta only replaces holes explicitly typed in by the user as "_" with metavariable spines *)
    let ty_meta = hole_to_meta e [] d.ty in
    check_is_type e ty_meta;
    (* replace_metas only fills in metavariables *)
    let ty_filled = replace_metas e ty_meta in
    Hashtbl.clear e.metas;
    (* conv_to_kterm does a straightforward variant-to-variant conversion *)
    let ty_k = conv_to_kterm ty_filled in
    Hashtbl.add e.env d.name {name = d.name; ty = ty_filled; data = Axiom};
    Hashtbl.add e.kenv d.name ty_k 
  with Error.ElabError x ->
    raise (Error.ElabError { x with context = { x.context with decl_name = Some d.name } })