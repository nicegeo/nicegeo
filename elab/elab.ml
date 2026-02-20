open Decl
open Term
open Convert
(* open Print *)
module KInfer = System_e_kernel.Infer
module KTerm = System_e_kernel.Term

type t = {
  env : (string, term) Hashtbl.t; (* elaboration-level environment *)
  kenv : KTerm.environment; (* kernel-level environment (should be kept in sync with env) *)

  metas : (int, term) Hashtbl.t; (* mapping from hole IDs to values *)
  lctx : (int, string option * term) Hashtbl.t; (* local context id to name and type. *)
}
let rec term_to_string (e: t) (tm: term) : string =
  match tm with
  | Name name -> name
  | Bvar idx -> "Bvar(" ^ string_of_int idx ^ ")"
  | Fvar idx -> 
    Hashtbl.find_opt e.lctx idx |> (function
      | Some (Some name, _) -> name
      | _ -> "Fvar(" ^ string_of_int idx ^ ")")
  | Hole idx -> "Hole(" ^ string_of_int idx ^ ")"
  | Fun (arg, ty_arg, body) ->
      let arg_str = match arg with Some a -> a | None -> "_" in
      "(fun (" ^ arg_str ^ " : " ^ term_to_string e ty_arg ^ ") => " ^ term_to_string e body ^ ")"
  | Arrow (arg, ty_arg, ty_ret) ->
      let arg_str = match arg with Some a -> a | None -> "_" in
      "(" ^ arg_str ^ " : " ^ term_to_string e ty_arg ^ " -> " ^ term_to_string e ty_ret ^ ")"
  | App (f, arg) ->
      "(" ^ term_to_string e f ^ " " ^ term_to_string e arg ^ ")"
  | Sort n -> "Sort(" ^ string_of_int n ^ ")"

let create () : t = {
  env = Hashtbl.create 16;
  kenv = Hashtbl.create 16;

  metas = Hashtbl.create 16;
  lctx = Hashtbl.create 16;
}


let rec hole_valid (e: t) (m: int) (tm: term) : bool =
  match tm with
  | Hole m' -> if m = m' then false else (match Hashtbl.find_opt e.metas m' with
    | Some tm_sol -> hole_valid e m tm_sol
    | None -> false)
  | Fvar _ -> false (* only first order unification for now *)
  | Fun (_, ty, body) -> hole_valid e m ty && hole_valid e m body
  | Arrow (_, ty, ret) -> hole_valid e m ty && hole_valid e m ret
  | App (f, arg) -> hole_valid e m f && hole_valid e m arg
  | _ -> true

let rec whnf_beta (tm: term) : term =
  match tm with
  | App (f, arg) -> 
    let fn = whnf_beta f in
    (match fn with
    | Fun (_, _, body) -> whnf_beta (replace_bvar body 0 arg)
    | _ -> App (fn, arg))
  | _ -> tm


let rec unify (e: t) (t1: term) (t2: term) : unit =
  (* print_endline ("unifying " ^ term_to_string e t1 ^ " and " ^ term_to_string e t2); *)
  let t1 = whnf_beta t1 in
  let t2 = whnf_beta t2 in
  (* t1 and t2 should be closed under the current e *)
  match (t1, t2) with
  | Hole m1, Hole m2 ->
    (match (Hashtbl.find_opt e.metas m1, Hashtbl.find_opt e.metas m2) with
    | Some tm1_sol, Some tm2_sol -> unify e tm1_sol tm2_sol
    | Some tm1_sol, None -> unify e tm1_sol t2
    | None, Some tm2_sol -> unify e t1 tm2_sol
    | None, None -> ())
  | Hole m, _ ->
    if hole_valid e m t2 then
      Hashtbl.add e.metas m t2
    else
      failwith "could not unify, hole is not valid"
  | _, Hole m ->
    if hole_valid e m t1 then
      Hashtbl.add e.metas m t1
    else
      failwith "could not unify, hole is not valid"
  | Name n1, Name n2 when n1 = n2 -> ()
  | Fun (_, ty_arg1, body1), Fun (_, ty_arg2, body2) ->
    unify e ty_arg1 ty_arg2;
    let x = gen_fvar_id () in
    let body1_fvar = replace_bvar body1 0 (Fvar x) in
    let body2_fvar = replace_bvar body2 0 (Fvar x) in
    Hashtbl.add e.lctx x (None, ty_arg1);
    unify e body1_fvar body2_fvar;
    Hashtbl.remove e.lctx x
  | Arrow (_, ty_arg1, ty_ret1), Arrow (_, ty_arg2, ty_ret2) ->
    unify e ty_arg1 ty_arg2;
    let x = gen_fvar_id () in
    let ty_ret1_fvar = replace_bvar ty_ret1 0 (Fvar x) in
    let ty_ret2_fvar = replace_bvar ty_ret2 0 (Fvar x) in
    Hashtbl.add e.lctx x (None, ty_arg1);
    unify e ty_ret1_fvar ty_ret2_fvar;
    Hashtbl.remove e.lctx x
  | App (f1, arg1), App (f2, arg2) ->
    unify e f1 f2;
    unify e arg1 arg2
  | Sort n1, Sort n2 when n1 = n2 -> ()
  | Bvar idx1, Bvar idx2 when idx1 = idx2 -> ()
  | Fvar idx1, Fvar idx2 when idx1 = idx2 -> ()
  | _ -> failwith ("failed to unify non-matching terms " ^ term_to_string e t1 ^ " and " ^ term_to_string e t2)

(* checks that tm has expected type ty, trying to fill in metas? *)
(* if it fails it throws an exception. todo: use actual exceptions *)
let rec checktype (e: t) (tm: term) (ty: term) : unit =
  (* print_endline ("checking " ^ term_to_string e tm ^ " has type " ^ term_to_string e ty); *)
  match tm with 
  | Hole m ->
    (match Hashtbl.find_opt e.metas m with
    | Some tm_sol -> checktype e tm_sol ty
    | None -> ()) (* todo keep track of hole types i think *)
  | Name name ->
    (match Hashtbl.find_opt e.env name with
      | Some ty_sol -> unify e ty_sol ty
      | None -> failwith ("unknown identifier: " ^ name))
  | Fun (arg, ty_arg, body) ->
    (match ty with
    | Arrow (_, ty_arg_expected, ty_ret) ->
        unify e ty_arg ty_arg_expected;
        (* free variableify the body *)
        let x = gen_fvar_id () in
        let body_fvar = replace_bvar body 0 (Fvar x) in
        let ty_ret_fvar = replace_bvar ty_ret 0 (Fvar x) in
        Hashtbl.add e.lctx x (arg, ty_arg);
        checktype e body_fvar ty_ret_fvar;
        Hashtbl.remove e.lctx x
    | _ -> failwith "expected fun to have arrow type")
  | Arrow (_, ty_arg, ty_ret) ->
    (match ty with
    | Sort _ -> 
      check_is_type e ty_arg;
      let x = gen_fvar_id () in
      let ty_ret_fvar = replace_bvar ty_ret 0 (Fvar x) in
      Hashtbl.add e.lctx x (None, ty_arg);
      check_is_type e ty_ret_fvar;
      Hashtbl.remove e.lctx x (* technically should check universes here *)
    | _ -> failwith "expected arrow to have sort type")
  | App (f, arg) ->
    let f_type = infertype e f in
    (match f_type with
    | Arrow (_, ty_arg, ty_ret) -> 
      let ty_ret_replaced = replace_bvar ty_ret 0 arg in
      unify e ty ty_ret_replaced;
      checktype e arg ty_arg
    | _ -> failwith "expected a function type in application")
  | Sort n -> (match ty with
    | Sort m when m > n -> ()
    | _ -> failwith "expected a higher sort in sort typing")
  | Bvar _ -> failwith "unexpected bound variable in checktype"
  | Fvar fvar -> 
    (match Hashtbl.find_opt e.lctx fvar with
    | Some (_, lctx_ty) -> unify e ty lctx_ty
    | None -> failwith "unknown free variable in checktype")

    (* i sort of inlined some parts of infertype here but erm *)

(* entirely vibe coded surely it works *)
and infertype (e: t) (tm: term) : term =
  (* print_endline ("inferring type of " ^ term_to_string e tm); *)
  let res = match tm with
  | Hole _ -> failwith "cannot infer type of hole"
  | Name name ->
    (match Hashtbl.find_opt e.env name with
      | Some ty -> ty      | None -> failwith ("unknown identifier: " ^ name))
  | Fun (arg, ty_arg, body) ->
    let x = gen_fvar_id () in
    let body_fvar = replace_bvar body 0 (Fvar x) in
    Hashtbl.add e.lctx x (arg, ty_arg);
    let ty_body = infertype e body_fvar in
    Hashtbl.remove e.lctx x;
    Arrow (arg, ty_arg, ty_body)
  | Arrow (arg, ty_arg, ty_ret) ->
    let ty_arg_ty = infertype e ty_arg in
    let x = gen_fvar_id () in
    let ty_ret_fvar = replace_bvar ty_ret 0 (Fvar x) in
    Hashtbl.add e.lctx x (arg, ty_arg);
    let ty_ret_ty = infertype e ty_ret_fvar in
    Hashtbl.remove e.lctx x;
    (match ty_arg_ty, ty_ret_ty with
    | Sort n1, Sort n2 -> Sort (max n1 n2)
    | _ -> failwith "expected types of arrow to be sorts")
  | App (f, arg) ->
    let f_type = infertype e f in
    (match f_type with
    | Arrow (_, ty_arg, ty_ret) ->
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

and check_is_type (e: t) (tm: term) : unit =
  (* print_endline ("checking " ^ term_to_string e tm ^ " is a type"); *)
  match tm with
  | Hole m ->
    (match Hashtbl.find_opt e.metas m with
    | Some tm_sol -> check_is_type e tm_sol
    | None -> ())
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
    let f_type = infertype e f in
    (match f_type with
    | Arrow (_, ty_arg, ty_ret) -> 
      (* print_endline ("app checktype: checking that " ^ term_to_string e arg ^ " has type " ^ term_to_string e ty_arg);
      print_endline ("because f is " ^ term_to_string e f ^ " and has type " ^ term_to_string e f_type); *)
      checktype e arg ty_arg;
      if not (is_sort ty_ret) then failwith "expected return type of function to be a sort"
    | _ -> failwith "expected a function type in application")
  | Sort _ -> ()
  | Bvar _ -> failwith "unexpected bound variable in check_is_type"
  | Fvar fvar ->
    (match Hashtbl.find_opt e.lctx fvar with
    | Some (_, ty) -> if not (is_sort ty) then failwith "expected type of free variable to be a sort" else ()
    | None -> failwith "unknown free variable in check_is_type")


let rec replace_metas (e: t) (tm: term) : term =
  match tm with
  | Hole m -> (match Hashtbl.find_opt e.metas m with
    | Some tm_sol -> replace_metas e tm_sol
    | None -> failwith ("unfilled hole in replace_metas: " ^ term_to_string e tm))
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

let process_decl (e: t) (d: declaration) : unit =
  match d with
  | Theorem (name, ty, proof) ->
    if Hashtbl.mem e.env name then failwith ("theorem " ^ name ^ " already defined.\n") else
    check_is_type e ty;
    let ty_filled = replace_metas e ty in
    Hashtbl.clear e.metas;
    checktype e proof ty;
    let proof_filled = replace_metas e proof in
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
    check_is_type e ty;
    let ty_filled = try replace_metas e ty with Failure msg -> failwith ("failed to replace metas in axiom " ^ name ^ " of type " ^ term_to_string e ty ^ ": " ^ msg) in

    Hashtbl.clear e.metas;
    let ty_k = conv_to_kterm ty_filled in
    Hashtbl.add e.env name ty_filled;
    Hashtbl.add e.kenv name ty_k 


let create_with_env () : t = 
  let e = create () in
  let ic = open_in "elab/env.txt" in
  let lexbuf = Lexing.from_channel ic in
  let decls = Parser.main Lexer.token lexbuf in
  let _ = List.map (process_decl e) decls in
  e

