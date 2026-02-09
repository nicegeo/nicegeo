open Term

(* Substitute the bound variable at index `bvar_idx` (relative to the top level
term, so what would have been at index `bvar_idx` in the localcontext stack for
the original term) with the provided value `bvar_val` in the term `t`*)
let rec subst_bvar (t: term) (bvar_idx: int) (bvar_val: term) : term = 
  match t with
    | Const _ | Sort _ | Fvar _ -> t
    | Bvar idx -> if bvar_idx = idx then bvar_val else Bvar idx
    | Lam (domain_type, body) -> 
        (* Add 1 to bvar_idx to account for the fact that a Lam introduces a bound
        variable *)
        Lam (subst_bvar domain_type bvar_idx bvar_val, subst_bvar body (bvar_idx + 1) bvar_val)
    | Forall (domain_type, ret_type) ->
        Forall (subst_bvar domain_type bvar_idx bvar_val, subst_bvar ret_type (bvar_idx + 1) bvar_val)
    | App (func, arg) -> 
        let func_subst = subst_bvar func bvar_idx bvar_val in
        let arg_subst = subst_bvar arg bvar_idx bvar_val in
        App (func_subst, arg_subst)

let rec inferType (env : environment) (localCtx : localcontext) (t : term) : term =
  match t with
  | Const name -> (
      try Hashtbl.find env name
      with Not_found -> failwith ("unknown constant: " ^ name)
    )
  (* TODO: remove this (since we're not using free variables anymore) *)
  | Fvar name -> (
      try Hashtbl.find env name
      with Not_found -> failwith ("unknown free variable: " ^ name)
    )
  | Bvar idx -> (
      try List.nth localCtx idx
      with Failure _ | Invalid_argument _ ->
        failwith ("bound variable index out of scope: " ^ string_of_int idx)
    )
  | App (func, arg) -> (
    let func_type = inferType env localCtx func in
    let inferred_arg_type = inferType env localCtx arg in
    match func_type with
      | Forall (expected_arg_type, _) -> 
          (* TODO: replace this with checking for definitional equality *)
        if expected_arg_type = inferred_arg_type then
          (* TODO: check if this is the right approach *)
          (* The actual type of the function application can depend on the
          actual value that it's evaluated at so we need to evaluate the function
          at the given argument and then infer the type of the result *)
          let body_evaluated_at_arg = match func with
            | Lam (_, body) -> subst_bvar body 0 arg
            | _ -> failwith "Expected Lam for `func` in application" in
          inferType env localCtx body_evaluated_at_arg
        else failwith "Function called with invalid argument type"
      | _ -> failwith "Tried to apply non-function to an argument"
  )
  | Lam (domainType, body) -> (
      (* Put the type of the argument at the start of the local context list so
      that Bvar 0 in the lambda points to domainType, and Bvar 1 (for example)
      would point to what is now Bvar 0 (since Bvar 0 at that point would point
      to this function's argument and Bvar 1 would point to the next bound variable)*)
      let new_local_ctx = domainType :: localCtx in
      let ret_type = inferType env new_local_ctx body in
      Forall (domainType, ret_type)
    )
  | Forall (_domainType, _returnType) -> failwith "infer type of a forall"
  | Sort _level -> failwith "infer type of a sort"

let type0 = Sort 0                 (* "Type" *)
let pi (a : term) (b : term) = Forall (a, b)  (* Π (_ : a), b *)
let app2 f x y = App (App (f, x), y)
let exists_ty : term =
  pi type0
    (pi (pi (Bvar 0) type0)   (* B : A -> Type *)
        type0)                (* Exists A B : Type *)
let exists_intro_ty : term =
  pi type0
    (pi (pi (Bvar 0) type0)          (* B : A -> Type *)
      (pi (Bvar 1)                   (* a : A   (A is Bvar 1 here) *)
        (pi (App (Bvar 1, Bvar 0))   (* b : B a *)
          (app2 (Const "Exists") (Bvar 3) (Bvar 2)))))  (* Exists A B *)

let add_exists (env : environment) : unit =
  Hashtbl.replace env "Exists" exists_ty;
  Hashtbl.replace env "Exists.intro" exists_intro_ty


let mk_axioms_env () =
  let env = Hashtbl.create 16 in
  Hashtbl.add env "Point" (Sort 1);
  Hashtbl.add env "Line" (Sort 1);
  Hashtbl.add env "Circle" (Sort 1);
  env

