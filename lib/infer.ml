open Term

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
      | Forall (expected_arg_type, return_type) -> 
          (* TODO: replace this with checking for definitional equality *)
        if expected_arg_type = inferred_arg_type then
          return_type
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
