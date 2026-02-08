open Term

let rec inferType (env : environment) (localCtx : localcontext) (t : term) : term =
  match t with
  | Const name -> (
      try Hashtbl.find env name
      with Not_found -> failwith ("unknown constant: " ^ name)
    )
  | Fvar name -> (
      try Hashtbl.find env name
      with Not_found -> failwith ("unknown free variable: " ^ name)
    )
  | Bvar idx -> (
      try List.nth localCtx idx
      with Failure _ | Invalid_argument _ ->
        failwith ("bound variable index out of scope: " ^ string_of_int idx)
    )
  | App (_func, _arg) -> failwith "infer type of function application"
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
