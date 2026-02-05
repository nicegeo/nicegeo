open Term

let inferType (env : environment) (localCtx : localcontext) (t : term) : term =
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
  | Lam (_domainType, _body) -> failwith "infer type of a function"
  | Forall (_domainType, _returnType) -> failwith "infer type of a forall"
  | Sort _level -> failwith "infer type of a sort"
