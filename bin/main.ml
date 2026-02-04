open System_e_kernel
open Term

let inferType (env : environment) (localCtx : localcontext) (t : term) : term =
  match t with
  | Const name -> failwith "infer type of const"
  | Fvar name -> failwith "infer type of a free variable"
  | Bvar idx -> failwith "infer type of a bound variable"
  | App (func, arg) -> failwith "infer type of function application"
  | Lam (domainType, body) -> failwith "infer type of a function"
  | Forall (domainType, returnType) -> failwith "infer type of a forall"
  | Sort level -> failwith "infer type of a sort"

let () = print_endline "test"

