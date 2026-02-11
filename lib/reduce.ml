open Term

(* Replace all bvars of `t` referring to `idx` with `replace`. *)
let rec instantiateBvarAtIdx (t : term) (replace : term) (bvarIdx : int) : term =
  match t with
  | Bvar idx -> if idx = bvarIdx then replace else t
  | Lam (dom, body) -> 
    let dom' = instantiateBvarAtIdx dom replace bvarIdx in
    let body' = instantiateBvarAtIdx body replace (bvarIdx + 1) in
    Lam (dom', body')
  | Forall (dom, body) ->
    let dom' = instantiateBvarAtIdx dom replace bvarIdx in
    let body' = instantiateBvarAtIdx body replace (bvarIdx + 1) in
    Forall (dom', body')
  | App (func, arg) ->
    let func = instantiateBvarAtIdx func replace bvarIdx in
    let arg = instantiateBvarAtIdx arg replace bvarIdx in
    App (func, arg)
  | Const _ | Sort _ | Fvar _ -> t

let instantiateBvar (t : term) (replace : term) : term =
  instantiateBvarAtIdx t replace 0

(* Reduce the given term as much as possible. *)
let rec reduce (env : environment) (t : term) : term =
    match t with
    | Const name -> Const name
    | Fvar name -> Fvar name
    | Bvar idx -> Bvar idx
    | App (func, arg) ->
        let normalFunc = reduce env func in
        let normalArg = reduce env arg in
        (match normalFunc with
        | Lam (_, body) ->
            let body' = instantiateBvar body normalArg in
            reduce env body'
        | _ -> App (normalFunc, normalArg))
    | Lam (dom, body) -> Lam (reduce env dom, reduce env body)
    | Forall (dom, body) -> Forall (reduce env dom, reduce env body)
    | Sort lvl -> Sort lvl

(* Two terms are definitionally equal if once fully reduced
  they are literally equal. *)
let isDefEq (env : environment) (t1 : term) (t2 : term) : bool =
    (reduce env t1) = (reduce env t2)