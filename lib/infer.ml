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

(* In the term t, converts a free variable fvar_name to a bound variable with index 
bvar_idx relative to the top level. Replaces all `FVar fvar_name` references with the
appropriate `Bvar idx` reference. This will return a term that by itself will have 
out-of-bounds Bvar references, so it should be placed in an appropriate Lam/Forall 
to be valid. *)
let rec rebind_bvar (t: term) (bvar_idx: int) (fvar_name: string) : term = 
  match t with
    | Const _ | Sort _  | Bvar _ -> t
    | Fvar name -> if fvar_name = name then Bvar bvar_idx else t
    | Lam (domain_type, body) -> 
        (* Add 1 to bvar_idx to account for the fact that a Lam introduces a bound
        variable *)
        Lam (rebind_bvar domain_type bvar_idx fvar_name, rebind_bvar body (bvar_idx + 1) fvar_name)
    | Forall (domain_type, ret_type) ->
        Forall (rebind_bvar domain_type bvar_idx fvar_name, rebind_bvar ret_type (bvar_idx + 1) fvar_name)
    | App (func, arg) -> 
        let func_subst = rebind_bvar func bvar_idx fvar_name in
        let arg_subst = rebind_bvar arg bvar_idx fvar_name in
        App (func_subst, arg_subst)

let fvar_counter = ref 0
let gen_new_fvar_name () : string = 
  let name = "fvar" ^ string_of_int !fvar_counter in
  incr fvar_counter;
  name

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
            let body' = subst_bvar body 0 normalArg in
            reduce env body'
        | _ -> App (normalFunc, normalArg))
    | Lam (dom, body) -> Lam (reduce env dom, reduce env body)
    | Forall (dom, body) -> Forall (reduce env dom, reduce env body)
    | Sort lvl -> Sort lvl

(* Two terms are definitionally equal if once fully reduced
  they are literally equal. *)
let isDefEq (env : environment) (t1 : term) (t2 : term) : bool =
    (reduce env t1) = (reduce env t2)

let isSort (env : environment) (t : term) : bool =
  match reduce env t with
  | Sort _ -> true
  | _ -> false

let rec inferType (env : environment) (localCtx : localcontext) (t : term) : term =
  match t with
  | Const name -> (
      try Hashtbl.find env name
      with Not_found -> failwith ("unknown constant: " ^ name)
    )
  | Fvar name -> (
      try Hashtbl.find localCtx name
      with Not_found -> failwith ("unknown free variable: " ^ name)
    )
  | Bvar idx -> (
      failwith ("bound variable index out of scope: " ^ string_of_int idx)
    )
  | App (func, arg) -> (
    let func_type = inferType env localCtx func in
    let inferred_arg_type = inferType env localCtx arg in
    match func_type with
      | Forall (expected_arg_type, return_type) -> 
        if isDefEq env expected_arg_type inferred_arg_type then
          (* The actual type of the function application can depend on the
          actual value that it's evaluated at so we need to substitute the arg
          for any bvars referring to this arg in the return_type. *)
          subst_bvar return_type 0 arg
        else failwith "Function called with invalid argument type"
      | _ -> failwith "Tried to apply non-function to an argument"
  )
  | Lam (domainType, body) -> (
      let new_fvar_name = gen_new_fvar_name () in
      let domainTypeType = inferType env localCtx domainType in
      if not (isSort env domainTypeType) then
        failwith "invalid domain type for lambda"
      else
      (* add mapping new_fvar_name -> domainType to localCtx in recursive call *)
      (* this is fine because domainType won't have any unresolved BVars *)
      let newLocalCtx = 
        let t = Hashtbl.copy localCtx in
        Hashtbl.replace t new_fvar_name domainType;
        t
      in
      (* replace bound variable with new free variable *)
      let substed_term = subst_bvar body 0 (Fvar new_fvar_name) in
      let ret_type = inferType env newLocalCtx substed_term in
      (* replace the free variable with bound variable *)
      let rebound_type = rebind_bvar ret_type 0 new_fvar_name in
      Forall (domainType, rebound_type)
    )
  | Forall (domainType, returnType) -> (
      let domainTypeType = inferType env localCtx domainType in
      let returnTypeType = 
        let new_fvar_name = gen_new_fvar_name () in
        let newLocalCtx = 
          let t = Hashtbl.copy localCtx in
          Hashtbl.replace t new_fvar_name domainType;
          t
        in
        let substed_return_type = subst_bvar returnType 0 (Fvar new_fvar_name) in
        inferType env newLocalCtx substed_return_type in
      match (domainTypeType, returnTypeType) with
        | (Sort u, Sort v) -> (
          if v = 0 then Sort 0  (* Prop is impredicative *)
          else Sort (max u v)
        )
        | (Sort _, _) -> failwith "Return type of a Forall must be a sort"
        | (_, Sort _) -> failwith "Domain type of a Forall must be a sort"
        | _ -> failwith "Domain and return types of a Forall must be sorts"
    )
  | Sort level -> Sort (level + 1)