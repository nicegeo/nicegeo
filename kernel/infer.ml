open Term
open Exceptions

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
        if isDefEq env localCtx expected_arg_type inferred_arg_type then
          (* The actual type of the function application can depend on the
          actual value that it's evaluated at so we need to substitute the arg
          for any bvars referring to this arg in the return_type. *)
          subst_bvar return_type 0 arg
        else 
          let msg = 
            Printf.sprintf 
              "Function called with invalid argument type.\n\
               Local Context:\n%s\n\
               Term: %s\n\
               Func: %s\n\
               Arg: %s\n\n\
               Func Type: %s\n\
               Expected Arg Type: %s\n\
               Inferred Arg Type: %s\n"
              (context_to_string localCtx)
              (term_to_string t)
              (term_to_string func)
              (term_to_string arg)
              (term_to_string func_type)
              (term_to_string expected_arg_type)
              (term_to_string inferred_arg_type)
          in
          failwith msg
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
        | _ -> 
          raise (TypeError {env; ctx = localCtx; trm = t; err_kind = ForallSortError (domainTypeType, returnTypeType)}))
  | Sort level -> Sort (level + 1)

and isDefEq (env : environment) (localCtx : localcontext) (t1 : term) (t2 : term) : bool =
  let t1_reduced = reduce env localCtx t1 in
  let t2_reduced = reduce env localCtx t2 in
  t1_reduced = t2_reduced

and reduce (env : environment) (localCtx : localcontext) (t : term) : term =
  match t with
  | App (Lam (domainType, body), arg) -> (* beta reduction i think *)
      let arg_type = inferType env localCtx arg in
      if domainType = arg_type then
        let substed_body = subst_bvar body 0 arg in
        reduce env localCtx substed_body
      else
        failwith "Function called with invalid argument type during reduction"
  | App (func, arg) -> 
      let reduced_func = reduce env localCtx func in
      let reduced_arg = reduce env localCtx arg in
      App (reduced_func, reduced_arg)
  | Lam (domainType, body) -> 
    (* need to subst fvar *)
    let new_fvar_name = gen_new_fvar_name () in
    let domainTypeReduced = reduce env localCtx domainType in
    let newLocalCtx = 
      let t = Hashtbl.copy localCtx in
      Hashtbl.replace t new_fvar_name domainTypeReduced;
      t
    in
    let substed_body = subst_bvar body 0 (Fvar new_fvar_name) in
    let bodyReduced = reduce env newLocalCtx substed_body in
    Lam (domainTypeReduced, rebind_bvar bodyReduced 0 new_fvar_name)
  | Forall (domainType, returnType) -> 
    let new_fvar_name = gen_new_fvar_name () in
    let domainTypeReduced = reduce env localCtx domainType in
    let newLocalCtx = 
      let t = Hashtbl.copy localCtx in
      Hashtbl.replace t new_fvar_name domainTypeReduced;
      t
    in
    let substed_return_type = subst_bvar returnType 0 (Fvar new_fvar_name) in
    let returnTypeReduced = reduce env newLocalCtx substed_return_type in
    Forall (domainTypeReduced, rebind_bvar returnTypeReduced 0 new_fvar_name)
  | _ -> t

and isSort (env : environment) (t : term) : bool =
  match reduce env (Hashtbl.create 0) t with
  | Sort _ -> true
  | _ -> false


