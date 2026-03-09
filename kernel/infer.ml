open Term
open Exceptions

(* Substitute the bound variable at index `bvar_idx` (relative to the top level
term, so what would have been at index `bvar_idx` in the localcontext stack for
the original term) with the provided value `bvar_val` in the term `t`*)
let rec subst_bvar (t : term) (bvar_idx : int) (bvar_val : term) : term =
  match t with
  | Const _ | Sort _ | Fvar _ -> t
  | Bvar idx -> if bvar_idx = idx then bvar_val else Bvar idx
  | Lam (domain_type, body) ->
      (* Add 1 to bvar_idx to account for the fact that a Lam introduces a bound
        variable *)
      Lam
        (subst_bvar domain_type bvar_idx bvar_val, subst_bvar body (bvar_idx + 1) bvar_val)
  | Forall (domain_type, ret_type) ->
      Forall
        ( subst_bvar domain_type bvar_idx bvar_val,
          subst_bvar ret_type (bvar_idx + 1) bvar_val )
  | App (func, arg) ->
      let func_subst = subst_bvar func bvar_idx bvar_val in
      let arg_subst = subst_bvar arg bvar_idx bvar_val in
      App (func_subst, arg_subst)

(* In the term t, converts a free variable fvar_name to a bound variable with index 
bvar_idx relative to the top level. Replaces all `FVar fvar_name` references with the
appropriate `Bvar idx` reference. This will return a term that by itself will have 
out-of-bounds Bvar references, so it should be placed in an appropriate Lam/Forall 
to be valid. *)
let rec rebind_bvar (t : term) (bvar_idx : int) (fvar_name : string) : term =
  match t with
  | Const _ | Sort _ | Bvar _ -> t
  | Fvar name -> if fvar_name = name then Bvar bvar_idx else t
  | Lam (domain_type, body) ->
      (* Add 1 to bvar_idx to account for the fact that a Lam introduces a bound
        variable *)
      Lam
        ( rebind_bvar domain_type bvar_idx fvar_name,
          rebind_bvar body (bvar_idx + 1) fvar_name )
  | Forall (domain_type, ret_type) ->
      Forall
        ( rebind_bvar domain_type bvar_idx fvar_name,
          rebind_bvar ret_type (bvar_idx + 1) fvar_name )
  | App (func, arg) ->
      let func_subst = rebind_bvar func bvar_idx fvar_name in
      let arg_subst = rebind_bvar arg bvar_idx fvar_name in
      App (func_subst, arg_subst)

let fvar_counter = ref 0

let gen_new_fvar_name () : string =
  let name = "fvar" ^ string_of_int !fvar_counter in
  incr fvar_counter;
  name

(* Reduce a term to normal form *)
let rec reduce (env : environment) (localCtx : localcontext) (t : term) : term =
  match t with
  | App (func, arg) -> (
      (* we need to reduce the func before matching if it's a Lam in the case of nested applications *)
      let reduced_func = reduce env localCtx func in
      let reduced_arg = reduce env localCtx arg in
      match reduced_func with
      | Lam (_, body) ->
          (* beta reduction---substitute bound variable *)
          let substed_body = subst_bvar body 0 reduced_arg in
          reduce env localCtx substed_body
      | _ -> App (reduced_func, reduced_arg))
  | Lam (domainType, body) ->
      (* substitute free variable in lambda *)
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
      (* substitute free variable in forall *)
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

(* Determine if a term is a Sort *)
let isSort (env : environment) (t : term) : bool =
  match reduce env (Hashtbl.create 0) t with Sort _ -> true | _ -> false

(* Definitional equality: reduce and check exact equality *)
let isDefEq (env : environment) (localCtx : localcontext) (t1 : term) (t2 : term) : bool =
  let t1_reduced = reduce env localCtx t1 in
  let t2_reduced = reduce env localCtx t2 in
  t1_reduced = t2_reduced

(*
 * Core type inference algorithm.
 * When this fails, throws a TypeError.
 *)
let rec inferType (env : environment) (localCtx : localcontext) (t : term) : term =
  match t with
  | Const name -> (
      try Hashtbl.find env name
      with Not_found ->
        (* Error: Unknown constant *)
        let err_kind = UnknownConstError name in
        raise (TypeError { env; ctx = localCtx; trm = t; err_kind }))
  | Fvar name -> (
      try Hashtbl.find localCtx name
      with Not_found ->
        (* Error: Unknown free variable *)
        let err_kind = UnknownFreeVarError name in
        raise (TypeError { env; ctx = localCtx; trm = t; err_kind }))
  | Bvar idx ->
      (* Error: Bound variable out of scope *)
      let err_kind = BoundVarScopeError idx in
      raise (TypeError { env; ctx = localCtx; trm = t; err_kind })
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
            (* Error: Invalid argument type *)
            let err_kind =
              AppArgTypeError (func, arg, func_type, expected_arg_type, inferred_arg_type)
            in
            raise (TypeError { env; ctx = localCtx; trm = t; err_kind })
      | _ ->
          (* Error: Tried to apply non-function to an argument *)
          let err_kind = AppNonFuncError in
          raise (TypeError { env; ctx = localCtx; trm = t; err_kind }))
  | Lam (domainType, body) ->
      let new_fvar_name = gen_new_fvar_name () in
      let domainTypeType = inferType env localCtx domainType in
      if not (isSort env domainTypeType) then
        (* Invalid domain type for lambda *)
        let err_kind = LamDomainError in
        raise (TypeError { env; ctx = localCtx; trm = t; err_kind })
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
        inferType env newLocalCtx substed_return_type
      in
      let domainTypeType = reduce env localCtx domainTypeType in
      let returnTypeType = reduce env localCtx returnTypeType in
      match (domainTypeType, returnTypeType) with
      | Sort u, Sort v ->
          if v = 0 then Sort 0 (* Prop is impredicative *) else Sort (max u v)
      | _ ->
          (* Error: domain and return type of forall both need to be sorts *)
          let ctx = localCtx in
          let trm = t in
          let err_kind = ForallSortError (domainTypeType, returnTypeType) in
          raise (TypeError { env; ctx; trm; err_kind }))
  | Sort level -> Sort (level + 1)

(* Type-checks and adds a theorem to the environment, throwing a TypeError on failure. *)
let add_theorem (env : environment) (name : string) (theorem_type : term) (proof : term) :
    unit =
  let local_ctx = Hashtbl.create 0 in
  match Hashtbl.find_opt env name with
  | Some _ ->
      (* Error: Name already defined *)
      let err_kind = AlreadyDefined name in
      raise (TypeError { env; ctx = local_ctx; trm = proof; err_kind })
  | None ->
      let typetype = inferType env local_ctx theorem_type in
      if not (isSort env typetype) then
        (* Error: Theorem type must be a sort *)
        let err_kind = LamDomainError in
        raise (TypeError { env; ctx = local_ctx; trm = theorem_type; err_kind })
      else
        let proof_type = inferType env local_ctx proof in
        if not (isDefEq env local_ctx proof_type theorem_type) then
          (* Error: Proof does not match theorem type *)
          let err_kind = TypeMismatchError (theorem_type, proof_type) in
          raise (TypeError { env; ctx = local_ctx; trm = proof; err_kind })
        else Hashtbl.add env name theorem_type

let add_axiom (env : environment) (name : string) (axiomType : term) : unit =
  let localCtx = Hashtbl.create 0 in
  match Hashtbl.find_opt env name with
  | Some _ ->
      (* Error: Name already defined *)
      let err_kind = AlreadyDefined name in
      raise (TypeError { env; ctx = localCtx; trm = axiomType; err_kind })
  | None ->
      let typetype = inferType env localCtx axiomType in
      if not (isSort env typetype) then
        (* Error: Axiom type must be a sort *)
        let err_kind = LamDomainError in
        raise (TypeError { env; ctx = localCtx; trm = axiomType; err_kind })
      else Hashtbl.add env name axiomType

(** The internal kernal functionality is exposed in an Internals module for testing
    purposes. These functions are not meant to be interacted with by non-kernel code
    otherwise, but OCaml does not have a good way to enforce this. *)
module Internals = struct
  let subst_bvar = subst_bvar
  let rebind_bvar = rebind_bvar
  let isSort = isSort
end
