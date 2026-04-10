open Term
open Exceptions

type environment = {
  types : (string, term) Hashtbl.t;
  defs : (string, term) Hashtbl.t;
}

module Internals = struct
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
          ( subst_bvar domain_type bvar_idx bvar_val,
            subst_bvar body (bvar_idx + 1) bvar_val )
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

  (** Fully delta-reduce a term by replacing all defined constants with their definition
      body, so that there are no subterms of "Const x" where "x" is in env.defs in the
      returned term. *)
  let rec delta_reduce (env : environment) (t : term) : term =
    match t with
    | Const name -> (
        match Hashtbl.find_opt env.defs name with
        | Some body -> delta_reduce env body
        | None -> t)
    | App (func, arg) -> App (delta_reduce env func, delta_reduce env arg)
    | Lam (domainType, body) -> Lam (delta_reduce env domainType, delta_reduce env body)
    | Forall (domainType, returnType) ->
        Forall (delta_reduce env domainType, delta_reduce env returnType)
    | _ -> t

  (** Fully beta-reduce a term (performing computation) by recursively replacing all
      instances of (fun x => body) arg with body[arg/x]. *)
  let rec beta_reduce (localCtx : localcontext) (t : term) =
    match t with
    | App (func, arg) -> (
        (* we need to reduce the func before matching if it's a Lam in the case of nested applications *)
        let reduced_func = beta_reduce localCtx func in
        let reduced_arg = beta_reduce localCtx arg in
        match reduced_func with
        | Lam (_, body) ->
            (* beta reduction---substitute bound variable *)
            let substed_body = subst_bvar body 0 reduced_arg in
            beta_reduce localCtx substed_body
        | _ -> App (reduced_func, reduced_arg))
    | Lam (domainType, body) ->
        (* substitute free variable in lambda *)
        let new_fvar_name = gen_new_fvar_name () in
        let domainTypeReduced = beta_reduce localCtx domainType in
        let newLocalCtx =
          let t = Hashtbl.copy localCtx in
          Hashtbl.replace t new_fvar_name domainTypeReduced;
          t
        in
        let substed_body = subst_bvar body 0 (Fvar new_fvar_name) in
        let bodyReduced = beta_reduce newLocalCtx substed_body in
        Lam (domainTypeReduced, rebind_bvar bodyReduced 0 new_fvar_name)
    | Forall (domainType, returnType) ->
        (* substitute free variable in forall *)
        let new_fvar_name = gen_new_fvar_name () in
        let domainTypeReduced = beta_reduce localCtx domainType in
        let newLocalCtx =
          let t = Hashtbl.copy localCtx in
          Hashtbl.replace t new_fvar_name domainTypeReduced;
          t
        in
        let substed_return_type = subst_bvar returnType 0 (Fvar new_fvar_name) in
        let returnTypeReduced = beta_reduce newLocalCtx substed_return_type in
        Forall (domainTypeReduced, rebind_bvar returnTypeReduced 0 new_fvar_name)
    | _ -> t

  (* Reduce a term to normal form *)
  let reduce (env : environment) (localCtx : localcontext) (t : term) : term =
    beta_reduce localCtx (delta_reduce env t)

  (* Determine if a term is a Sort *)
  let isSort (env : environment) (t : term) : bool =
    match reduce env (Hashtbl.create 0) t with Sort _ -> true | _ -> false

  (* Definitional equality: reduce and check exact equality *)
  let isDefEq (env : environment) (localCtx : localcontext) (t1 : term) (t2 : term) : bool
      =
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
        try Hashtbl.find env.types name
        with Not_found ->
          (* Error: Unknown constant *)
          let err_kind = UnknownConstError name in
          raise (TypeError { ctx = localCtx; trm = t; err_kind }))
    | Fvar name -> (
        try Hashtbl.find localCtx name
        with Not_found ->
          (* Error: Unknown free variable *)
          let err_kind = UnknownFreeVarError name in
          raise (TypeError { ctx = localCtx; trm = t; err_kind }))
    | Bvar idx ->
        (* Error: Bound variable out of scope *)
        let err_kind = BoundVarScopeError idx in
        raise (TypeError { ctx = localCtx; trm = t; err_kind })
    | App (func, arg) -> (
        let func_type = reduce env localCtx (inferType env localCtx func) in
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
                AppArgTypeError
                  (func, arg, func_type, expected_arg_type, inferred_arg_type)
              in
              raise (TypeError { ctx = localCtx; trm = t; err_kind })
        | _ ->
            (* Error: Tried to apply non-function to an argument *)
            let err_kind = AppNonFuncError func_type in
            raise (TypeError { ctx = localCtx; trm = t; err_kind }))
    | Lam (domainType, body) ->
        let new_fvar_name = gen_new_fvar_name () in
        let domainTypeType = inferType env localCtx domainType in
        if not (isSort env domainTypeType) then
          (* Invalid domain type for lambda *)
          let err_kind = LamDomainError domainTypeType in
          raise (TypeError { ctx = localCtx; trm = t; err_kind })
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
            raise (TypeError { ctx; trm; err_kind }))
    | Sort level -> Sort (level + 1)
end

open Internals

let create () : environment = { types = Hashtbl.create 16; defs = Hashtbl.create 16 }

(** Ensures name does not exist in env. *)
let ensure_name_not_exists (env : environment) (name : string) : unit =
  if Hashtbl.mem env.types name then
    (* Error: Name already defined *)
    let err_kind = AlreadyDefined name in
    raise (TypeError { ctx = Hashtbl.create 0; trm = Const name; err_kind })

(** Ensures ty is actually a type. *)
let check_is_type (env : environment) (ty : term) : unit =
  (* Error: type must be a sort *)
  let local_ctx = Hashtbl.create 0 in
  let typetype = inferType env local_ctx ty in
  if not (isSort env typetype) then
    let err_kind = DeclarationTypeError ty in
    raise (TypeError { ctx = local_ctx; trm = ty; err_kind })

(** Type-checks and adds an axiom to the provided environment, throwing TypeError on
    failure. *)
let add_axiom (env : environment) (name : string) (axiom_type : term) : unit =
  ensure_name_not_exists env name;
  check_is_type env axiom_type;
  Hashtbl.add env.types name axiom_type

(** Ensures that the inferred type of [proof] is definitionally equal to [theorem_type] *)
let check_theorem (env : environment) (theorem_type : term) (proof : term) =
  check_is_type env theorem_type;
  let local_ctx = Hashtbl.create 0 in
  let proof_type = inferType env local_ctx proof in
  if not (isDefEq env local_ctx proof_type theorem_type) then
    (* Error: Proof does not match theorem type *)
    let err_kind = ProofTypeMismatch (theorem_type, proof_type) in
    raise (TypeError { ctx = local_ctx; trm = proof; err_kind })

(** Type-checks and adds a theorem to the provided environment, throwing TypeError on
    failure. *)
let add_theorem (env : environment) (name : string) (theorem_type : term) (proof : term) :
    unit =
  ensure_name_not_exists env name;
  check_theorem env theorem_type proof;
  Hashtbl.add env.types name theorem_type

(** Type-checks and adds a definition to the provided environment, throwing TypeError on
    failure. Type-checks the definition as a theorem, then adds the definition body. *)
let add_definition (env : environment) (name : string) (definition_type : term)
    (body : term) : unit =
  add_theorem env name definition_type body;
  Hashtbl.add env.defs name body

let get_types (env : environment) = Hashtbl.copy env.types
let get_definitions (env : environment) = Hashtbl.copy env.defs
