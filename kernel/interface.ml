open Term
open Exceptions
open Infer.Internals

(** Type-checks and adds a theorem to the provided environment, throwing TypeError on
    failure. First ensures [theorem_type]'s type is a sort, and then that the inferred
    type of [proof] is definitionally equal to [theorem_type]. *)
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
        let err_kind = DeclarationTypeError theorem_type in
        raise (TypeError { env; ctx = local_ctx; trm = theorem_type; err_kind })
      else
        let proof_type = inferType env local_ctx proof in
        if not (isDefEq env local_ctx proof_type theorem_type) then
          (* Error: Proof does not match theorem type *)
          let err_kind = ProofTypeMismatch (theorem_type, proof_type) in
          raise (TypeError { env; ctx = local_ctx; trm = proof; err_kind })
        else Hashtbl.add env name theorem_type

(** Type-checks and adds an axiom to the provided environment, throwing TypeError on
    failure. Ensures [axiomType]'s type is a sort. *)
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
        let err_kind = DeclarationTypeError axiomType in
        raise (TypeError { env; ctx = localCtx; trm = axiomType; err_kind })
      else Hashtbl.add env name axiomType
