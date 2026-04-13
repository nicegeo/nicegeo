open Term
open Exceptions
open Infer.Internals

let create () : environment = { types = Hashtbl.create 16; defs = Hashtbl.create 16 }

(** Verifies that a declaration name is not already defined and that the type is of
    a valid sort. *)
let validate_decl (env : environment) (name : string) (ty : term) : unit =
  let localCtx = Hashtbl.create 0 in
  match Hashtbl.find_opt env.types name with
  | Some _ ->
      (* Error: Name already defined *)
      let err_kind = AlreadyDefined name in
      raise (TypeError { env; ctx = localCtx; trm = ty; err_kind })
  | None ->
      let typetype = inferType env localCtx ty in
      if not (isSort env typetype) then
        (* Error: type must be a sort *)
        let err_kind = DeclarationTypeError ty in
        raise (TypeError { env; ctx = localCtx; trm = ty; err_kind })

(** Type-checks and adds an axiom to the provided environment, throwing TypeError on
    failure. *)
let add_axiom (env : environment) (name : string) (axiomType : term) : unit =
  validate_decl env name axiomType;
  Hashtbl.add env.types name axiomType

(** Type-checks and adds a theorem to the provided environment, throwing TypeError on
    failure. Ensures that the inferred type of [proof] is definitionally equal to
    [theorem_type]. *)
let add_theorem (env : environment) (name : string) (theorem_type : term) (proof : term) :
    unit =
  let local_ctx = Hashtbl.create 0 in
  validate_decl env name theorem_type;
  let proof_type = inferType env local_ctx proof in
  if not (isDefEq env local_ctx proof_type theorem_type) then
    (* Error: Proof does not match theorem type *)
    let err_kind = ProofTypeMismatch (theorem_type, proof_type) in
    raise (TypeError { env; ctx = local_ctx; trm = proof; err_kind })
  else Hashtbl.add env.types name theorem_type

(** Type-checks and adds a definition to the provided environment, throwing TypeError on
    failure. Type-checks the definition as a theorem, then adds the definition body. *)
let add_definition (env : environment) (name : string) (definition_type : term)
    (body : term) : unit =
  add_theorem env name definition_type body;
  Hashtbl.add env.defs name body
