open Term
open Infer

type declaration =
    | Theorem of string * term * term
    | Axiom of string * term

let rec convertFvarToConst (t : term) : term =
  match t with
  | Const _ | Bvar _ | Sort _ -> t
  | Fvar n -> Const n
  | Lam (dom, body) -> Lam (convertFvarToConst dom, convertFvarToConst body)
  | Forall (dom, body) -> Forall (convertFvarToConst dom, convertFvarToConst body)
  | App (func, arg) -> App (convertFvarToConst func, convertFvarToConst arg)

let convertDeclFvarToConst (decl : declaration) : declaration =
  match decl with
  | Axiom (name, ty) -> Axiom (name, convertFvarToConst ty)
  | Theorem (name, ty, proof) ->
      Theorem (name, convertFvarToConst ty, convertFvarToConst proof)

let addDeclaration (decl : declaration) (env : environment) : unit =
    match convertDeclFvarToConst decl with
    | Axiom (name, ty) ->
      let tyType = inferType env (Hashtbl.create 16) ty in
      if isSort env tyType then
        Hashtbl.add env name ty
      else
        failwith ("type of axiom " ^ name ^ "is invalid\n
        The type of its type is " ^ term_to_string tyType)
    | Theorem (name, ty, proof) ->
      let inferredType = inferType env (Hashtbl.create 16) proof in
      let isValidProof = isDefEq env (Hashtbl.create 16) inferredType ty in

      if isValidProof then
        Hashtbl.add env name ty
      else
        failwith ("invalid proof of " ^ name ^ "\n. Expected type:\n"
          ^ term_to_string ty ^ "\n Type of proof is:\n" ^ term_to_string inferredType)