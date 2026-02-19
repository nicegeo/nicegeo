open Decl
open Term
open Convert
open System_e_kernel.Infer
module KTerm = System_e_kernel.Term

type t = {
  env : (string, term) Hashtbl.t; (* elaboration-level environment *)
  kenv : KTerm.environment; (* kernel-level environment (should be kept in sync with env) *)
}

let create () : t = {
  env = Hashtbl.create 16;
  kenv = Hashtbl.create 16;
}

let checktype (_e: t) (_tm: term) (_ty: term) : bool =
  failwith "how does this work"

let unify (_e: t) (tm: term) : term =
  tm

let process_decl (e: t) (d: declaration) : unit =
  match d with
  | Theorem (name, ty, proof) ->
      if Hashtbl.mem e.env name then
        failwith ("theorem " ^ name ^ " already defined.\n")
      else
        let ty_k = conv_to_kterm (unify e ty) in
        let proof_k = conv_to_kterm (unify e proof) in
        let inferredType = inferType e.kenv (Hashtbl.create 0) proof_k in
        let isValidProof = isDefEq e.kenv (Hashtbl.create 0) inferredType ty_k in

        if isValidProof then
          (Hashtbl.add e.env name ty;
          Hashtbl.add e.kenv name ty_k)
        else
          failwith ("invalid proof of " ^ name ^ ".\n")
  | Axiom (name, ty) ->
      if Hashtbl.mem e.env name then
        failwith ("axiom " ^ name ^ " already defined.\n")
      else
        let ty_k = conv_to_kterm (unify e ty) in
        if isSort e.kenv ty_k then
           (Hashtbl.add e.env name ty;
            Hashtbl.add e.kenv name ty_k)
        else
          failwith ("axiom " ^ name ^ " has invalid type.\n")


let create_with_env () : t = 
  let e = create () in
  let ic = open_in "elab/env.txt" in
  let lexbuf = Lexing.from_channel ic in
  let decls = Parser.main Lexer.token lexbuf in
  let _ = List.map (process_decl e) decls in
  e

