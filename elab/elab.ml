open Decl
open Term
open System_e_kernel.Infer
module KTerm = System_e_kernel.Term


let rec conv_to_kterm1 (t: term) : KTerm.term =
  match t with
  | Name x -> KTerm.Fvar x
  | Hole -> failwith "hole in conv_to_kterm input"
  | Fun (x, ty, body) -> 
      let body_conv = conv_to_kterm1 body in
      let rebound_body = rebind_bvar body_conv 0 x in
      KTerm.Lam (conv_to_kterm1 ty, rebound_body)
  | Arrow (x, ty, ret) -> 
      let ret_conv = conv_to_kterm1 ret in
      let rebound_ret = rebind_bvar ret_conv 0 x in
      KTerm.Forall (conv_to_kterm1 ty, rebound_ret)
  | App (f, arg) -> KTerm.App (conv_to_kterm1 f, conv_to_kterm1 arg)
  | Sort n -> KTerm.Sort n

let conv_to_kterm (t: term) : KTerm.term =
  System_e_kernel.Decl.convertFvarToConst (conv_to_kterm1 t)

let unify (t: term) : term =
  t

let elab (t: term) : KTerm.term =
  let t1 = unify t in
  conv_to_kterm t1

let elab_decl (d: declaration) : System_e_kernel.Decl.declaration =
  match d with
  | Theorem (name, ty, proof) -> 
      let ty_k = conv_to_kterm ty in
      let proof_k = conv_to_kterm proof in
      System_e_kernel.Decl.Theorem (name, ty_k, proof_k)
  | Axiom (name, ty) ->
      let ty_k = conv_to_kterm ty in
      System_e_kernel.Decl.Axiom (name, ty_k)
