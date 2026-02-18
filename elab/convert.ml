
open Term
open System_e_kernel.Infer
module KTerm = System_e_kernel.Term

let rec conv_to_kterm1 (tm: term) : KTerm.term =
  match tm with
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

let rec convertFvarToConst (tm: KTerm.term) : KTerm.term =
  match tm with
  | KTerm.Fvar x -> KTerm.Const x
  | KTerm.Lam (ty, body) -> KTerm.Lam (convertFvarToConst ty, convertFvarToConst body)
  | KTerm.Forall (ty, ret) -> KTerm.Forall (convertFvarToConst ty, convertFvarToConst ret)
  | KTerm.App (f, arg) -> KTerm.App (convertFvarToConst f, convertFvarToConst arg)
  | t -> t

(* Converts an elaboration-level term to a kernel-level term. tm must not have any holes *)
let conv_to_kterm (tm: term) : KTerm.term =
  convertFvarToConst (conv_to_kterm1 tm)
