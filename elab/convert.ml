
open Term
module KTerm = System_e_kernel.Term

(* Converts an elaboration-level term to a kernel-level term. tm must not have any holes *)
let rec conv_to_kterm (tm: term) : KTerm.term =
  match tm with
  | Name x -> KTerm.Const x
  | Hole _ -> failwith "hole in conv_to_kterm input"
  | Fun (_, ty, body) -> KTerm.Lam (conv_to_kterm ty, conv_to_kterm body)
  | Arrow (_, ty, ret) -> KTerm.Forall (conv_to_kterm ty, conv_to_kterm ret)
  | App (f, arg) -> KTerm.App (conv_to_kterm f, conv_to_kterm arg)
  | Sort n -> KTerm.Sort n
  | Bvar n -> KTerm.Bvar n
  | Fvar _ -> failwith "fvar in conv_to_kterm input"
