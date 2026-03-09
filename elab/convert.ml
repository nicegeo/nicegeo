open Term
module KTerm = Kernel.Term

let rec term_name_of (tm : term) : string option =
  match tm.inner with
  | Name x -> Some x
  | Fun (Some x, _, _) -> Some x
  | Arrow (Some x, _, _) -> Some x
  | Hole m -> Some ("_" ^ string_of_int m)
  | Fvar i -> Some ("f" ^ string_of_int i)
  | Bvar i -> Some ("#" ^ string_of_int i)
  | App (f, _) -> term_name_of f
  | _ -> None

(* Converts an elaboration-level term to a kernel-level term. tm must not have any holes *)
let rec conv_to_kterm (tm : term) : KTerm.term =
  match tm.inner with
  | Name x -> KTerm.Const x
  | Hole _ ->
      raise
        (Error.ElabError
           {
             context =
               { loc = Some tm.loc; decl_name = None; term_name = term_name_of tm };
             error_type = Error.InternalError "hole in conv_to_kterm input";
           })
  | Fun (_, ty, body) -> KTerm.Lam (conv_to_kterm ty, conv_to_kterm body)
  | Arrow (_, ty, ret) -> KTerm.Forall (conv_to_kterm ty, conv_to_kterm ret)
  | App (f, arg) -> KTerm.App (conv_to_kterm f, conv_to_kterm arg)
  | Sort n -> KTerm.Sort n
  | Bvar n -> KTerm.Bvar n
  | Fvar _ ->
      raise
        (Error.ElabError
           {
             context =
               { loc = Some tm.loc; decl_name = None; term_name = term_name_of tm };
             error_type = Error.InternalError "fvar in conv_to_kterm input";
           })
