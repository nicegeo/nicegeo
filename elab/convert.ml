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
let conv_to_kterm (tm : term) : KTerm.term =
  (* [stack] is a list of binder IDs in scope; the de Bruijn index of a [Bvar bid] is the 
     index into [stack] that [bid] appears. *)
  let rec conv_to_kterm_helper (tm : term) (stack : int list) : KTerm.term =
    match tm.inner with
    | Name x -> KTerm.Const x
    | Hole _ -> failwith "hole in conv_to_kterm input"
    | Fun (_, bid, ty, body) ->
        KTerm.Lam (conv_to_kterm_helper ty stack, conv_to_kterm_helper body (bid :: stack))
    | Arrow (_, bid, ty, ret) ->
        KTerm.Forall
          (conv_to_kterm_helper ty stack, conv_to_kterm_helper ret (bid :: stack))
    | App (f, arg) ->
        KTerm.App (conv_to_kterm_helper f stack, conv_to_kterm_helper arg stack)
    | Sort n -> KTerm.Sort n
    | Bvar n -> KTerm.Bvar (Option.get (List.find_index (( = ) n) stack))
  in
  conv_to_kterm_helper tm []
