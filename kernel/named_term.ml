(* "Named terms", terms with named Lam and Forall arguments which are hopefully easier to read. 
These conversion functions will also need to be trusted. *)

type named_term =
  | Name of string
  | Lam of string * named_term * named_term
  | Forall of string * named_term * named_term
  | App of named_term * named_term
  | Sort of int
  | Bvar of int

(** Makes all instances of `Name name` in `nt` bound to the variable at the given level *)
let rec bind_bvar (nt : named_term) (level : int) (name : string) : named_term =
  match nt with
  | Name s when s = name -> Bvar level
  | Lam (n, ty, body) ->
      let bound_ty = bind_bvar ty level name in
      (* Don't recurse into the body if this binding shadows the outside name *)
      let bound_body = if n = name then body else bind_bvar body (level + 1) name in
      Lam (n, bound_ty, bound_body)
  | Forall (n, ty, ret_type) ->
      let bound_ty = bind_bvar ty level name in
      (* Don't recurse into the return type if this binding shadows the outside name *)
      let bound_body =
        if n = name then ret_type else bind_bvar ret_type (level + 1) name
      in
      Forall (n, bound_ty, bound_body)
  | App (f, arg) ->
      let bound_f = bind_bvar f level name in
      let bound_arg = bind_bvar arg level name in
      App (bound_f, bound_arg)
  | _ -> nt

(** Converts a named term to a kernel term, calculating all bound variable indices. *)
let rec named_term_to_term (nt : named_term) : Term.term =
  match nt with
  | Name s ->
      (* If we encounter a name that is not bound, then it is a Const *)
      Term.Const s
  | Lam (name, ty, body) ->
      let ty = named_term_to_term ty in
      (* Replace any `Name name` in `body` with a Bvar *)
      let bound_body = bind_bvar body 0 name in
      Term.Lam (ty, named_term_to_term bound_body)
  | Forall (name, ty, ret_type) ->
      let ty = named_term_to_term ty in
      (* Replace any `Name name` in `ret_type` with a Bvar *)
      let bound_body = bind_bvar ret_type 0 name in
      Term.Forall (ty, named_term_to_term bound_body)
  | App (f, arg) -> Term.App (named_term_to_term f, named_term_to_term arg)
  | Sort n -> Term.Sort n
  | Bvar n -> Term.Bvar n

(** Creates an application from a list of named terms. e.g. app [f; x; y] is App(App(f,
    x), y) *)
let app (terms : named_term list) : named_term =
  match terms with
  | [] -> failwith "Cannot create an application with no terms"
  | f :: args -> List.fold_left (fun acc arg -> App (acc, arg)) f args
