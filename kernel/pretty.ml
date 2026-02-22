(** Pretty-printing for kernel terms. Does not depend on Infer or
    axiom tracking. Hides raw [Bvar] indices and uses readable Sort names. *)

open Term

let sort_to_string = function
  | 0 -> "Prop"
  | 1 -> "Type"
  | n -> "Type" ^ string_of_int n

(** [names] is for bound variables: index 0 = innermost binder (head of list).
    Empty string means use default "_0", "_1", etc. *)
let bvar_name names idx =
  if idx < List.length names then
    let n = List.nth names idx in
    if n = "" then "_" ^ string_of_int idx else n
  else "_" ^ string_of_int idx

(** Default name for the binder we're introducing when no name is provided. *)
let default_binder_name names = "_" ^ string_of_int (List.length names)

let is_atomic = function
  | Const _ | Fvar _ | Bvar _ | Sort _ -> true
  | Lam _ | Forall _ | App _ -> false

(** Flatten application spine: [App (App (f, a), b)] -> (f, [a; b]). *)
let rec flatten_app t =
  match t with
  | App (f, a) ->
      let (head, args) = flatten_app f in
      (head, args @ [a])
  | other -> (other, [])

let rec term_to_string_pretty ?(names = []) (t : term) : string =
  match t with
  | Const name -> name
  | Sort n -> sort_to_string n
  | Fvar name -> name
  | Bvar idx -> bvar_name names idx
  | Lam (dom, body) ->
      let name = default_binder_name names in
      let body_names = name :: names in
      let dom_s = term_to_string_pretty ~names dom in
      let body_s = term_to_string_pretty ~names:body_names body in
      "fun (" ^ name ^ " : " ^ dom_s ^ ") => " ^ body_s
  | Forall (dom, body) ->
      let name = default_binder_name names in
      let body_names = name :: names in
      let dom_s = term_to_string_pretty ~names dom in
      let body_s = term_to_string_pretty ~names:body_names body in
      "(" ^ name ^ " : " ^ dom_s ^ ") -> " ^ body_s
  | App _ ->
      let (head, args) = flatten_app t in
      let head_s = term_to_string_pretty ~names head in
      let args_s =
        List.map
          (fun a ->
            let s = term_to_string_pretty ~names a in
            if is_atomic a then s else "(" ^ s ^ ")")
          args
      in
      (match args_s with [] -> head_s | _ -> head_s ^ " " ^ String.concat " " args_s)
