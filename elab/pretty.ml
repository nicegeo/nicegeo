(** Pretty-printing for elaborator terms.

    Elaborator terms now contain [Bvar] and [Fvar]s and only optional
    binder names. To print readable names we consult the elaborator context
    stored in [Types.ctx] (notably [lctx] and [metas]). *)

open Term
open Decl

(* Sort 0 = Prop, Sort 1 = Type; for n >= 2 display as "Sort n". *)
let sort_to_string = function
  | 0 -> "Prop"
  | 1 -> "Type"
  | n -> "Sort " ^ string_of_int n

let is_atomic x = match fst x with
  | Name _ | Bvar _ | Fvar _ | Hole _ | Sort _ -> true
  | Fun _ | Arrow _ | App _ -> false

(** Flatten application spine. *)
let rec flatten_app t =
  match fst t with
  | App (f, a) ->
      let head, args = flatten_app f in
      (head, args @ [a])
  | _ -> (t, [])

let opt_name_to_string = function
  | Some x -> x
  | None -> "_"

let bvar_to_string (bctx : string list) (idx : int) : string =
  if idx < List.length bctx then List.nth bctx idx else "_" ^ string_of_int idx

let fvar_to_string (e : Types.ctx) (idx : int) : string =
  match Hashtbl.find_opt e.lctx idx with
  | Some (Some name, _) -> name
  | _ -> "f" ^ string_of_int idx

let rec term_to_string_with (e : Types.ctx) (bctx : string list) (t : term) : string =
  match fst t with
  | Name x -> x
  | Bvar idx -> bvar_to_string bctx idx
  | Fvar idx -> fvar_to_string e idx
  | Hole idx -> (
      match Hashtbl.find_opt e.metas idx with
      | Some { sol = Some tm_sol; _ } ->
          "?m" ^ string_of_int idx ^ " := " ^ term_to_string_with e bctx tm_sol
      | _ -> "?m" ^ string_of_int idx
    )
  | Sort n -> sort_to_string n
  | Fun (x, ty, body) ->
      let x_s = opt_name_to_string x in
      let ty_s = term_to_string_with e bctx ty in
      let body_s = term_to_string_with e (x_s :: bctx) body in
      "fun (" ^ x_s ^ " : " ^ ty_s ^ ") => " ^ body_s
  | Arrow (x, ty, ret) ->
      let x_s = opt_name_to_string x in
      let ty_s = term_to_string_with e bctx ty in
      let ret_s = term_to_string_with e (x_s :: bctx) ret in
      if x = None then ty_s ^ " -> " ^ ret_s else "(" ^ x_s ^ " : " ^ ty_s ^ ") -> " ^ ret_s
  | App _ ->
      let head, args = flatten_app t in
      let head_s = term_to_string_with e bctx head in
      let args_s =
        List.map
          (fun a ->
            let s = term_to_string_with e bctx a in
            if is_atomic a then s else "(" ^ s ^ ")")
          args
      in
      (match args_s with [] -> head_s | _ -> head_s ^ " " ^ String.concat " " args_s)

let term_to_string (e : Types.ctx) (t : term) : string = term_to_string_with e [] t

let decl_to_string (e : Types.ctx) = function
  | Axiom (name, _,  ty) -> "Axiom " ^ name ^ " : " ^ term_to_string e ty
  | Theorem (name, _, ty, proof) ->
      "Theorem " ^ name ^ " : " ^ term_to_string e ty ^ " := " ^ term_to_string e proof
