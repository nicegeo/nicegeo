(** Pretty-printing for elaborator terms.  Only depends on [Term] and [Decl]. *)

open Term
open Decl

(* Lean convention: Sort 0 = Prop, Sort 1 = Type (= Type 0), Sort n = Type (n-1); display level 0-based *)
let sort_to_string = function
  | 0 -> "Prop"
  | 1 -> "Type"
  | n -> "Sort " ^ string_of_int (n - 1)

let is_atomic = function
  | Name _ | Hole | Sort _ -> true
  | Fun _ | Arrow _ | App _ -> false

(** Flatten application spine. *)
let rec flatten_app t =
  match t with
  | App (f, a) ->
      let head, args = flatten_app f in
      (head, args @ [a])
  | other -> (other, [])

let rec term_to_string (t : term) : string =
  match t with
  | Name x -> x
  | Hole -> "_"
  | Sort n -> sort_to_string n
  | Fun (x, ty, body) ->
      let ty_s = term_to_string ty in
      let body_s = term_to_string body in
      "fun (" ^ x ^ " : " ^ ty_s ^ ") => " ^ body_s
  | Arrow (x, ty, ret) ->
      let ty_s = term_to_string ty in
      let ret_s = term_to_string ret in
      if x = "" then ty_s ^ " -> " ^ ret_s
      else "(" ^ x ^ " : " ^ ty_s ^ ") -> " ^ ret_s
  | App _ ->
      let head, args = flatten_app t in
      let head_s = term_to_string head in
      let args_s =
        List.map
          (fun a ->
            let s = term_to_string a in
            if is_atomic a then s else "(" ^ s ^ ")")
          args
      in
      (match args_s with [] -> head_s | _ -> head_s ^ " " ^ String.concat " " args_s)

let decl_to_string = function
  | Axiom (name, ty) -> "Axiom " ^ name ^ " : " ^ term_to_string ty
  | Theorem (name, ty, proof) ->
      "Theorem " ^ name ^ " : " ^ term_to_string ty ^ " := " ^ term_to_string proof
