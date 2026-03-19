(** Pretty-printing for elaborator terms.

    Elaborator terms now contain [Bvar] and [Fvar]s and only optional binder names. To
    print readable names we consult the elaborator context stored in [Types.ctx] (notably
    [lctx] and [metas]). *)

open Term
open Statement

(* Sort 0 = Prop, Sort 1 = Type; for n >= 2 display as "Sort n". *)
let sort_to_string = function 0 -> "Prop" | 1 -> "Type" | n -> "Sort " ^ string_of_int n

let is_atomic x =
  match x.inner with
  | Name _ | Bvar _ | Hole _ | Sort _ -> true
  | Fun _ | Arrow _ | App _ -> false

(** Flatten application spine. *)
let rec flatten_app t =
  match t.inner with
  | App (f, a) ->
      let head, args = flatten_app f in
      (head, args @ [ a ])
  | _ -> (t, [])

let ctr = ref 0

let gen_fresh_name () =
  let name = "x" ^ string_of_int !ctr in
  incr ctr;
  name

let opt_name_to_string = function Some x -> x | None -> gen_fresh_name ()
let fmt_binder (name : string) (ty : string) : string = "(" ^ name ^ " : " ^ ty ^ ")"
let reduce (_e : Types.ctx) (t : term) : term = t

(* Return a list of formatted arguments to the lambdas,
  the remaining body to format, and the new `bctx` after processing them all.
*)
let rec _flatten_fun (t : term) (bctx : string list) (fmt : string list -> term -> string)
    : string list * term * string list =
  match t.inner with
  | Fun (x, _, ty, body) ->
      let x_s : string = opt_name_to_string x in
      let ty_s : string = fmt bctx ty in
      let binder = fmt_binder x_s ty_s in
      let binders, new_body, new_bctx = _flatten_fun body (x_s :: bctx) fmt in
      (binder :: binders, new_body, new_bctx)
  | _ -> ([], t, bctx)

let pp_loc (r : range) =
  if r.start.pos_lnum = r.end_.pos_lnum then
    Printf.sprintf
      "%s:%d:%d-%d"
      r.start.pos_fname
      r.start.pos_lnum
      (r.start.pos_cnum - r.start.pos_bol + 1)
      (r.end_.pos_cnum - r.end_.pos_bol + 1)
  else
    Printf.sprintf
      "%s:%d:%d to %d:%d"
      r.start.pos_fname
      r.start.pos_lnum
      (r.start.pos_cnum - r.start.pos_bol + 1)
      r.end_.pos_lnum
      (r.end_.pos_cnum - r.end_.pos_bol + 1)

let bvar_to_string (e : Types.ctx) (idx : int) : string =
  match Hashtbl.find_opt e.lctx idx with
  | Some (Some name, _) -> name ^ "[" ^ string_of_int idx ^ "]"
  | Some (None, _) -> "x" ^ string_of_int idx
  | None -> "!" ^ string_of_int idx

let rec term_to_string (e : Types.ctx) (t : term) : string =
  (* let t = reduce e t in *)
  match t.inner with
  | Name x -> x
  | Bvar idx -> bvar_to_string e idx
  | Hole idx -> (
      match Hashtbl.find_opt e.metas idx with
      | Some { sol = Some tm_sol; _ } -> term_to_string e tm_sol
      | _ -> "?m" ^ string_of_int idx)
  | Sort n -> sort_to_string n
  | Fun (x, bid, ty, body) ->
      "fun ("
      ^ (match x with
        | Some name -> name ^ "[" ^ string_of_int bid ^ "]"
        | None -> "x" ^ string_of_int bid)
      ^ " : " ^ term_to_string e ty ^ ") => "
      ^
      (Hashtbl.add e.lctx bid (x, ty);
       let body_str = term_to_string e body in
       Hashtbl.remove e.lctx bid;
       body_str)
  | Arrow (x, bid, ty, ret) -> (
      match x with
      | None ->
          let ty_s = term_to_string e ty in
          let ret_s = term_to_string e ret in
          ty_s ^ " -> " ^ ret_s
      | Some name ->
          let ty_s = term_to_string e ty in
          Hashtbl.add e.lctx bid (Some name, ty);
          let ret_s = term_to_string e ret in
          Hashtbl.remove e.lctx bid;
          "(" ^ name ^ "[" ^ string_of_int bid ^ "]" ^ " : " ^ ty_s ^ ") -> " ^ ret_s)
  | App _ -> (
      let head, args = flatten_app t in
      let head_s = term_to_string e head in
      let args_s =
        List.map
          (fun a ->
            let s = term_to_string e a in
            if is_atomic a then s else "(" ^ s ^ ")")
          args
      in
      match args_s with [] -> head_s | _ -> head_s ^ " " ^ String.concat " " args_s)

let decl_to_string (e : Types.ctx) (d : declaration) =
  match d.kind with
  | Axiom -> "Axiom " ^ d.name ^ " : " ^ term_to_string e d.ty
  | Theorem proof ->
      "Theorem " ^ d.name ^ " : " ^ term_to_string e d.ty ^ " := "
      ^ term_to_string e proof
