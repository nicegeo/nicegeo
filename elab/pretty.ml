open Term
open Statement

(* Sort 0 = Prop, Sort 1 = Type; for n >= 2 display as "Sort n". *)
let sort_to_string = function 0 -> "Prop" | 1 -> "Type" | n -> "Sort " ^ string_of_int n

let is_atomic x =
  match x.inner with
  | Name _ | Bvar _ | Sort _ -> true
  | Hole _ | Fun _ | Arrow _ | App _ -> false

(** Flatten application spine. *)
let rec flatten_app t =
  match t.inner with
  | App (f, a) ->
      let head, args = flatten_app f in
      (head, args @ [ a ])
  | _ -> (t, [])

(* Return a list of argument names, list of argument types, and the remaining body of 
the lambda to format, after processing them all.
*)
let rec flatten_fun (e : Types.ctx) (t : term) : string list * term list * term =
  match t.inner with
  | Fun (x, bid, ty, body) ->
      let x_s : string =
        match x with Some name -> name | None -> "x" ^ string_of_int bid
      in
      Hashtbl.add e.lctx bid (x, ty);
      let xs, args, body = flatten_fun e body in
      (x_s :: xs, ty :: args, body)
  | _ -> ([], [], t)

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
  | Some (Some name, _) -> name (* ^ "[" ^ string_of_int idx ^ "]" *)
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
  | Fun _ ->
      let saved_lctx = Hashtbl.copy e.lctx in
      let xs, args, body = flatten_fun e t in
      let res =
        "fun "
        ^ String.concat
            " "
            (List.map2 (fun x ty -> "(" ^ x ^ " : " ^ term_to_string e ty ^ ")") xs args)
        ^ " => " ^ term_to_string e body
      in
      Hashtbl.clear e.lctx;
      Hashtbl.iter (Hashtbl.add e.lctx) saved_lctx;
      res
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
          "(" ^ name (* "[" ^ string_of_int bid ^ "]" ^ *) ^ " : "
          ^ ty_s ^ ") -> " ^ ret_s)
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
