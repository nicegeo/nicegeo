open Term

(* Sort 0 = Prop, Sort 1 = Type; for n >= 2 display as "Sort n". *)
let sort_to_string = function 0 -> "Prop" | 1 -> "Type" | n -> "Sort " ^ string_of_int n

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

(* Precedence levels for terms for parentheses, corresponding to term rules in the parser. 
  Lower means tighter binding. *)
let prec_term = 20
let prec_app = 10
let prec_atomic = 0

let rec get_prec (e : Types.ctx) (t : term) : int =
  match t.inner with
  | Name _ | Bvar _ | Sort 0 | Sort 1 -> prec_atomic
  | Sort _ | App _ -> prec_app
  | Fun _ | Arrow _ -> prec_term
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; _ } -> get_prec e tm_sol
      | _ -> prec_atomic)

let term_to_string (e : Types.ctx) (t : term) : string =
  let rec term_to_string_helper (e : Types.ctx) (t : term) (level : int) : string =
    if level < get_prec e t then "(" ^ term_to_string_helper e t prec_term ^ ")"
    else
      match t.inner with
      | Name x -> x
      | Bvar idx -> bvar_to_string e idx
      | Hole idx -> (
          match Hashtbl.find_opt e.metas idx with
          | Some { sol = Some tm_sol; _ } -> term_to_string_helper e tm_sol level
          | _ -> "?m" ^ string_of_int idx)
      | Sort n -> sort_to_string n
      | Fun _ ->
          let saved_lctx = Hashtbl.copy e.lctx in
          let xs, args, body = flatten_fun e t in
          let res =
            "fun "
            ^ String.concat
                " "
                (List.map2
                   (fun x ty ->
                     "(" ^ x ^ " : " ^ term_to_string_helper e ty prec_term ^ ")")
                   xs
                   args)
            ^ " => "
            ^ term_to_string_helper e body prec_term
          in
          Hashtbl.clear e.lctx;
          Hashtbl.iter (Hashtbl.add e.lctx) saved_lctx;
          res
      | Arrow (x, bid, ty, ret) -> (
          match x with
          | None ->
              let ty_s = term_to_string_helper e ty prec_app in
              let ret_s = term_to_string_helper e ret prec_term in
              ty_s ^ " -> " ^ ret_s
          | Some name ->
              let ty_s = term_to_string_helper e ty prec_term in
              Hashtbl.add e.lctx bid (Some name, ty);
              let ret_s = term_to_string_helper e ret prec_term in
              Hashtbl.remove e.lctx bid;
              "(" ^ name (* "[" ^ string_of_int bid ^ "]" ^ *) ^ " : "
              ^ ty_s ^ ") -> " ^ ret_s)
      | App (f, arg) ->
          term_to_string_helper e f prec_app
          ^ " "
          ^ term_to_string_helper e arg prec_atomic
  in
  term_to_string_helper e t prec_term
