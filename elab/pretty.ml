open Term
open Types

(* Sort 0 = Prop, Sort 1 = Type; for n >= 2 display as "Sort n". *)
let sort_to_string = function 0 -> "Prop" | 1 -> "Type" | n -> "Sort " ^ string_of_int n

(* Return a list of argument names, bids, and types, and the remaining body of 
  the lambda to format, after processing them all. *)
let rec flatten_fun (t : term) : (string * int * term) list * term =
  match t.inner with
  | Fun (x, bid, ty, body) ->
      let x_s : string =
        match x with Some name -> name | None -> "x" ^ string_of_int bid
      in
      let args, body = flatten_fun body in
      ((x_s, bid, ty) :: args, body)
  | _ -> ([], t)

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

let bvar_to_string (lctx : local_ctx) (idx : int) : string =
  match List.find_opt (fun v -> v.bid = idx) lctx with
  | Some { name = Some name; _ } -> name (* ^ "[" ^ string_of_int idx ^ "]" *)
  | _ -> "!" ^ string_of_int idx

(* Precedence levels for terms for parentheses, corresponding to term rules in the parser. 
  Lower means tighter binding. *)
let prec_term = 20
let prec_app = 10
let prec_atomic = 0

let rec get_prec (e : ctx) (t : term) : int =
  match t.inner with
  | Name _ | Bvar _ | Sort 0 | Sort 1 -> prec_atomic
  | Sort _ | App _ -> prec_app
  | Fun _ | Arrow _ -> prec_term
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; _ } -> get_prec e tm_sol
      | _ -> prec_atomic)

let term_to_string (e : ctx) ?(lctx : local_ctx = []) (t : term) : string =
  let rec term_to_string_helper (e : ctx) (lctx : local_ctx) (t : term) (level : int) :
      string =
    if level < get_prec e t then "(" ^ term_to_string_helper e lctx t prec_term ^ ")"
    else
      match t.inner with
      | Name x -> x
      | Bvar idx -> bvar_to_string lctx idx
      | Hole idx -> (
          match Hashtbl.find_opt e.metas idx with
          | Some { sol = Some tm_sol; _ } -> term_to_string_helper e lctx tm_sol level
          | _ -> "?m" ^ string_of_int idx)
      | Sort n -> sort_to_string n
      | Fun _ ->
          let args, body = flatten_fun t in
          let lctx, param_groups =
            List.fold_left
              (fun (lctx, acc) (arg_name, arg_bid, arg_ty) ->
                let param_s =
                  "(" ^ arg_name ^ " : "
                  ^ term_to_string_helper e lctx arg_ty prec_term
                  ^ ")"
                in
                ( { name = Some arg_name; bid = arg_bid; ty = arg_ty } :: lctx,
                  acc @ [ param_s ] ))
              (lctx, [])
              args
          in

          "fun "
          ^ String.concat " " param_groups
          ^ " => "
          ^ term_to_string_helper e lctx body prec_term
      | Arrow (x, bid, ty, ret) -> (
          match x with
          | None ->
              let ty_s = term_to_string_helper e lctx ty prec_app in
              let ret_s = term_to_string_helper e lctx ret prec_term in
              ty_s ^ " -> " ^ ret_s
          | Some name ->
              let ty_s = term_to_string_helper e lctx ty prec_term in
              let new_lctx = { bid; name = Some name; ty } :: lctx in
              let ret_s = term_to_string_helper e new_lctx ret prec_term in
              "(" ^ name (* "[" ^ string_of_int bid ^ "]" ^ *) ^ " : "
              ^ ty_s ^ ") -> " ^ ret_s)
      | App (f, arg) ->
          term_to_string_helper e lctx f prec_app
          ^ " "
          ^ term_to_string_helper e lctx arg prec_atomic
  in
  term_to_string_helper e lctx t prec_term

let tactic_to_string (e : ctx) (lctx : local_ctx) (t : Statement.tactic) : string =
  t.name ^ " "
  ^ String.concat
      " "
      (List.map
         (fun arg ->
           let arg_str = term_to_string e ~lctx arg in
           if get_prec e arg <> prec_atomic then "(" ^ arg_str ^ ")" else arg_str)
         t.args)

let decl_to_string (e : ctx) (d : Statement.declaration) =
  match d.kind with
  | Axiom -> "Axiom " ^ d.name ^ " : " ^ term_to_string e d.ty
  | Theorem (DefEq term) ->
      "Theorem " ^ d.name ^ " : " ^ term_to_string e d.ty ^ " := " ^ term_to_string e term
  | Theorem (Proof proof) ->
      "Theorem " ^ d.name ^ " : " ^ term_to_string e d.ty ^ "\nProof.\n"
      ^ String.concat "\n" (List.map (tactic_to_string e []) proof)
      ^ "\nQed."
  | Def body ->
      "Def " ^ d.name ^ " : " ^ term_to_string e d.ty ^ " := " ^ term_to_string e body
