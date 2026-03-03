type range = { start: Lexing.position; end_: Lexing.position }
let dummy_pos : Lexing.position = {
  pos_fname = "";
  pos_lnum = 0;
  pos_bol = 0;
  pos_cnum = 0;
}
let dummy_range : range = { start = dummy_pos; end_ = dummy_pos }

type term = {inner: term'; loc: range}
and term' =
  | Name of string (* a name in the code (refers to a const or the nearest bound variable of the same name during parsing) *)
  | Bvar of int (* de Bruijn index *)
  | Fvar of int (* unique index *)
  | Hole of int
  | Fun of string option * term * term  (* argument name, type, body *)
  | Arrow of string option * term * term  (* argument name, type, return type *)
  | App of term * term
  | Sort of int


let counter = ref 0

let gen_hole_id () =
  let id = !counter in
  counter := id + 1;
  id

let gen_fvar_id = gen_hole_id

let rec bind_bvar (tm: term) (bvar_idx: int) (pat: term) : term =
  match tm.inner with
  | Fun (x, ty_arg, body) ->
    let ty_arg_rebound = bind_bvar ty_arg bvar_idx pat in
    let body_rebound = bind_bvar body (bvar_idx + 1) pat in
    {inner=Fun (x, ty_arg_rebound, body_rebound); loc=tm.loc}
  | Arrow (x, ty_arg, ty_ret) ->
    let ty_arg_rebound = bind_bvar ty_arg bvar_idx pat in
    let ty_ret_rebound = bind_bvar ty_ret (bvar_idx + 1) pat in
    {inner=Arrow (x, ty_arg_rebound, ty_ret_rebound); loc=tm.loc}
  | App (t1, t2) ->
    let t1_rebound = bind_bvar t1 bvar_idx pat in
    let t2_rebound = bind_bvar t2 bvar_idx pat in
    {inner=App (t1_rebound, t2_rebound); loc=tm.loc}
  | Name _ | Fvar _ -> if tm.inner = pat.inner then {inner=Bvar bvar_idx; loc=tm.loc} else {inner=tm.inner; loc=tm.loc}
  | _ -> tm


let rec replace_bvar (tm: term) (bvar_idx: int) (replacement: term) : term =
  match tm.inner with
  | Fun (x, ty, body) ->
    let ty_replaced = replace_bvar ty bvar_idx replacement in
    let body_replaced = replace_bvar body (bvar_idx + 1) replacement in
    {inner=Fun (x, ty_replaced, body_replaced); loc=tm.loc}
  | Arrow (x, ty, ret) ->
    let ty_replaced = replace_bvar ty bvar_idx replacement in
    let ret_replaced = replace_bvar ret (bvar_idx + 1) replacement in
    {inner=Arrow (x, ty_replaced, ret_replaced); loc=tm.loc}
  | App (f, arg) ->
    let f_replaced = replace_bvar f bvar_idx replacement in
    let arg_replaced = replace_bvar arg bvar_idx replacement in
    {inner=App (f_replaced, arg_replaced); loc=tm.loc}
  | Bvar idx -> if idx = bvar_idx then {inner=replacement.inner; loc=tm.loc} else tm
  | _ -> tm

let is_sort (t: term) : bool =
  match t.inner with
  | Sort _ -> true
  | _ -> false