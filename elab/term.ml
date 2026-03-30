type range = {
  start : Lexing.position;
  end_ : Lexing.position;
}

let dummy_pos : Lexing.position =
  { pos_fname = ""; pos_lnum = 0; pos_bol = 0; pos_cnum = 0 }

let dummy_range : range = { start = dummy_pos; end_ = dummy_pos }

type term = {
  inner : termkind;
  loc : range;
}

and termkind =
  | Name of string
  | Bvar of int
  | Hole of int
  | Fun of string option * int * term * term
  | Arrow of string option * int * term * term
  | App of term * term
  | Sort of int

let counter = ref 0

let gen_hole_id () =
  let id = !counter in
  counter := id + 1;
  id

let gen_binder_id = gen_hole_id

let rec subst (tm : term) (pat : termkind) (replacement : termkind) =
  match tm.inner with
  | Name _ | Bvar _ ->
      if tm.inner = pat then { inner = replacement; loc = tm.loc } else tm
  | Fun (x, bid, ty, body) ->
      let ty_subst = subst ty pat replacement in
      let body_subst = subst body pat replacement in
      { inner = Fun (x, bid, ty_subst, body_subst); loc = tm.loc }
  | Arrow (x, bid, ty_arg, ty_ret) ->
      let ty_arg_subst = subst ty_arg pat replacement in
      let ty_ret_subst = subst ty_ret pat replacement in
      { inner = Arrow (x, bid, ty_arg_subst, ty_ret_subst); loc = tm.loc }
  | App (f, arg) ->
      let f_subst = subst f pat replacement in
      let arg_subst = subst arg pat replacement in
      { inner = App (f_subst, arg_subst); loc = tm.loc }
  | _ -> tm
