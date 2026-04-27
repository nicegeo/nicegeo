open Term

let rec subst (e : Types.ctx) (tm : term) (pat : termkind) (replacement : termkind) =
  match tm.inner with
  | Name _ | Bvar _ ->
      if tm.inner = pat then { inner = replacement; loc = tm.loc } else tm
  | Fun (x, bid, ty, body) ->
      let ty_subst = subst e ty pat replacement in
      let body_subst = subst e body pat replacement in
      { inner = Fun (x, bid, ty_subst, body_subst); loc = tm.loc }
  | Arrow (x, bid, ty_arg, ty_ret) ->
      let ty_arg_subst = subst e ty_arg pat replacement in
      let ty_ret_subst = subst e ty_ret pat replacement in
      { inner = Arrow (x, bid, ty_arg_subst, ty_ret_subst); loc = tm.loc }
  | App (f, arg) ->
      let f_subst = subst e f pat replacement in
      let arg_subst = subst e arg pat replacement in
      { inner = App (f_subst, arg_subst); loc = tm.loc }
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; _ } -> subst e tm_sol pat replacement
      | _ -> tm)
  | _ -> tm

let rec reduce (e : Types.ctx) (tm : term) : term =
  match tm.inner with
  | App (f, arg) -> (
      let fn = reduce e f in
      let arg = reduce e arg in
      match fn.inner with
      | Fun (_, bid, _, body) -> reduce e (subst e body (Bvar bid) arg.inner)
      | _ -> { inner = App (fn, arg); loc = tm.loc })
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; _ } -> reduce e tm_sol
      | _ -> tm)
  | Fun (arg, bid, ty, body) ->
      let ty = reduce e ty in
      let body = reduce e body in
      { inner = Fun (arg, bid, ty, body); loc = tm.loc }
  | Arrow (arg, bid, ty_arg, ty_ret) ->
      let ty_arg = reduce e ty_arg in
      let ty_ret = reduce e ty_ret in
      { inner = Arrow (arg, bid, ty_arg, ty_ret); loc = tm.loc }
  | _ -> tm

let rec delta_reduce (e : Types.ctx) (tm : term) : term =
  match tm.inner with
  | App (f, arg) ->
      let fn = delta_reduce e f in
      let arg = delta_reduce e arg in
      { inner = App (fn, arg); loc = tm.loc }
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; _ } -> delta_reduce e tm_sol
      | _ -> tm)
  | Name n -> (
      match Hashtbl.find_opt e.env n with
      | Some { data = Def (_, body, false); _ } -> delta_reduce e body
      | _ -> tm)
  | Fun (arg, bid, ty, body) ->
      let ty = delta_reduce e ty in
      let body = delta_reduce e body in
      { inner = Fun (arg, bid, ty, body); loc = tm.loc }
  | Arrow (arg, bid, ty_arg, ty_ret) ->
      let ty_arg = delta_reduce e ty_arg in
      let ty_ret = delta_reduce e ty_ret in
      { inner = Arrow (arg, bid, ty_arg, ty_ret); loc = tm.loc }
  | _ -> tm
