open Term

let rec reduce (e : Types.ctx) (tm : term) : term =
  match tm.inner with
  | App (f, arg) -> (
      let fn = reduce e f in
      let arg = reduce e arg in
      match fn.inner with
      | Fun (_, _, body) -> reduce e (replace_bvar body 0 arg)
      | _ -> { inner = App (fn, arg); loc = tm.loc })
  (* do we need to recurse into holes? possibly *)
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; _ } -> reduce e tm_sol
      | _ -> tm)
  | Fun (arg, ty, body) ->
      let x = gen_fvar_id () in
      let ty' = reduce e ty in
      let body' = reduce e (replace_bvar body 0 { inner = Fvar x; loc = tm.loc }) in
      let body'' = bind_bvar body' 0 { inner = Fvar x; loc = tm.loc } in
      { inner = Fun (arg, ty', body''); loc = tm.loc }
  | Arrow (arg, ty, ret) ->
      let x = gen_fvar_id () in
      let ty' = reduce e ty in
      let ret' = reduce e (replace_bvar ret 0 { inner = Fvar x; loc = tm.loc }) in
      let ret'' = bind_bvar ret' 0 { inner = Fvar x; loc = tm.loc } in
      { inner = Arrow (arg, ty', ret''); loc = tm.loc }
  | _ -> tm
