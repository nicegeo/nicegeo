open Elab.Term
open Elab.Proofstate
open Elab.Typecheck
open Elab.Tactic
open Measure

let measure_norm (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> Failure "no goals"
  | Some g ->
      let goal_filled = replace_metas st.elab_ctx g.goal_type in
      let motive_bid = Elab.Term.gen_binder_id () in
      (*
    if infertype t is Measure,
        t' = normalize t, also producing p : t' = t
        apply Eq.elim
        but with what motive
        the current goal type of st, but with the position where we are currently abstracted
        maybe we need to pass around the motive
        that sounds slow and weird
        maybe its fine
        return the new state and the goal type subterm produced by the normalization 
    *)
      let rec go (tm : term) (motive : term) (st : proof_state) : proof_state * term =
        let ty = infertype st.elab_ctx g.lctx tm in
        match ty.inner with
        | Name "Measure" -> (
            match to_measure tm with
            | Some m ->
                let goal_id = (List.hd st.open_goals).goal_id in
                let m_normal = normalize_measure m in
                let tm_normal = measure_to_term m_normal in
                let tm_normal_eq_tm = Simpterm.from_simpterm m_normal.proof in
                let new_goal_ty = subst motive (Bvar motive_bid) tm_normal.inner in
                let goal_hole, st = fresh_goal st g.lctx new_goal_ty in
                let motive_fun = mk_fun None motive_bid (mk_name "Measure") motive in
                let proof =
                  mk_app
                    (mk_app
                       (mk_app
                          (mk_app
                             (mk_app
                                (mk_app (mk_name "Eq.elim") (mk_name "Measure"))
                                tm_normal)
                             motive_fun)
                          goal_hole)
                       tm)
                    tm_normal_eq_tm
                in
                let st = assign_meta goal_id proof st in
                let st = close_goal goal_id st in
                (st, tm_normal)
            | None -> (st, tm))
        | _ -> (
            (* recursively traverse the term *)
            match tm.inner with
            | App (f, arg) ->
                let left_motive =
                  subst motive (Bvar motive_bid) (App (mk_bvar motive_bid, arg))
                in
                let st, f' = go f left_motive st in
                let right_motive =
                  subst motive (Bvar motive_bid) (App (f', mk_bvar motive_bid))
                in
                let st, arg' = go arg right_motive st in
                let tm' = mk_app f' arg' in
                (st, tm')
            | _ -> (st, tm))
      in

      let st, _ = go goal_filled (mk_bvar motive_bid) st in
      Success st
