open Term
open Types
open Proofstate

type tactic_result =
  | Success of proof_state
  | Failure of string

let succeed st = Success st
let fail msg = Failure msg

(* Used by future tactics that need to catch elaboration errors and return a Failure. *)
let _catch_elab (ectx : ctx) (f : unit -> tactic_result) : tactic_result =
  try f () with Error.ElabError info -> fail (Error.pp_exn ectx info)

let beta_nf (e : ctx) (tm : term) : term = Reduce.reduce e tm

type tactic = proof_state -> tactic_result

(** [seq t1 t2] applies t1 to the state. If it succeeds, it applies t2 to the new state.
*)
let seq (t1 : tactic) (t2 : tactic) (st : proof_state) : tactic_result =
  match t1 st with Failure msg -> Failure msg | Success st_new -> t2 st_new

(** [try_tac t] attempts to apply t. If t fails, it simply does nothing and succeeds with
    the original state. *)
let try_tac (t : tactic) (st : proof_state) : tactic_result =
  match t st with Success st_new -> Success st_new | Failure _ -> succeed st

(** [repeat t] applies t over and over until it fails, then returns the last successful
    state. *)
let rec repeat (t : tactic) (st : proof_state) : tactic_result =
  match t st with
  | Failure _ -> succeed st (* Stop repeating and return current state *)
  | Success st_new -> repeat t st_new

(* sequencing operator *)
let ( >> ) = seq

let rec def_eq (e : ctx) (t1 : term) (t2 : term) : bool =
  let t1 = beta_nf e t1 in
  let t2 = beta_nf e t2 in
  match (t1.inner, t2.inner) with
  | Sort i, Sort j -> i = j
  | Bvar i, Bvar j -> i = j
  | Name s, Name t -> s = t
  | Hole i, Hole j -> i = j
  | App (f1, x1), App (f2, x2) -> def_eq e f1 f2 && def_eq e x1 x2
  | Fun (_, bid1, ty1, b1), Fun (_, bid2, ty2, b2) ->
      def_eq e ty1 ty2 && def_eq e b1 (Reduce.subst e b2 (Bvar bid2) (Bvar bid1))
  | Arrow (_, bid1, ty1, r1), Arrow (_, bid2, ty2, r2) ->
      def_eq e ty1 ty2 && def_eq e r1 (Reduce.subst e r2 (Bvar bid2) (Bvar bid1))
  | _ -> false

(* Used by future tactics that need to pass the in-scope bids when creating subgoals. *)
let _goal_stack (g : goal) : int list = List.map (fun h -> h.hyp_bid) g.ctx

(** [Eq A lhs rhs] when [lhs] and [rhs] are definitionally equal, proof term is
    [@refl A lhs].*)
let reflexivity (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g -> (
      let ty = beta_nf st.elab_ctx g.goal_type in
      match ty.inner with
      | App
          ( { inner = App ({ inner = App ({ inner = Name "Eq"; _ }, _a); _ }, lhs); _ },
            rhs ) ->
          if def_eq st.elab_ctx lhs rhs then
            let proof = mk_app (mk_app (mk_name "refl") _a) lhs in
            let st = assign_meta g.goal_id proof st in
            let st = close_goal g.goal_id st in
            succeed st
          else
            fail
              (Printf.sprintf
                 "reflexivity: lhs '%s' and rhs '%s' are not definitionally equal."
                 (pp_term st.elab_ctx lhs)
                 (pp_term st.elab_ctx rhs)) (* need to map to existing error categories*)
      | _ ->
          fail
            (Printf.sprintf
               "reflexivity: goal '%s' is not of the form 'Eq A t t'."
               (pp_term st.elab_ctx ty)))
(* need to map to existing error categories*)

(** [infertype] looks up [Bvar] nodes in [lctx]. Hypotheses live in the goal's local
    context but are not in [lctx] yet — populate it for the duration of [f], then remove
    them so we leave [lctx] exactly as we found it. *)
let with_hyps (st : proof_state) (g : goal) (f : unit -> tactic_result) : tactic_result =
  let cleanup () = List.iter (fun h -> Hashtbl.remove st.elab_ctx.lctx h.hyp_bid) g.ctx in
  List.iter
    (fun h -> Hashtbl.add st.elab_ctx.lctx h.hyp_bid (Some h.hyp_name, h.hyp_type))
    g.ctx;
  try
    let result = f () in
    cleanup ();
    result
  with exn ->
    cleanup ();
    raise exn

let exact (tm : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g ->
      with_hyps st g (fun () ->
          (* Catch ill-typed or unknown-name errors from infertype as Failure
           rather than letting them escape as exceptions. *)
          _catch_elab st.elab_ctx (fun () ->
              (* Ask the elaborator what type [tm] actually has. *)
              let inferred_ty = Typecheck.infertype st.elab_ctx tm in
              (* Accept if the inferred type is definitionally equal to the goal type
             (beta-reduces both sides before comparing). *)
              if def_eq st.elab_ctx inferred_ty g.goal_type then
                let st = assign_meta g.goal_id tm st in
                let st = close_goal g.goal_id st in
                succeed st
              else
                fail
                  (Printf.sprintf
                     "exact: term has type '%s' but goal is '%s'."
                     (pp_term st.elab_ctx inferred_ty)
                     (pp_term st.elab_ctx g.goal_type))))

(** Resolve [name] to a proof term and its type: hypotheses shadow global names. *)
let resolve (name : string) (g : goal) (st : proof_state) : (term * term) option =
  match List.find_opt (fun h -> h.hyp_name = name) g.ctx with
  | Some h -> Some (mk_bvar h.hyp_bid, h.hyp_type)
  | None -> (
      match Hashtbl.find_opt st.elab_ctx.env name with
      | Some entry -> Some (mk_name name, entry.ty)
      | None -> None)

(** [apply name st] looks up [name] as a hypothesis or global lemma, then:
    - if its type is [A -> B] and [B] matches the goal, closes the goal and opens a new
      subgoal for [A];
    - if its type directly matches the goal (no arrow), closes it like [exact]. *)
let apply (name : string) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g -> (
      match resolve name g st with
      | None -> fail (Printf.sprintf "apply: unknown name '%s'." name)
      | Some (tm, f_ty) -> (
          let f_ty = beta_nf st.elab_ctx f_ty in
          match f_ty.inner with
          | Arrow (_, bid, premise_ty, conclusion_ty) ->
              (* Check the instantiated conclusion before opening the subgoal,
                so a failed [apply] does not leak a fresh meta. *)
              let hole_id = gen_hole_id () in
              let hole = mk_hole hole_id in
              let conclusion =
                Reduce.subst st.elab_ctx conclusion_ty (Bvar bid) hole.inner
              in
              if def_eq st.elab_ctx conclusion g.goal_type then (
                let context = List.map (fun h -> h.hyp_bid) g.ctx in
                Hashtbl.replace
                  st.elab_ctx.metas
                  hole_id
                  { ty = Some premise_ty; context; sol = None };
                let subgoal =
                  { ctx = g.ctx; goal_type = premise_ty; goal_id = hole_id }
                in
                let st = { st with open_goals = st.open_goals @ [ subgoal ] } in
                let st = assign_meta g.goal_id (mk_app tm hole) st in
                let st = close_goal g.goal_id st in
                succeed st)
              else
                fail
                  (Printf.sprintf
                     "apply: conclusion '%s' does not match goal '%s'."
                     (pp_term st.elab_ctx conclusion)
                     (pp_term st.elab_ctx g.goal_type))
          | _ ->
              (* No arrow — fall back to exact-style check. *)
              if def_eq st.elab_ctx f_ty g.goal_type then
                let st = assign_meta g.goal_id tm st in
                let st = close_goal g.goal_id st in
                succeed st
              else
                fail
                  (Printf.sprintf
                     "apply: '%s' has type '%s' but goal is '%s'."
                     name
                     (pp_term st.elab_ctx f_ty)
                     (pp_term st.elab_ctx g.goal_type))))

let ensure_sorry_ax (st : proof_state) : unit =
  if not (Hashtbl.mem st.elab_ctx.env "sorry_ax") then (
    let bid = Term.gen_binder_id () in
    let elab_ty = mk_arrow (Some "A") bid (mk_sort 0) (mk_bvar bid) in
    let k_ty = Convert.conv_to_kterm elab_ty in
    Hashtbl.add
      st.elab_ctx.env
      "sorry_ax"
      { name = "sorry_ax"; ty = elab_ty; data = Axiom };
    Hashtbl.add st.elab_ctx.kenv "sorry_ax" k_ty)

let sorry (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g ->
      Printf.eprintf "Warning: proof used sorry - this proof is not valid. \n";
      ensure_sorry_ax st;
      let proof = mk_app (mk_name "sorry_ax") g.goal_type in
      let st = assign_meta g.goal_id proof st in
      let st = close_goal g.goal_id st in
      succeed st

let intro (name : string) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> Failure "intro: no goals remaining"
  | Some g -> (
      match g.goal_type.inner with
      | Arrow (_, bid, premise_ty, conclusion_ty) ->
          let hole_id = fresh_id () in
          let hole = mk_hole hole_id in
          let proof_term = mk_fun (Some name) bid premise_ty hole in
          let st_assigned = assign_meta g.goal_id proof_term st in
          let new_hyp =
            { hyp_name = name; hyp_bid = bid; hyp_def = None; hyp_type = premise_ty }
          in
          let new_ctx_bids = bid :: List.map (fun h -> h.hyp_bid) g.ctx in
          Hashtbl.replace
            st.elab_ctx.metas
            hole_id
            { ty = Some conclusion_ty; context = new_ctx_bids; sol = None };
          let new_goal =
            { ctx = new_hyp :: g.ctx; goal_type = conclusion_ty; goal_id = hole_id }
          in
          let remaining_goals = List.tl st_assigned.open_goals in
          Success { st_assigned with open_goals = new_goal :: remaining_goals }
      | _ -> Failure "intro: goal is not an implication or forall")

let rec intros (names : string list) : tactic =
  match names with [] -> succeed | name :: rest -> intro name >> intros rest

let have (name : string) (ty : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> Failure "have: no goals remaining"
  | Some g ->
      let bid = Term.gen_binder_id () in
      let cont_ty = mk_arrow (Some name) bid ty g.goal_type in
      let proof_id = fresh_id () in
      let cont_id = fresh_id () in
      let ctx_bids = List.map (fun h -> h.hyp_bid) g.ctx in
      Hashtbl.replace
        st.elab_ctx.metas
        proof_id
        { ty = Some ty; context = ctx_bids; sol = None };
      Hashtbl.replace
        st.elab_ctx.metas
        cont_id
        { ty = Some cont_ty; context = ctx_bids; sol = None };
      let proof_hole = mk_hole proof_id in
      let cont_hole = mk_hole cont_id in
      let app_term = mk_app cont_hole proof_hole in
      let st_assigned = assign_meta g.goal_id app_term st in
      let proof_goal = { ctx = g.ctx; goal_type = ty; goal_id = proof_id } in
      let cont_goal = { ctx = g.ctx; goal_type = cont_ty; goal_id = cont_id } in
      let remaining_goals = List.tl st_assigned.open_goals in

      Success { st_assigned with open_goals = proof_goal :: cont_goal :: remaining_goals }
