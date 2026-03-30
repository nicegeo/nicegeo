open Term
open Types
open Proofstate 

type tactic_result =
  | Success of proof_state
  | Failure of string

let succeed st  = Success st
let fail    msg = Failure msg 
let failf fmt = Printf.ksprintf fail fmt

let no_goals_msg = "No goals remaining."

(* Used by future tactics that need to catch elaboration errors and return a Failure. *)
let catch_elab (ectx : ctx) (f : unit -> tactic_result) : tactic_result =
  try f ()
  with Error.ElabError info -> fail (Error.pp_exn ectx info)


let beta_nf (e : ctx) (tm : term) : term = Reduce.reduce e tm


let rec def_eq (e : ctx) (t1 : term) (t2 : term) : bool =
  let t1 = beta_nf e t1 in
  let t2 = beta_nf e t2 in
  match t1.inner, t2.inner with
  | Sort i,    Sort j    -> i = j
  | Bvar i,    Bvar j    -> i = j
  | Name s,    Name t    -> s = t
  | Hole i,    Hole j    -> i = j
  | App (f1, x1), App (f2, x2) ->
      def_eq e f1 f2 && def_eq e x1 x2
  | Fun (_, bid1, ty1, b1), Fun (_, bid2, ty2, b2) ->
      def_eq e ty1 ty2 &&
      def_eq e b1 (Reduce.subst e b2 (Bvar bid2) (Bvar bid1))
  | Arrow (_, bid1, ty1, r1), Arrow (_, bid2, ty2, r2) ->
      def_eq e ty1 ty2 &&
      def_eq e r1 (Reduce.subst e r2 (Bvar bid2) (Bvar bid1))
  | _ -> false

(* Used by future tactics that need to pass the in-scope bids when creating subgoals. *)
let _goal_stack (g : goal) : int list =
	List.map (fun h -> h.hyp_bid) g.ctx

(*[Eq A lhs rhs] when [lhs] and [rhs] are definitionally equal, proof term is [@refl A lhs].*)
let reflexivity (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g ->
      let ty = beta_nf st.elab_ctx g.goal_type in
      (match ty.inner with
       | App ({ inner = App ({ inner = App ({ inner = Name "Eq"; _ }, _a); _ }, lhs); _ }, rhs) ->
           if def_eq st.elab_ctx lhs rhs then
             let proof = mk_app (mk_app (mk_name "refl") _a) lhs in
             let st = assign_meta g.goal_id proof st in
             let st = close_goal  g.goal_id st in
             succeed st
           else
             fail (Printf.sprintf
               "reflexivity: lhs '%s' and rhs '%s' are not definitionally equal."
               (pp_term st.elab_ctx lhs) (pp_term st.elab_ctx rhs))
               (* need to map to existing error categories*)
       | _ ->
           fail (Printf.sprintf
             "reflexivity: goal '%s' is not of the form 'Eq A t t'."
             (pp_term st.elab_ctx ty)))
      		 (* need to map to existing error categories*)

(* [infertype] looks up [Bvar] nodes in [lctx]. Hypotheses live in the goal's
   local context but are not in [lctx] yet — populate it for the duration of [f],
   then remove them so we leave [lctx] exactly as we found it. *)
let with_hyps (st : proof_state) (g : goal) (f : unit -> tactic_result) : tactic_result =
  List.iter (fun h ->
    Hashtbl.add st.elab_ctx.lctx h.hyp_bid (Some h.hyp_name, h.hyp_type)
  ) g.ctx;
  try
    let result = f () in
    List.iter (fun h ->
      Hashtbl.remove st.elab_ctx.lctx h.hyp_bid
    ) g.ctx;
    result
  with exn ->
    List.iter (fun h ->
      Hashtbl.remove st.elab_ctx.lctx h.hyp_bid
    ) g.ctx;
    raise exn

let with_current_goal (st : proof_state) (f : goal -> tactic_result) : tactic_result =
  match current_goal st with
  | None -> fail no_goals_msg
  | Some g -> f g

let solve_goal (g : goal) (proof : term) (st : proof_state) : tactic_result =
  succeed (close_goal g.goal_id (assign_meta g.goal_id proof st))

let fail_goal_type_mismatch
    (tactic : string)
    (subject : string)
    (ectx : ctx)
    (actual_ty : term)
    (goal_ty : term) : tactic_result =
  failf "%s: %s has type '%s' but goal is '%s'."
    tactic
    subject
    (pp_term ectx actual_ty)
    (pp_term ectx goal_ty)

let solve_if_goal_type_matches
    (tactic : string)
    (subject : string)
    (proof : term)
    (proof_ty : term)
    (g : goal)
    (st : proof_state) : tactic_result =
  if def_eq st.elab_ctx proof_ty g.goal_type then
    solve_goal g proof st
  else
    fail_goal_type_mismatch tactic subject st.elab_ctx proof_ty g.goal_type

let open_subgoal
    (st : proof_state)
    (ctx : local_ctx)
    (goal_id : int)
    (goal_type : term) : term * proof_state =
  let hole = mk_hole goal_id in
  let context = List.map (fun h -> h.hyp_bid) ctx in
  Hashtbl.replace st.elab_ctx.metas goal_id { ty = Some goal_type; context; sol = None };
  let g = { ctx; goal_type; goal_id } in
  (hole, { st with open_goals = st.open_goals @ [g] })

let exact (tm : term) (st : proof_state) : tactic_result =
  with_current_goal st (fun g ->
    with_hyps st g (fun () ->
      catch_elab st.elab_ctx (fun () ->
        let inferred_ty = Typecheck.infertype st.elab_ctx tm in
        solve_if_goal_type_matches "exact" "term" tm inferred_ty g st
      )
    )
  )

(* Resolve [name] to a proof term and its type: hypotheses shadow global names. *)
let resolve (name : string) (g : goal) (st : proof_state)
    : (term * term) option =
  match List.find_opt (fun h -> h.hyp_name = name) g.ctx with
  | Some h -> Some (mk_bvar h.hyp_bid, h.hyp_type)
  | None ->
      match Hashtbl.find_opt st.elab_ctx.env name with
      | Some entry -> Some (mk_name name, entry.ty)
      | None -> None

(* [apply name st] looks up [name] as a hypothesis or global lemma, then:
   - if its type is [A -> B] and [B] matches the goal, closes the goal and
     opens a new subgoal for [A];
   - if its type directly matches the goal (no arrow), closes it like [exact]. *)
let apply (name : string) (st : proof_state) : tactic_result =
  with_current_goal st (fun g ->
    match resolve name g st with
    | None -> failf "apply: unknown name '%s'." name
    | Some (tm, f_ty) ->
        let f_ty = beta_nf st.elab_ctx f_ty in
        match f_ty.inner with
        | Arrow (_, bid, premise_ty, conclusion_ty) ->
            let hole_id = gen_hole_id () in
            let preview_hole = mk_hole hole_id in
            let conclusion =
              Reduce.subst st.elab_ctx conclusion_ty (Bvar bid) preview_hole.inner
            in
            if def_eq st.elab_ctx conclusion g.goal_type then
              let (hole, st) = open_subgoal st g.ctx hole_id premise_ty in
              solve_goal g (mk_app tm hole) st
            else
              failf "apply: conclusion '%s' does not match goal '%s'."
                (pp_term st.elab_ctx conclusion)
                (pp_term st.elab_ctx g.goal_type)
        | _ ->
            solve_if_goal_type_matches
              "apply"
              (Printf.sprintf "'%s'" name)
              tm
              f_ty
              g
              st
  )

let ensure_sorry_ax (st : proof_state) : unit = 
  if not (Hashtbl.mem st.elab_ctx.env "sorry_ax") then
    let bid = Term.gen_binder_id () in
    let elab_ty = mk_arrow (Some "A") bid (mk_sort 0) (mk_bvar bid) in
    let k_ty = Convert.conv_to_kterm elab_ty in
    Hashtbl.add st.elab_ctx.env "sorry_ax"
      { name = "sorry_ax"; ty = elab_ty; data = Axiom};
    Hashtbl.add st.elab_ctx.kenv "sorry_ax" k_ty

let sorry (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g ->
      Printf.eprintf "Warning: proof used sorry - this proof is not valid. \n";
      ensure_sorry_ax st;
      let proof = mk_app (mk_name "sorry_ax") g.goal_type in
      let st = assign_meta g.goal_id proof st in
      let st = close_goal  g.goal_id st in
      succeed st
