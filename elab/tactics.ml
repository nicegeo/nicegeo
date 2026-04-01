open Term
open Types
open Proofstate

type tactic_result =
  | Success of proof_state
  | Failure of string

(** A tactic is a function from proof state to tactic result. *)
type tactic = proof_state -> tactic_result

let succeed st = Success st
let fail msg = Failure msg

(* ------------------------------------------------------------------ *)
(* Internal helpers                                                     *)
(* ------------------------------------------------------------------ *)

(** Catch elaboration errors from [f] and return them as [Failure] rather
    than letting them escape as exceptions. Used by tactics that call into
    the elaborator ([exact], future tactics with hole-filling). *)
let _catch_elab (ectx : ctx) (f : unit -> tactic_result) : tactic_result =
  try f () with Error.ElabError info -> fail (Error.pp_exn ectx info)

(** Full beta/delta reduction of [tm] in context [e].  Used to normalise
    goal types before pattern-matching on them. *)
let beta_nf (e : ctx) (tm : term) : term = Reduce.reduce e tm

(** Definitional equality: beta-normalise both sides, then compare
    structurally.  Handles alpha-equivalence for binders by rewriting one
    body's bid to match the other before recursing. *)
let rec def_eq (e : ctx) (t1 : term) (t2 : term) : bool =
  let t1 = beta_nf e t1 in
  let t2 = beta_nf e t2 in
  match (t1.inner, t2.inner) with
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

(** [with_hyps st g f] temporarily inserts the hypotheses from goal [g]
    into [lctx] for the duration of [f], then removes them.

    [infertype] looks up [Bvar] nodes in [lctx].  When a tactic hands a
    term to the elaborator, that term may contain [Bvar] nodes whose bids
    come from hypothesis binders introduced outside the term.  Without
    this injection those bids would be unknown to [infertype] and trigger
    an [InternalError].  Cleanup is guaranteed even if [f] raises. *)
let with_hyps (st : proof_state) (g : goal) (f : unit -> tactic_result) : tactic_result =
  let cleanup () =
    List.iter (fun h -> Hashtbl.remove st.elab_ctx.lctx h.hyp_bid) g.ctx
  in
  List.iter
    (fun h -> Hashtbl.add st.elab_ctx.lctx h.hyp_bid (Some h.hyp_name, h.hyp_type))
    g.ctx;
  match f () with
  | result -> cleanup (); result
  | exception exn -> cleanup (); raise exn

(** [resolve name g st] looks up [name] in the goal's local context first,
    then in the global environment.  Returns [(proof_term, type)] or [None].
    Hypotheses shadow globals with the same name. *)
let resolve (name : string) (g : goal) (st : proof_state) : (term * term) option =
  match List.find_opt (fun h -> h.hyp_name = name) g.ctx with
  | Some h -> Some (mk_bvar h.hyp_bid, h.hyp_type)
  | None ->
      match Hashtbl.find_opt st.elab_ctx.env name with
      | Some entry -> Some (mk_name name, entry.ty)
      | None -> None

(** Used by future tactics that need to pass the in-scope bids when
    creating subgoals (e.g. tactics that introduce new binders). *)
let _goal_stack (g : goal) : int list =
  List.map (fun h -> h.hyp_bid) g.ctx

(* ------------------------------------------------------------------ *)
(* Tactic combinators                                                   *)
(* ------------------------------------------------------------------ *)

(** [seq t1 t2 st] applies [t1] to [st].  On success, applies [t2] to the
    resulting state.  On failure, propagates the failure without running [t2]. *)
let seq (t1 : tactic) (t2 : tactic) (st : proof_state) : tactic_result =
  match t1 st with
  | Failure msg -> Failure msg
  | Success st' -> t2 st'

(** [try_tac t st] attempts [t].  If [t] fails, succeeds with [st] unchanged.
    Never fails itself. *)
let try_tac (t : tactic) (st : proof_state) : tactic_result =
  match t st with
  | Success st' -> Success st'
  | Failure _   -> succeed st

(** [repeat t st] applies [t] repeatedly until it fails, returning the last
    successful state.  If [t] fails immediately, returns [st].
    Never fails itself. *)
let rec repeat (t : tactic) (st : proof_state) : tactic_result =
  match t st with
  | Failure _    -> succeed st
  | Success st'  -> repeat t st'

(** Sequencing operator — right-associative alias for [seq]. *)
let ( >> ) = seq

(* ------------------------------------------------------------------ *)
(* Core proof tactics                                                   *)
(* ------------------------------------------------------------------ *)

(** [reflexivity st] closes an [Eq A lhs rhs] goal when [lhs] and [rhs]
    are definitionally equal.  Proof term: [@refl A lhs]. *)
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
       | _ ->
           fail (Printf.sprintf
             "reflexivity: goal '%s' is not of the form 'Eq A t t'."
             (pp_term st.elab_ctx ty)))

(** [exact tm st] closes the current goal if [tm]'s inferred type is
    definitionally equal to the goal type.

    Proof term: [tm] itself.

    Hypotheses are injected into [lctx] so that [infertype] can resolve
    [Bvar] nodes that refer to locally introduced variables (see
    [with_hyps]).  Elaboration errors are caught as [Failure]. *)
let exact (tm : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g ->
      with_hyps st g (fun () ->
        _catch_elab st.elab_ctx (fun () ->
          let inferred_ty = Typecheck.infertype st.elab_ctx tm in
          if def_eq st.elab_ctx inferred_ty g.goal_type then
            let st = assign_meta g.goal_id tm st in
            let st = close_goal  g.goal_id st in
            succeed st
          else
            fail (Printf.sprintf
              "exact: term has type '%s' but goal is '%s'."
              (pp_term st.elab_ctx inferred_ty)
              (pp_term st.elab_ctx g.goal_type))))

(** [apply name st] unifies the conclusion of [name]'s type with the
    current goal.

    - Arrow case: if [name : A → B] and the conclusion [B] is definitionally
      equal to the goal, closes the goal with proof [name ?premise] and
      opens a fresh subgoal for [A].
      The fresh meta for [?premise] is only registered after the conclusion
      check passes — so a failing [apply] never leaks a meta.
    - Non-arrow case: behaves like [exact] (direct definitional equality
      check).

    Hypotheses shadow globals (see [resolve]). *)
let apply (name : string) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g ->
      (match resolve name g st with
       | None -> fail (Printf.sprintf "apply: unknown name '%s'." name)
       | Some (tm, f_ty) ->
           let f_ty = beta_nf st.elab_ctx f_ty in
           (match f_ty.inner with
            | Arrow (_, bid, premise_ty, conclusion_ty) ->
                (* Instantiate the conclusion with a placeholder before checking,
                   so a mismatch doesn't leave a stale meta in the table. *)
                let hole_id = gen_hole_id () in
                let hole = mk_hole hole_id in
                let conclusion =
                  Reduce.subst st.elab_ctx conclusion_ty (Bvar bid) hole.inner
                in
                if def_eq st.elab_ctx conclusion g.goal_type then begin
                  let context = List.map (fun h -> h.hyp_bid) g.ctx in
                  Hashtbl.replace st.elab_ctx.metas hole_id
                    { ty = Some premise_ty; context; sol = None };
                  let subgoal = { ctx = g.ctx; goal_type = premise_ty; goal_id = hole_id } in
                  let st = { st with open_goals = st.open_goals @ [subgoal] } in
                  let st = assign_meta g.goal_id (mk_app tm hole) st in
                  let st = close_goal  g.goal_id st in
                  succeed st
                end else
                  fail (Printf.sprintf
                    "apply: conclusion '%s' does not match goal '%s'."
                    (pp_term st.elab_ctx conclusion)
                    (pp_term st.elab_ctx g.goal_type))
            | _ ->
                if def_eq st.elab_ctx f_ty g.goal_type then
                  let st = assign_meta g.goal_id tm st in
                  let st = close_goal  g.goal_id st in
                  succeed st
                else
                  fail (Printf.sprintf
                    "apply: '%s' has type '%s' but goal is '%s'."
                    name
                    (pp_term st.elab_ctx f_ty)
                    (pp_term st.elab_ctx g.goal_type))))

(** Lazily register [sorry_ax : (A : Prop) → A] in both the elaboration
    and kernel environments.  Called at most once per [elab_ctx]. *)
let ensure_sorry_ax (st : proof_state) : unit =
  if not (Hashtbl.mem st.elab_ctx.env "sorry_ax") then begin
    let bid = Term.gen_binder_id () in
    let elab_ty = mk_arrow (Some "A") bid (mk_sort 0) (mk_bvar bid) in
    let k_ty = Convert.conv_to_kterm elab_ty in
    Hashtbl.add st.elab_ctx.env  "sorry_ax" { name = "sorry_ax"; ty = elab_ty; data = Axiom };
    Hashtbl.add st.elab_ctx.kenv "sorry_ax" k_ty
  end

(** [sorry st] closes any goal with a logically unsound placeholder proof.

    Registers the axiom [sorry_ax : (A : Prop) → A] on first use and
    assigns [sorry_ax goal_type] as the proof term.  Emits a warning to
    stderr.

    Use only during development to defer proof obligations. *)
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

(** [intro name st] introduces the premise of the current implication into
    the local context.

    Precondition: the current goal (after beta-normalisation) has shape
    [A → B].

    Effect: closes the current goal with proof [fun (name : A) => ?body]
    and opens a new goal [name : A ⊢ B].  The fresh body hole reuses the
    binder id from the Arrow node, so any occurrences of that id in [B]
    continue to refer to the introduced hypothesis. *)
let intro (name : string) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "intro: no goals remaining"
  | Some g ->
      let ty = beta_nf st.elab_ctx g.goal_type in
      (match ty.inner with
       | Arrow (_, bid, premise_ty, conclusion_ty) ->
           let hole_id = fresh_id () in
           let hole    = mk_hole hole_id in
           let new_hyp = { hyp_name = name; hyp_bid = bid; hyp_def = None; hyp_type = premise_ty } in
           let new_ctx_bids = bid :: List.map (fun h -> h.hyp_bid) g.ctx in
           Hashtbl.replace st.elab_ctx.metas hole_id
             { ty = Some conclusion_ty; context = new_ctx_bids; sol = None };
           let new_goal = { ctx = new_hyp :: g.ctx; goal_type = conclusion_ty; goal_id = hole_id } in
           let st = assign_meta g.goal_id (mk_fun (Some name) bid premise_ty hole) st in
           let st = close_goal  g.goal_id st in
           succeed { st with open_goals = new_goal :: st.open_goals }
       | _ -> fail "intro: goal is not an implication or forall")

(** [intros names] applies [intro] for each name in order.  Equivalent to
    [intro n₁ >> intro n₂ >> … >> intro nₖ].  [intros []] is the identity.
    Fails if any [intro] in the chain fails. *)
let rec intros (names : string list) : tactic =
  match names with
  | []           -> succeed
  | name :: rest -> intro name >> intros rest

(** [have name ty st] introduces an intermediate lemma named [name] of
    type [ty].

    Replaces the current goal [G] with two ordered subgoals:
      1. [ctx ⊢ ty]               — prove the intermediate claim
      2. [ctx ⊢ (name : ty) → G]  — prove the continuation using the claim

    Proof term assigned to the original goal: [?cont ?proof], where
    [?cont : (name : ty) → G] and [?proof : ty].

    Note: [name] is not added directly to the continuation's context.
    The second subgoal has type [(name : ty) → G]; use [intro name] to
    bring it into scope. *)
let have (name : string) (ty : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "have: no goals remaining"
  | Some g ->
      let bid      = Term.gen_binder_id () in
      let cont_ty  = mk_arrow (Some name) bid ty g.goal_type in
      let ctx_bids = List.map (fun h -> h.hyp_bid) g.ctx in
      let proof_id = fresh_id () in
      let cont_id  = fresh_id () in
      Hashtbl.replace st.elab_ctx.metas proof_id
        { ty = Some ty;      context = ctx_bids; sol = None };
      Hashtbl.replace st.elab_ctx.metas cont_id
        { ty = Some cont_ty; context = ctx_bids; sol = None };
      let proof_hole = mk_hole proof_id in
      let cont_hole  = mk_hole cont_id  in
      let proof_goal = { ctx = g.ctx; goal_type = ty;      goal_id = proof_id } in
      let cont_goal  = { ctx = g.ctx; goal_type = cont_ty; goal_id = cont_id  } in
      let st = assign_meta g.goal_id (mk_app cont_hole proof_hole) st in
      let st = close_goal  g.goal_id st in
      succeed { st with open_goals = proof_goal :: cont_goal :: st.open_goals }
