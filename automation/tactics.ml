open Elab.Term
open Elab.Types
open Elab.Proofstate
open Elab.Typecheck
open Elab.Tactic

let succeed st = Success st
let fail msg = Failure msg

(* Used by future tactics that need to catch elaboration errors and return a Failure. *)
let catch_elab (ectx : ctx) (f : unit -> tactic_result) : tactic_result =
  try f () with Elab.Error.ElabError info -> fail (Elab.Error.pp_exn ectx info)

let beta_nf (e : ctx) (tm : term) : term = Elab.Reduce.reduce e tm

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
      def_eq e ty1 ty2 && def_eq e b1 (Elab.Reduce.subst e b2 (Bvar bid2) (Bvar bid1))
  | Arrow (_, bid1, ty1, r1), Arrow (_, bid2, ty2, r2) ->
      def_eq e ty1 ty2 && def_eq e r1 (Elab.Reduce.subst e r2 (Bvar bid2) (Bvar bid1))
  | _ -> false

let destruct_eq (e : ctx) (t : term) : term * term * term =
  let t = beta_nf e t in
  match t.inner with
  | App ({ inner = App ({ inner = App ({ inner = Name "Eq"; _ }, a); _ }, lhs); _ }, rhs)
    ->
      (a, lhs, rhs)
  | _ -> failwith (Printf.sprintf "expected 'Eq A lhs rhs', got '%s'" (pp_term e t))

(** [Eq A lhs rhs] when [lhs] and [rhs] are definitionally equal, proof term is
    + [@refl A lhs]. *)
let reflexivity (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g ->
      let ty = beta_nf st.elab_ctx g.goal_type in
      let _a, lhs, rhs = destruct_eq st.elab_ctx ty in
      if def_eq st.elab_ctx lhs rhs then
        let proof = mk_app (mk_app (mk_name "Eq.intro") _a) lhs in
        let st = assign_meta g.goal_id proof st in
        let st = close_goal g.goal_id st in
        succeed st
      else
        fail
          (Printf.sprintf
             "reflexivity: lhs '%s' and rhs '%s' are not definitionally equal."
             (pp_term st.elab_ctx lhs)
             (pp_term st.elab_ctx rhs))
(* need to map to existing error categories*)

let exact (tm : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g ->
      (* Catch ill-typed or unknown-name errors from infertype as Failure
        rather than letting them escape as exceptions. *)
      catch_elab st.elab_ctx (fun () ->
          (* try to elaborate the input with the expected goal type *)
          create_metas st.elab_ctx tm (List.map (fun h -> h.bid) g.lctx);
          let ty = infertype st.elab_ctx g.lctx tm in
          unify st.elab_ctx ty (Hashtbl.create 0) g.goal_type (Hashtbl.create 0);
          (* check all holes are filled *)
          (* here lean's refine would instead open a goal for each unfilled hole *)
          ignore (replace_metas st.elab_ctx tm);
          let st = assign_meta g.goal_id tm st in
          let st = close_goal g.goal_id st in
          succeed st)

(** Modifies the contents of [tbl1] to the contents of [tbl2]. Useful for restoring the
    state of the ctx.metas table. *)
let hashtbl_set tbl1 tbl2 =
  if tbl1 != tbl2 then (
    Hashtbl.clear tbl1;
    Hashtbl.iter (fun k v -> Hashtbl.replace tbl1 k v) tbl2)

(** [apply tm st] attempts to solve the current goal by applying [tm].

    The tactic repeatedly tries [tm], [tm ?m1], [tm ?m1 ?m2], ... by introducing fresh
    metavariables as arguments until the inferred type of the application unifies with the
    goal type. On success it assigns the current goal to the application term and opens
    one subgoal per introduced metavariable (in argument order), each under the current
    local context.

    Metavariable assignments produced by unsuccessful attempts are discarded by restoring
    the original metavariable table before trying the next application. If no application
    shape yields a well-typed term that unifies with the goal, the tactic fails. *)
let apply (tm : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g ->
      (* Create a copy of the metas state for restoration. This is required because the 
         tactic interface expects us to modify the passed in st.elab_ctx.metas as it does 
         not use the returned st.elab_ctx.metas. *)
      let metas = Hashtbl.copy st.elab_ctx.metas in
      let lctx_bids = List.map (fun h -> h.bid) g.lctx in
      let rec loop (sol : term) (goal_ids : int list) : tactic_result =
        create_metas st.elab_ctx sol lctx_bids;
        try
          let sol_ty = infertype st.elab_ctx g.lctx sol in
          try
            unify st.elab_ctx sol_ty (Hashtbl.create 0) g.goal_type (Hashtbl.create 0);
            (* unification succeeded, set the solution and open goals *)
            let st = assign_meta g.goal_id sol st in
            let st = close_goal g.goal_id st in
            let goals =
              List.map
                (fun id ->
                  {
                    lctx = g.lctx;
                    goal_type = (Hashtbl.find st.elab_ctx.metas id).ty |> Option.get;
                    goal_id = id;
                  })
                (List.rev goal_ids)
            in
            Success { st with open_goals = goals @ st.open_goals }
          with Elab.Error.ElabError _ ->
            (* unification failed, try with another application term *)
            (* restore metas state *)
            hashtbl_set st.elab_ctx.metas metas;
            let subgoal_id = gen_hole_id () in
            loop (mk_app sol (mk_hole subgoal_id)) (subgoal_id :: goal_ids)
        with Elab.Error.ElabError _ ->
          (* infertype failed so term is not well-typed, probably added too many terms so we are done *)
          (* restore metas state *)
          hashtbl_set st.elab_ctx.metas metas;
          Failure "application of term does not unify with the goal"
      in
      loop tm []

let ensure_sorry_ax (st : proof_state) : unit =
  if not (Hashtbl.mem st.elab_ctx.env "sorry_ax") then (
    let bid = Elab.Term.gen_binder_id () in
    let elab_ty = mk_arrow (Some "A") bid (mk_sort 0) (mk_bvar bid) in
    let k_ty = Elab.Convert.conv_to_kterm elab_ty in
    Hashtbl.add
      st.elab_ctx.env
      "sorry_ax"
      { name = "sorry_ax"; ty = elab_ty; data = Axiom };
    Hashtbl.add st.elab_ctx.kenv.types "sorry_ax" k_ty)

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
      match (whnf st.elab_ctx g.goal_type).inner with
      | Arrow (_, bid, premise_ty, conclusion_ty) ->
          let hole_id = fresh_id () in
          let hole = mk_hole hole_id in
          let proof_term = mk_fun (Some name) bid premise_ty hole in
          let new_hyp = { name = Some name; bid; ty = premise_ty } in
          let st_assigned = assign_meta g.goal_id proof_term st in
          let new_lctx = new_hyp :: g.lctx in
          let new_ctx_bids = List.map (fun h -> h.bid) new_lctx in
          Hashtbl.replace
            st.elab_ctx.metas
            hole_id
            { ty = Some conclusion_ty; context = new_ctx_bids; sol = None };
          let new_goal =
            { lctx = new_lctx; goal_type = conclusion_ty; goal_id = hole_id }
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
      create_metas st.elab_ctx ty (List.map (fun h -> h.bid) g.lctx);
      (* fill holes if not itself a hole *)
      (match ty.inner with
      | Hole _ -> ()
      | _ -> ignore (infertype st.elab_ctx g.lctx ty));
      let proof_id = fresh_id () in
      let cont_id = fresh_id () in
      let fun_bid = gen_binder_id () in
      let ctx_bids = List.map (fun h -> h.bid) g.lctx in
      let cont_ctx = { name = Some name; bid = fun_bid; ty } :: g.lctx in
      let cont_ctx_bids = List.map (fun h -> h.bid) cont_ctx in
      Hashtbl.replace
        st.elab_ctx.metas
        proof_id
        { ty = Some ty; context = ctx_bids; sol = None };
      Hashtbl.replace
        st.elab_ctx.metas
        cont_id
        { ty = Some g.goal_type; context = cont_ctx_bids; sol = None };
      let proof_hole = mk_hole proof_id in
      let cont_hole = mk_hole cont_id in
      let proof = mk_app (mk_fun (Some name) fun_bid ty cont_hole) proof_hole in
      let st_assigned = assign_meta g.goal_id proof st in
      let proof_goal = { lctx = g.lctx; goal_type = ty; goal_id = proof_id } in
      let cont_goal = { lctx = cont_ctx; goal_type = g.goal_type; goal_id = cont_id } in
      let remaining_goals = List.tl st_assigned.open_goals in

      Success { st_assigned with open_goals = proof_goal :: cont_goal :: remaining_goals }

(*
  Fold the function `f` over all the children of the given term.

  Inspired by Rocq's fold functions
*)
let term_fold (f : 'a -> term -> 'a) (t : term) (acc : 'a) : 'a =
  match t.inner with
  | Fun (_, _, t1, t2) -> f (f acc t1) t2
  | Arrow (_, _, t1, t2) -> f (f acc t1) t2
  | App (t1, t2) -> f (f acc t1) t2
  | _ -> acc

(*
  Apply the function `f` to all the children of the given term.

  Inspired by Rocq's fold functions
*)
let term_map (f : term -> term) (t : term) : term =
  match t.inner with
  | Fun (a, b, t1, t2) -> { loc = t.loc; inner = Fun (a, b, f t1, f t2) }
  | Arrow (a, b, t1, t2) -> { loc = t.loc; inner = Arrow (a, b, f t1, f t2) }
  | App (t1, t2) -> { loc = t.loc; inner = App (f t1, f t2) }
  | _ -> t

(*
  Abstract out all subterms that are defeq to the given pattern.
  Returns the binder id used and the new term.

  Inspired by Lean's kabstract function
*)
let abstract_pat (ctx : ctx) (t : term) (pat : term) : int * term =
  let bid = gen_binder_id () in
  let rec go (t : term) =
    try
      (* If they unify, then replace the term with a bvar

        Notice that since we do not modify the local context,
        `pat` should not unify with `t` if `t` contains a free variable. *)
      unify ctx t (Hashtbl.create 0) pat (Hashtbl.create 0);
      { loc = t.loc; inner = Bvar bid }
    with _ -> term_map (fun term -> go term) t
  in
  (bid, go t)

(*
  Check if the term contains the given binder id anywhere iside of it
*)
let rec has_bid ?(acc = false) (bid : int) (t : term) : bool =
  acc
  ||
  match t.inner with
  | Bvar i -> i == bid
  | _ -> term_fold (fun acc term -> has_bid ~acc bid term) t acc

(*
  Get the list of possible motives to rewrite with.
  We currently only return one motive, the one that abstacts out eerything.
*)
let get_rewrite_motives (ctx : ctx) (t : term) (ty : term) (pat : term) : term list =
  let bid, abstracted = abstract_pat ctx t pat in
  if has_bid bid abstracted then [ mk_fun (Some "x") bid ty abstracted ] else []

(*
  Given a term `t : lhs = rhs`, it rewrites all occurrences of `lhs`
  to being `rhs` in the new goal.
*)
let rewrite (t : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g -> (
      create_metas st.elab_ctx t (List.map (fun h -> h.bid) g.lctx);
      let t_ty = beta_nf st.elab_ctx (infertype st.elab_ctx g.lctx t) in
      let eq_ty, lhs, rhs = destruct_eq st.elab_ctx t_ty in
      let motives = get_rewrite_motives st.elab_ctx g.goal_type eq_ty lhs in
      match motives with
      | p :: _ ->
          let new_goal_ty = whnf st.elab_ctx (mk_app p rhs) in
          let new_hole, st = fresh_goal st g.lctx new_goal_ty in
          (* Eq.symm A lhs rhs t *)
          let sym =
            mk_app (mk_app (mk_app (mk_app (mk_name "Eq.symm") eq_ty) lhs) rhs) t
          in
          (* Eq.elim A rhs P new_hole lhs (Eq.symm A lhs rhs t) *)
          let proof =
            mk_app
              (mk_app
                 (mk_app
                    (mk_app (mk_app (mk_app (mk_name "Eq.elim") eq_ty) rhs) p)
                    new_hole)
                 lhs)
              sym
          in
          let st = assign_meta g.goal_id proof st in
          let st = close_goal g.goal_id st in
          succeed st
      | [] ->
          fail
            (Printf.sprintf
               "rewrite: failed to find instance of '%s' in goal '%s'"
               (pp_term st.elab_ctx lhs)
               (pp_term st.elab_ctx g.goal_type)))

(** Breaks goal of the form [A and B] into two subgoals for [A] and [B] by applying
    [And.intro]. Fails if the current goal is not a conjunction. *)
let split (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g -> (
      let ty = beta_nf st.elab_ctx g.goal_type in
      match ty.inner with
      | App ({ inner = App ({ inner = Name "And"; _ }, a); _ }, b) ->
          let hole_b, st = fresh_goal st g.lctx b in
          let hole_a, st = fresh_goal st g.lctx a in
          let proof =
            mk_app (mk_app (mk_app (mk_app (mk_name "And.intro") a) b) hole_a) hole_b
          in
          let st = assign_meta g.goal_id proof st in
          let st = close_goal g.goal_id st in

          succeed st
      | _ ->
          fail
            (Printf.sprintf
               "split: goal '%s' is not a conjunction."
               (pp_term st.elab_ctx ty)))

(** Helper function that creates a tuple (hole_id, hole_term) where the hole_term is just
    the Hole term corresponding to the created hole ID *)
let create_hole () : int * term =
  let hole_id = gen_hole_id () in
  let hole_term = mk_hole hole_id in
  (hole_id, hole_term)

(** Get the solution term for the hole `hole_id`, or return None if there is no solution
    for the given hole (i.e. unification couldn't find a solution) *)
let get_hole_sol (ctx : ctx) (hole_id : int) : term option =
  match Hashtbl.find_opt ctx.metas hole_id with
  | Some mvar -> mvar.sol
  | None -> failwith "internal nicegeo programming error: created hole does not exist!"

(** Create a new context by adding each hole that appears in `expected_term` to the
    existing context `ctx` if it hasn't been added already.

    This function doesn't modify `ctx` itself, instead returning the new context, in
    addition to the list of hole IDs for all of the created holes *)
let ctx_with_new_holes (g : goal) (ctx : ctx) (expected_term : term) : ctx =
  let metas = Hashtbl.copy ctx.metas in
  let new_ctx = { ctx with metas } in
  (* g.lctx includes a list of local variables (represented as binder IDs) that
  are in scope when the goal term would be used (e.g. the variables x and y in
  `fun x => fun y => <hole for g>`)

  In general, the goal type is allowed to depend on any variables that are in
  scope when it's used, and using those binder IDs here ensures that all holes
  created are allowed to reference said variables.
   *)
  let outer_local_var_bids = List.map (fun h -> h.bid) g.lctx in
  create_metas new_ctx expected_term outer_local_var_bids;
  new_ctx

(** Use unification to both check if a given term `t` matches a certain expected format,
    where the expected format is specified as a term with holes for places where arbitrary
    values are allowed. Specifically, The expected format is specified by `expected_term`,
    which should use new holes created by the user (e.g. using `create_hole`) for the
    subterms that need to get inferred in the expected term.

    This function returns a new context that contains the result of unification (instead
    of modifying the provided context) *)
let match_term_and_solve_holes (g : goal) (ctx : ctx) (t : term) (expected_term : term) :
    ctx =
  (* expected_term has holes added by the user to specify what they want to infer,
  so make sure those holes are added to the new context *)
  let ctx = ctx_with_new_holes g ctx expected_term in
  unify ctx t (Hashtbl.create 0) expected_term (Hashtbl.create 0);

  ctx

(*
  This infers the motive p of the existential type when constructing an Exists.intro.
  It uses the type A to construct the expected type, leaving in a hole for the motive.
  It then calls unification with a fresh hole for p, to unify the goal with the type
  Exists A ?p, where ?p : A -> Prop. If successful, it returns Some p, otherwise None.
*)
let infer_motive (exists_type : term) (g : goal) (ctx : ctx) : term option =
  let motive_hole_id, motive_hole = create_hole () in

  let expected_term = mk_app_multiarg (mk_name "Exists") [ exists_type; motive_hole ] in
  let ctx = match_term_and_solve_holes g ctx g.goal_type expected_term in
  get_hole_sol ctx motive_hole_id

(*
 * This implements the exists tactic, which takes term a as an argument, and constructs
 * an existential from there that unifies appropriately with the goal type. It infers
 * the motive automatically from the goal type, which should have form Exists A ?p
 * where a : A and ?p : A -> Prop.
 *)
let exists (a : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | Some g -> (
      (* infer A *)
      let exists_type = Elab.Typecheck.infertype st.elab_ctx g.lctx a in
      (* infer the motive p *)
      match infer_motive exists_type g st.elab_ctx with
      | Some p ->
          (* update the goal to (p a) *)
          let new_goal_ty = whnf st.elab_ctx (mk_app p a) in
          let new_hole, st = fresh_goal st g.lctx new_goal_ty in
          (* construct the proof term *)
          let proof =
            mk_app_multiarg (mk_name "Exists.intro") [ exists_type; p; a; new_hole ]
          in
          (* update the proof state accordingly *)
          let st = assign_meta g.goal_id proof st in
          let st = close_goal g.goal_id st in
          succeed st
      | None -> fail "Goal must have the form [Exists A p]")
  | None -> fail "No goals remaining"

(** Infer the values of A and B such that the goal type for `g` is `Or A B`, or return
    None if values of A and B can't be found *)
let infer_or_type (g : goal) (st : proof_state) : (term * term) option =
  let ctx = st.elab_ctx in
  (* Create holes for both arguments to `Or` (which are both Props representing the type) *)
  let left_hole_id, left_hole = create_hole () in
  let right_hole_id, right_hole = create_hole () in

  let expected_or_type = mk_app_multiarg (mk_name "Or") [ left_hole; right_hole ] in
  let ctx = match_term_and_solve_holes g ctx g.goal_type expected_or_type in
  match (get_hole_sol ctx left_hole_id, get_hole_sol ctx right_hole_id) with
  | Some left_type, Some right_type -> Some (left_type, right_type)
  | _ -> None

(** Constructor tactic for Or that behaves like `right` (i.e. turns the right side of the
    Or into the goal) if the argument `use_right` is true, and behaves like `left` if not
*)
let constructor_or_tactic (use_right : bool) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining"
  | Some g -> (
      match infer_or_type g st with
      | None -> fail "Goal must be of the form [Or A B]"
      | Some (left_type, right_type) ->
          let new_goal_type = if use_right then right_type else left_type in
          let new_goal_hole, st = fresh_goal st g.lctx new_goal_type in

          let constructor_name = if use_right then "Or.inr" else "Or.inl" in
          let curr_goal_proof =
            mk_app_multiarg
              (mk_name constructor_name)
              [ left_type; right_type; new_goal_hole ]
          in
          let st = assign_meta g.goal_id curr_goal_proof st in
          let st = close_goal g.goal_id st in
          succeed st)

let left = constructor_or_tactic false
let right = constructor_or_tactic true

(** eliminating an Or. name1 is the name of the left hypothesis in the first subgoal,
    name2 is the name of the right hypothesis in the second subgoal *)
let cases (tm : term) (name1 : string) (name2 : string) (st : proof_state) : tactic_result
    =
  match current_goal st with
  | None -> fail "No goals remaining"
  | Some g -> (
      create_metas st.elab_ctx tm (List.map (fun h -> h.bid) g.lctx);
      let tm_ty = Elab.Typecheck.infertype st.elab_ctx g.lctx tm in
      let left_hole_id, left_hole = create_hole () in
      let right_hole_id, right_hole = create_hole () in

      let expected_or_type = mk_app_multiarg (mk_name "Or") [ left_hole; right_hole ] in
      let ctx = match_term_and_solve_holes g st.elab_ctx tm_ty expected_or_type in
      match (get_hole_sol ctx left_hole_id, get_hole_sol ctx right_hole_id) with
      | Some left_type, Some right_type ->
          let left_fun_bid = gen_binder_id () in
          let right_fun_bid = gen_binder_id () in
          let left_entry = { name = Some name1; bid = left_fun_bid; ty = left_type } in
          let right_entry = { name = Some name2; bid = right_fun_bid; ty = right_type } in
          let right_goal_hole, st = fresh_goal st (right_entry :: g.lctx) g.goal_type in
          let left_goal_hole, st = fresh_goal st (left_entry :: g.lctx) g.goal_type in
          let left_fun = mk_fun (Some name1) left_fun_bid left_type left_goal_hole in
          let right_fun = mk_fun (Some name2) right_fun_bid right_type right_goal_hole in

          let proof =
            mk_app_multiarg
              (mk_name "Or.elim")
              [ left_type; right_type; g.goal_type; tm; left_fun; right_fun ]
          in
          let st = assign_meta g.goal_id proof st in
          let st = close_goal g.goal_id st in
          succeed st
      | _ -> fail "Argument must have type [Or A B]")

(*
 * Infer both [A] and the motive [p] for the choose tactic, by way of unifying
 * with the input term [e : Exists ?? ??]
 *)
let infer_choose_types (e : term) (g : goal) (st : proof_state) :
    term option * term option =
  let hole_a_typ = gen_hole_id () in
  let hole_p = gen_hole_id () in

  let expected =
    mk_app (mk_app (mk_name "Exists") (mk_hole hole_a_typ)) (mk_hole hole_p)
  in
  create_metas st.elab_ctx e (List.map (fun h -> h.bid) g.lctx);
  let e_typ = Elab.Typecheck.infertype st.elab_ctx g.lctx e in
  let ctx = ctx_with_new_holes g st.elab_ctx expected in
  unify ctx e_typ (Hashtbl.create 0) expected (Hashtbl.create 0);
  match (Hashtbl.find_opt ctx.metas hole_a_typ, Hashtbl.find_opt ctx.metas hole_p) with
  | Some mvar1, Some mvar2 -> (mvar1.sol, mvar2.sol)
  | _ -> failwith "internal nicegeo programming error: created hole does not exist!"

(*
 * Given a term whose type unifies with type [Exists A p], infer A and p,
 * and introduce new hypothesis representing the first and (dependent) second 
 * projections of the existential. Do not delete any hypotheses. Do not change
 * the goal. Do update the proof term to represent the application of the
 * eliminator [Exists.elim A p b e (fun (a : A) (h : p a) => ??)].
 *)
let choose (names : string * string) (e : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | Some g -> (
      (* infer A and p *)
      match infer_choose_types e g st with
      | Some a_typ, Some p ->
          (* define new hypotheses *)
          let bid_a_typ = Elab.Term.gen_binder_id () in
          let hyp_a_typ = { name = Some (fst names); bid = bid_a_typ; ty = a_typ } in
          let bid_h = Elab.Term.gen_binder_id () in
          let ty = whnf st.elab_ctx (mk_app p (mk_bvar bid_a_typ)) in
          let hyp_h = { name = Some (snd names); bid = bid_h; ty } in
          let subgoal_lctx = hyp_h :: hyp_a_typ :: g.lctx in
          (* construct the proof term *)
          let new_hole, st = fresh_goal st subgoal_lctx g.goal_type in
          let proof =
            mk_app
              (mk_app
                 (mk_app (mk_app (mk_app (mk_name "Exists.elim") a_typ) p) g.goal_type)
                 e)
              (mk_fun None bid_a_typ a_typ (mk_fun None bid_h ty new_hole))
          in
          (* update the proof state accordingly (and close duplicated goal) *)
          let st = assign_meta g.goal_id proof st in
          let st = close_goal g.goal_id st in
          succeed st
      | _ -> fail "Argument must have the type [Exists A p]")
  | None -> fail "No goals remaining"

(** Recursively destructs a term whose type is an And tree into all of its leaves named
    from left to right *)
let destruct_ands (tm : term) (names : string list) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g -> (
      create_metas st.elab_ctx tm (List.map (fun h -> h.bid) g.lctx);
      let tm_ty = infertype st.elab_ctx g.lctx tm in

      (* returns name if leaf, remaining names, reversed final lctx, proof *)
      let rec destruct tm ty names lctx proof :
          string option * string list * local_ctx * term =
        match ty.inner with
        | App ({ inner = App ({ inner = Name "And"; _ }, a); _ }, b) ->
            (* And.elim a_ty b_ty goal_ty (fun a b => proof) tm *)
            let a_bid, b_bid = (gen_binder_id (), gen_binder_id ()) in
            let b_name, names, lctx, proof =
              destruct (mk_bvar b_bid) b names lctx proof
            in
            let a_name, names, lctx, proof =
              destruct (mk_bvar a_bid) a names lctx proof
            in
            let proof =
              mk_app
                (mk_app
                   (mk_app (mk_app (mk_app (mk_name "And.elim") a) b) g.goal_type)
                   (mk_fun a_name a_bid a (mk_fun b_name b_bid b proof)))
                tm
            in
            (None, names, lctx, proof)
        | _ -> (
            match tm.inner with
            | Bvar bid ->
                if names = [] then
                  failwith "destruct_ands: not enough names provided for destructuring"
                else
                  ( Some (List.hd names),
                    List.tl names,
                    { name = Some (List.hd names); bid; ty } :: lctx,
                    proof )
            | _ ->
                failwith
                  "destruct_ands: unreachable; expected to hit leaf node when we hit a \
                   non-And type")
      in

      (* head reduce type once to unfold definitions like eqtri *)
      let tm_ty = Elab.Typecheck.whnf st.elab_ctx tm_ty in
      (* check tm_ty is And *)
      match tm_ty.inner with
      | App ({ inner = App ({ inner = Name "And"; _ }, _); _ }, _) -> (
          let new_goal_id = gen_hole_id () in
          match
            try Ok (destruct tm tm_ty (List.rev names) [] (mk_hole new_goal_id))
            with Failure msg -> Error msg
          with
          | Ok (_, remaining_names, and_lctx, proof) ->
              if remaining_names <> [] then
                fail "destruct_ands: too many names provided for destructuring"
              else
                let goal_lctx = List.rev and_lctx @ g.lctx in
                (* remove tm from context if it's a bvar *)
                let goal_lctx =
                  match tm.inner with
                  | Bvar bid -> List.filter (fun h -> h.bid <> bid) goal_lctx
                  | _ -> goal_lctx
                in
                let st = assign_meta g.goal_id proof st in
                let st = close_goal g.goal_id st in
                let new_goal =
                  { lctx = goal_lctx; goal_type = g.goal_type; goal_id = new_goal_id }
                in
                let st = { st with open_goals = new_goal :: st.open_goals } in
                succeed st
          | Error msg -> fail msg)
      | _ -> fail "destruct_ands: expected a term of type And A B")

(* Infer the type of the distinct_from hypothesis for any of the distinct tactics *)
let infer_distinct (a : term) (h : term) (g : goal) (st : proof_state) :
    term option * term option * term option =
  let pts = gen_hole_id () in
  let ls = gen_hole_id () in
  let cs = gen_hole_id () in
  let expected =
    mk_app_multiarg (mk_name "distinct_from") [ a; mk_hole pts; mk_hole ls; mk_hole cs ]
  in
  create_metas st.elab_ctx h (List.map (fun h -> h.bid) g.lctx);
  let h_typ = Elab.Typecheck.infertype st.elab_ctx g.lctx h in
  let ctx = ctx_with_new_holes g st.elab_ctx expected in
  unify ctx h_typ (Hashtbl.create 0) expected (Hashtbl.create 0);
  match
    ( Hashtbl.find_opt ctx.metas pts,
      Hashtbl.find_opt ctx.metas ls,
      Hashtbl.find_opt ctx.metas cs )
  with
  | Some mvar1, Some mvar2, Some mvar3 -> (mvar1.sol, mvar2.sol, mvar3.sol)
  | _ -> failwith "internal nicegeo programming error: created hole does not exist!"

(* The [distinct_points] tactic takes a [distinct_from] proof as an argument, and from
    it proves an inequality between points and adds it to the hypotheses, asking
    for the [List.mem] proof obligation for now (future versions will probably
    try to prove this automatically when possible). For now this also explicitly
    takes the points that one is saying are not equal, though later it may
    infer these in concrete instances. *)
let distinct_points (name : string) (a : term) (b : term) (h : term) (st : proof_state) =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g -> (
      match infer_distinct a h g st with
      | Some pts, Some ls, Some cs ->
          (* case 2 goal: show original goal, given new inequality hypothesis *)
          let ty = mk_app_multiarg (mk_name "Ne") [ mk_name "Point"; a; b ] in
          let bid = Elab.Term.gen_binder_id () in
          let neq_h = { name = Some name; bid; ty } in
          let goal_pf, st = fresh_goal st (neq_h :: g.lctx) g.goal_type in
          (* case 1 goal: show mem *)
          let new_goal_typ =
            mk_app_multiarg (mk_name "List.mem") [ mk_name "Point"; b; pts ]
          in
          let mem_pf, st = fresh_goal st g.lctx new_goal_typ in
          (* construct the proof term for case 2 *)
          let neq_pf =
            mk_app_multiarg
              (mk_name "distinct_from_pt_neq")
              [ a; b; pts; ls; cs; mem_pf; h ]
          in
          let proof = mk_app (mk_fun (Some name) bid ty goal_pf) neq_pf in
          (* update the proof state accordingly (and close original goal) *)
          let st = assign_meta g.goal_id proof st in
          let st = close_goal g.goal_id st in
          succeed st
      | _ ->
          fail
            (Printf.sprintf
               "The term %s is expected to have type (distinct_from %s pts ls cs) for \
                lists pts, ls, and cs, but we cannot infer instances of pts, ls, and cs"
               (pp_term st.elab_ctx a)
               (pp_term st.elab_ctx h)))

let register () =
  register_tactic "try" Register.(tactical try_tac);
  register_tactic "repeat" Register.(tactical repeat);
  register_tactic "reflexivity" Register.(nullary reflexivity);
  register_tactic "exact" Register.(unary_term exact);
  register_tactic "apply" Register.(unary_term apply);
  register_tactic "sorry" Register.(nullary sorry);
  register_tactic "intro" Register.(unary_ident intro);
  register_tactic "intros" Register.(variadic_ident intros);
  register_tactic "left" Register.(nullary left);
  register_tactic "right" Register.(nullary right);
  register_tactic "cases" (function
    | [ tm; { inner = Name n1; _ }; { inner = Name n2; _ } ] -> cases tm n1 n2
    | [ tm; { inner = Name n1; _ } ] -> cases tm n1 n1
    | tm :: _ ->
        raise
          (Elab.Error.ElabError
             {
               context = { loc = Some tm.loc; decl_name = None; lctx = None };
               error_type =
                 Elab.Error.InvalidTacticParameter
                   "Expected an identifier, but got a term";
             })
    | args ->
        raise
          (Elab.Error.ElabError
             {
               context =
                 {
                   loc =
                     Some
                       {
                         start = (List.hd args).loc.start;
                         end_ = (List.hd (List.rev args)).loc.end_;
                       };
                   decl_name = None;
                   lctx = None;
                 };
               error_type =
                 Elab.Error.InvalidTacticParameter
                   ("Expected two or three parameters, but got "
                   ^ string_of_int (List.length args));
             }));
  register_tactic "split" Register.(nullary split);
  (* There's a clever design somewhere that lets me write this with some combinators, but for time's sake this one gets hard-coded for now. *)
  register_tactic "have" (function
    | [ { inner = Name name; _ }; ty ] -> have name ty
    | ty :: _ ->
        raise
          (Elab.Error.ElabError
             {
               context = { loc = Some ty.loc; decl_name = None; lctx = None };
               error_type =
                 Elab.Error.InvalidTacticParameter
                   "Expected an identifier, but got a term";
             })
    | args ->
        raise
          (Elab.Error.ElabError
             {
               context =
                 {
                   loc =
                     Some
                       {
                         start = (List.hd args).loc.start;
                         end_ = (List.hd (List.rev args)).loc.end_;
                       };
                   decl_name = None;
                   lctx = None;
                 };
               error_type =
                 Elab.Error.InvalidTacticParameter
                   ("Expected exactly two parameters (name and type), but got "
                   ^ string_of_int (List.length args));
             }));
  register_tactic "rewrite" Register.(unary_term rewrite);
  register_tactic "exists" Register.(unary_term exists);
  (* I don't feel comfortable enough with registration yet to extend Register *)
  register_tactic "choose" (function
    | [ { inner = Name n1; _ }; { inner = Name n2; _ }; trm ] -> choose (n1, n2) trm
    | trm :: _ ->
        raise
          (Elab.Error.ElabError
             {
               context = { loc = Some trm.loc; decl_name = None; lctx = None };
               error_type =
                 Elab.Error.InvalidTacticParameter
                   "Expected an identifier, but got a term";
             })
    | args ->
        raise
          (Elab.Error.ElabError
             {
               context =
                 {
                   loc =
                     Some
                       {
                         start = (List.hd args).loc.start;
                         end_ = (List.hd (List.rev args)).loc.end_;
                       };
                   decl_name = None;
                   lctx = None;
                 };
               error_type =
                 Elab.Error.InvalidTacticParameter
                   ("Expected exactly three parameters (two names and a term), but got "
                   ^ string_of_int (List.length args));
             }));
  register_tactic "destruct_ands" (function
    | tm :: names ->
        let names =
          List.map
            (function
              | { inner = Name id; _ } -> id
              | term ->
                  raise
                    (Elab.Error.ElabError
                       {
                         context = { loc = Some term.loc; decl_name = None; lctx = None };
                         error_type =
                           Elab.Error.InvalidTacticParameter
                             "Expected an identifier, but got a term";
                       }))
            names
        in
        destruct_ands tm names
    | [] ->
        (* uhh we don't have access to tactic location here *)
        raise
          (Elab.Error.ElabError
             {
               context = { loc = None; decl_name = None; lctx = None };
               error_type =
                 Elab.Error.InvalidTacticParameter "Expected at least one parameter";
             }));
  register_tactic "distinct_points" (function
    | [ { inner = Name n; _ }; a; b; h ] -> distinct_points n a b h
    | trm :: _ ->
        raise
          (Elab.Error.ElabError
             {
               context = { loc = Some trm.loc; decl_name = None; lctx = None };
               error_type =
                 Elab.Error.InvalidTacticParameter
                   "Expected an identifier, but got a term";
             })
    | args ->
        raise
          (Elab.Error.ElabError
             {
               context =
                 {
                   loc =
                     Some
                       {
                         start = (List.hd args).loc.start;
                         end_ = (List.hd (List.rev args)).loc.end_;
                       };
                   decl_name = None;
                   lctx = None;
                 };
               error_type =
                 Elab.Error.InvalidTacticParameter
                   ("Expected exactly four parameters, but got "
                   ^ string_of_int (List.length args));
             }));
  ()
