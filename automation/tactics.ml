open Elab.Term
open Elab.Types
open Elab.Proofstate
open Elab.Typecheck
open Elab.Tactic

let succeed st = Success st
let fail msg = Failure msg

(* Used by future tactics that need to catch elaboration errors and return a Failure. *)
let _catch_elab (ectx : ctx) (f : unit -> tactic_result) : tactic_result =
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
      _catch_elab st.elab_ctx (fun () ->
          (* Ask the elaborator what type [tm] actually has. *)
          let inferred_ty = Elab.Typecheck.infertype st.elab_ctx g.lctx tm in
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
                 (pp_term st.elab_ctx g.goal_type)))

(** [apply term st] if [term]'s type is [A -> B] and [B] matches the goal, closes the goal
    and opens a new subgoal for [A]. *)
let apply (tm : term) (st : proof_state) : tactic_result =
  match current_goal st with
  | None -> fail "No goals remaining."
  | Some g -> (
      let subgoal_id = gen_hole_id () in
      let sol = mk_app tm (mk_hole subgoal_id) in
      try
        create_metas st.elab_ctx sol (List.map (fun h -> h.bid) g.lctx);
        let sol_ty = infertype st.elab_ctx g.lctx sol in
        unify st.elab_ctx sol_ty (Hashtbl.create 0) g.goal_type (Hashtbl.create 0);
        (* basically check that all the holes in tm are filled *)
        ignore (replace_metas st.elab_ctx tm);
        match (Hashtbl.find st.elab_ctx.metas subgoal_id).ty with
        | Some subgoal_ty ->
            let subgoal =
              { lctx = g.lctx; goal_type = subgoal_ty; goal_id = subgoal_id }
            in
            let st = { st with open_goals = st.open_goals @ [ subgoal ] } in
            let st = assign_meta g.goal_id sol st in
            let st = close_goal g.goal_id st in
            succeed st
        | None -> fail "subgoal type could not be inferred"
      with Elab.Error.ElabError info -> fail (Elab.Error.pp_exn st.elab_ctx info))

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
      match g.goal_type.inner with
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
      let bid = Elab.Term.gen_binder_id () in
      let cont_ty = mk_arrow (Some name) bid ty g.goal_type in
      let proof_id = fresh_id () in
      let cont_id = fresh_id () in
      let ctx_bids = List.map (fun h -> h.bid) g.lctx in
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
      let proof_goal = { lctx = g.lctx; goal_type = ty; goal_id = proof_id } in
      let cont_goal = { lctx = g.lctx; goal_type = cont_ty; goal_id = cont_id } in
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
      let t_ty = beta_nf st.elab_ctx (infertype st.elab_ctx g.lctx t) in
      let eq_ty, lhs, rhs = destruct_eq st.elab_ctx t_ty in
      let motives = get_rewrite_motives st.elab_ctx g.goal_type eq_ty lhs in
      match motives with
      | p :: _ ->
          let new_goal_ty = mk_app p rhs in
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

(** This adds a hole of the desired type, again using a copy of the hashmap *)
let add_hole (g : goal) (hole_id : int) (ty : term) (ctx : ctx) : ctx =
  let metas = Hashtbl.copy ctx.metas in
  (* TODO: would we ever want to add other variables defined inside the term
  being created (e.g. if we wanted to create `fun x => ?m0` and we wanted to allow
  ?m0 to be able to depend on `x`) *)
  let ctx_bids = List.map (fun h -> h.bid) g.lctx in
  Hashtbl.replace metas hole_id { ty = Some ty; context = ctx_bids; sol = None };
  { ctx with metas }

(** Get the solution term for the hole `hole_id`, or return None if there is no solution
    for the given hole (i.e. unification couldn't find a solution) *)
let get_hole_sol (ctx : ctx) (hole_id : int) : term option =
  match Hashtbl.find_opt ctx.metas hole_id with
  | Some mvar -> mvar.sol
  (* If the hole_id isn't in ctx.metas at all, then that indicates a bug since
  the user should have added the given hole ID into the context when they created
  the hole *)
  | None -> failwith "internal nicegeo programming error: created hole does not exist!"

(** Create a new context with a new hole for each element of hole_types, where hole_types
    contains the required type that the value for that hole needs to have, and `ctx` is
    the starting context that we want to add holes to.

    This function doesn't modify `ctx` itself, instead returning the new context, in
    addition to the list of hole IDs for all of the created holes *)
let ctx_with_new_holes (g : goal) (ctx : ctx) (hole_types : term list) : ctx * int list =
  let hole_ids = List.map (fun _ -> gen_hole_id ()) hole_types in
  let ctx_with_holes_added =
    List.fold_left2
      (* TODO: try implementing this without making a new copy of the hash table
    for each new hole *)
      (fun curr_ctx hole_id hole_type -> add_hole g hole_id hole_type curr_ctx)
      ctx
      hole_ids
      hole_types
  in
  (ctx_with_holes_added, hole_ids)

(** Use unification to both check if a given term `t` matches a certain expected format,
    where the expected format is specified as a term with holes for places where arbitrary
    values are allowed.

    The expected format is specified by the function `create_expected_term`, which takes
    in a list of hole IDs (one hole ID for each hole type in `hole_types`), and returns a
    term `t2` using those hole IDs. This function then solves the equation `t = t2` for
    the values of the created holes, either returning a list of solutions for those hole
    values, or None if unification couldn't find a solution for any of the holes.*)
let match_term_and_solve_holes (g : goal) (ctx : ctx) (hole_types : term list) (t : term)
    (create_expected_term : int list -> term) : term list option =
  let ctx, hole_ids = ctx_with_new_holes g ctx hole_types in
  let expected_term = create_expected_term hole_ids in
  unify ctx t (Hashtbl.create 0) expected_term (Hashtbl.create 0);

  (* TODO: do we want to return a list of options instead so that the user can extract some of the
  hole solutions even when unification couldn't find a solution for all holes? *)
  let all_hole_solutions = List.map (fun hole_id -> get_hole_sol ctx hole_id) hole_ids in
  let holes_with_solutions = List.filter_map (fun x -> x) all_hole_solutions in
  if List.length holes_with_solutions = List.length all_hole_solutions then
    Some holes_with_solutions
  else None

(* 
  This infers the motive p of the existential type when constructing an Exists.intro.
  It uses the type A to construct the expected type, leaving in a hole for the motive.
  It then calls unification with a fresh hole for p, to unify the goal with the type
  Exists A ?p, where ?p : A -> Prop. If successful, it returns Some p, otherwise None.
*)
let infer_motive (exists_type : term) (g : goal) ctx : term option =
  let bid = Elab.Term.gen_binder_id () in
  let hole_type = mk_arrow (Some "A") bid exists_type (mk_sort 0) in

  let create_expected_term hole_ids =
    let hole_id = List.nth hole_ids 0 in
    mk_app (mk_app (mk_name "Exists") exists_type) (mk_hole hole_id)
  in
  let hole_solution_list =
    match_term_and_solve_holes g ctx [ hole_type ] g.goal_type create_expected_term
  in
  match hole_solution_list with
  | Some [ motive_solution ] -> Some motive_solution
  | None -> None
  | _ -> failwith "match_term_and_solve_holes returned a list of the wrong length"

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
          let new_goal_ty = mk_app p a in
          let new_hole, st = fresh_goal st g.lctx new_goal_ty in
          (* construct the proof term *)
          let proof =
            mk_app
              (mk_app (mk_app (mk_app (mk_name "Exists.intro") exists_type) p) a)
              new_hole
          in
          (* update the proof state accordingly *)
          let st = assign_meta g.goal_id proof st in
          let st = close_goal g.goal_id st in
          succeed st
      | None -> fail "Goal must have the form [Exists A p]")
  | None -> fail "No goals remaining"

let register () =
  register_tactic "reflexivity" Register.(nullary reflexivity);
  register_tactic "exact" Register.(unary_term exact);
  register_tactic "apply" Register.(unary_term apply);
  register_tactic "sorry" Register.(nullary sorry);
  register_tactic "intro" Register.(unary_ident intro);
  register_tactic "intros" Register.(variadic_ident intros);
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
  register_tactic "rewrite" Register.(unary_term rewrite)
