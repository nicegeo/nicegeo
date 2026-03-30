open Term
open Types
open Proofstate 

type tactic_result =
  | Success of proof_state
  | Failure of string

let succeed st  = Success st
let fail    msg = Failure msg 

(* Used by future tactics that need to catch elaboration errors and return a Failure. *)
let _catch_elab (ectx : ctx) (f : unit -> tactic_result) : tactic_result =
  try f ()
  with Error.ElabError info -> Failure (Error.pp_exn ectx info)


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
  let result = f () in
  List.iter (fun h ->
    Hashtbl.remove st.elab_ctx.lctx h.hyp_bid
  ) g.ctx;
  result

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
            fail (Printf.sprintf
              "exact: term has type '%s' but goal is '%s'."
              (pp_term st.elab_ctx inferred_ty)
              (pp_term st.elab_ctx g.goal_type))
        )
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
