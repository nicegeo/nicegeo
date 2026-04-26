
open Z3
open Elab.Term
open Kernel.Term



let rec transform_Elab_term_to_z3 (t : Elab.Term.term) (ctx : Z3.context) : Z3.Expr.expr =
  match t.inner with
  | Name s ->
    if s = "true" then Z3.Boolean.mk_true ctx
    else if s = "false" then Z3.Boolean.mk_false ctx
    else
      (* Create an uninterpreted boolean constant for unknown names *)
      let sym = Z3.Symbol.mk_string ctx s in
      Z3.Expr.mk_const ctx sym (Z3.Boolean.mk_sort ctx)
  | Bvar _ ->
      raise (Failure "Cannot transform term with bound variable to Z3 expression")
  | Hole _ ->
      raise (Failure "There should be no holes in the term when transforming to Z3 expression")
  | Fun _ ->
      raise (Failure "Cannot transform function term to Z3 expression")
  | Arrow _ ->
      raise (Failure "Cannot transform arrow term to Z3 expression")
  | App (f, arg) ->
      let z3_f = transform_Elab_term_to_z3 f ctx in
      let z3_arg = transform_Elab_term_to_z3 arg ctx in
      (* z3_f must be an application of a FuncDecl — extract and apply it *)
      let func_decl = Z3.Expr.get_func_decl z3_f in
      Z3.Expr.mk_app ctx func_decl [z3_arg]
  | Sort _ ->
      raise (Failure "Cannot transform sort term to Z3 expression")


let rec transform_Elab_ctx_to_z3 (ectx : Elab.Types.ctx) (ctx : Z3.context) : (Z3.Expr.expr) list =
  raise(Failure "Not implemented yet: transforming Elab context to Z3 expressions")


let create_solver (ectx : Elab.Types.ctx) : Z3.context * Z3.Solver.solver =
  let z3_ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_solver z3_ctx None in
  let assumptions = transform_Elab_ctx_to_z3 ectx z3_ctx in
  List.iter (fun a -> Z3.Solver.add solver [a]) assumptions;
  (z3_ctx, solver)


let solve_goal (st : Elab.Proofstate.proof_state) : bool =
  match Elab.Proofstate.current_goal st with
  | None -> true
  | Some goal ->
      let (z3_ctx, solver) = create_solver st.elab_ctx in
      let z3_goal = Z3.Boolean.mk_not z3_ctx (transform_Elab_term_to_z3 goal.goal_type z3_ctx) in
      Z3.Solver.add solver [z3_goal];
      match Z3.Solver.check solver [] with
      | Z3.Solver.SATISFIABLE -> false
      | Z3.Solver.UNSATISFIABLE -> true
      | Z3.Solver.UNKNOWN -> raise (Failure "Z3 returned UNKNOWN when solving the goal")






