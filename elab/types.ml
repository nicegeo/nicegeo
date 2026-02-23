open Term
module KTerm = System_e_kernel.Term

type metavar = {
  ty : term option;
  vartypes : term list; (* types of the free variables in the solution, in order *)
  sol : term option; (* solution term, should not contain fvars *)
}

type ctx = {
  env : (string, term) Hashtbl.t; (* elaboration-level environment *)
  kenv : KTerm.environment; (* kernel-level environment (should be kept in sync with env) *)

  metas : (int, metavar) Hashtbl.t; (* mapping from hole IDs to values *)
  lctx : (int, string option * term) Hashtbl.t; (* local context id to name and type. *)
}
