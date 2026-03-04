open Term
module KTerm = System_e_kernel.Term

type metavar = {
  ty : term option;
  vartypes : term list; (* types of the free variables in the solution, in order (later entries may have bvars referring to previous entries) *)
  sol : term option; (* solution term, should not contain fvars *)
}

type enventry_data =
  | Theorem of string list (* list of axiom names used *)
  | Axiom

type enventry = {
  name: string;
  ty : term;
  data: enventry_data;
}

type ctx = {
  env : (string, enventry) Hashtbl.t; (* elaboration-level environment that maps from defined names to what those names refer to *)
  kenv : KTerm.environment; (* kernel-level environment (should be kept in sync with env) *)
  
  metas : (int, metavar) Hashtbl.t; (** Mapping from hole IDs to values to fill in for that hole (i.e. values that we solved for during elaboration) *)
  lctx : (int, string option * term) Hashtbl.t; (* local context id of a given free variable to name and type of that variable. *)
}
