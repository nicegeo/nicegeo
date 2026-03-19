open Term
module KTerm = Kernel.Term

(** A metavariable (hole) to be solved during elaboration. *)
type metavar = {
  ty : term option;  (** Expected type of the hole, if already known. *)
  context : int list;
      (** list of binder ids that are in scope when the hole is defined *)
  sol : term option;  (** Solution term once found *)
}

type enventry_data =
  | Theorem of string list (* list of axiom names used *)
  | Axiom

type enventry = {
  name : string;
  ty : term;
  data : enventry_data;
}

type rw_graph = (int, int) Hashtbl.t

type ctx = {
  env : (string, enventry) Hashtbl.t;
      (* elaboration-level environment that maps from defined names to what those names refer to *)
  kenv : KTerm.environment;
      (* kernel-level environment (should be kept in sync with env) *)
  metas : (int, metavar) Hashtbl.t;
      (** Mapping from hole IDs to values to fill in for that hole (i.e. values that we
          solved for during elaboration) *)
  lctx : (int, string option * term) Hashtbl.t; (* graph : rw_graph; *)
}
