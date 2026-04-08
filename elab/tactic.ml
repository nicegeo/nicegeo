open Term
open Proofstate

type tactic_result =
  | Success of proof_state
  | Failure of string

type tactic = proof_state -> tactic_result

let tactics : (string, term list -> tactic) Hashtbl.t = Hashtbl.create 8

let bind_tactic_args (st : Proofstate.proof_state) (args : term list) : term list =
  let goal = List.hd st.open_goals in
  List.map (fun arg ->
    List.fold_right (fun hyp res ->
      Term.subst res (Name hyp.hyp_name) (Bvar hyp.hyp_bid)
    ) goal.ctx arg
  ) args

let run (e : Types.ctx) (tacs : Statement.tactic list) (goal : term) : term =
  let init_state = Proofstate.init_state ~elab_ctx:e goal in
  let state =
    List.fold_left
      (fun st (tac : Statement.tactic) ->
        let func_opt = Hashtbl.find_opt tactics tac.name in
        match func_opt with
        | Some func -> (
            (* bind names to Bvars based on the first goal's lctx. probably we actually
            want every tactic to do it themselves rather than hardcoding it here, but this
            is fine for now *)
            let bound_args = bind_tactic_args st tac.args in
            let result = func bound_args st in
            match result with
            | Success new_st -> new_st
            | Failure msg ->
                raise
                  (Error.ElabError
                     {
                       context = { loc = Some tac.loc; decl_name = None };
                       error_type = Error.TacticFailure msg;
                     }))
        | None ->
            raise
              (Error.ElabError
                 {
                   context = { loc = Some tac.loc; decl_name = None };
                   error_type = Error.UnknownName { name = tac.name };
                 }))
      init_state
      tacs
  in
  if state.open_goals <> [] then
    raise
      (Error.ElabError
         {
           context = { loc = Some (List.hd (List.rev tacs)).loc; decl_name = None };
           error_type =
             Error.TacticFailure
               ("Proof terminated with unsolved goals. Remaining goals:\n"
               ^ String.concat
                   "\n"
                   (List.map
                      (fun g -> "  " ^ Pretty.term_to_string e g.goal_type)
                      state.open_goals));
         })
  else state.statement

let register_tactic (name : string) (tac : term list -> tactic) : unit =
  if Hashtbl.mem tactics name then
    failwith (Printf.sprintf "Tactic '%s' is already registered." name)
  else Hashtbl.replace tactics name tac

module Register = struct
  let nullary (f : tactic) : term list -> tactic = function
    | [] -> f
    | terms ->
        raise
          (Error.ElabError
             {
               context =
                 {
                   loc =
                     Some
                       {
                         start = (List.hd terms).loc.start;
                         end_ = (List.hd (List.rev terms)).loc.end_;
                       };
                   decl_name = None;
                 };
               error_type =
                 Error.InvalidTacticParameter
                   ("Expected no parameters, but got " ^ string_of_int (List.length terms));
             })

  let unary_term (f : term -> tactic) : term list -> tactic = function
    | [ arg ] -> f arg
    | terms ->
        raise
          (Error.ElabError
             {
               context =
                 {
                   loc =
                     Some
                       {
                         start = (List.hd terms).loc.start;
                         end_ = (List.hd (List.rev terms)).loc.end_;
                       };
                   decl_name = None;
                 };
               error_type =
                 Error.InvalidTacticParameter
                   ("Expected exactly one term parameter, but got "
                   ^ string_of_int (List.length terms));
             })

  let unary_ident (f : string -> tactic) : term list -> tactic = function
    | [ { inner = Name id; _ } ] -> f id
    | [ term ] ->
        raise
          (Error.ElabError
             {
               context = { loc = Some term.loc; decl_name = None };
               error_type =
                 Error.InvalidTacticParameter "Expected an identifier, but got a term";
             })
    | terms ->
        raise
          (Error.ElabError
             {
               context =
                 {
                   loc =
                     Some
                       {
                         start = (List.hd terms).loc.start;
                         end_ = (List.hd (List.rev terms)).loc.end_;
                       };
                   decl_name = None;
                 };
               error_type =
                 Error.InvalidTacticParameter
                   ("Expected exactly one identifier parameter, but got "
                   ^ string_of_int (List.length terms));
             })

  let variadic_term (f : term list -> tactic) : term list -> tactic = fun args -> f args

  let variadic_ident (f : string list -> tactic) : term list -> tactic =
   fun args ->
    let idents =
      List.map
        (function
          | { inner = Name id; _ } -> id
          | term ->
              raise
                (Error.ElabError
                   {
                     context = { loc = Some term.loc; decl_name = None };
                     error_type =
                       Error.InvalidTacticParameter
                         "Expected an identifier, but got a term";
                   }))
        args
    in
    f idents
end
