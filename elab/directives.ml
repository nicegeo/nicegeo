open Types
open Statement

let process_directive (e : ctx) (dir : directive) : unit =
  match dir with
  | PrintAxioms (prop_name, loc) -> (
      let prefix = "[" ^ Pretty.pp_loc loc ^ "] " in
      match Hashtbl.find_opt e.env prop_name with
      | Some record -> (
          match record.data with
          | Theorem used_axioms ->
              print_endline (prefix ^ "Axioms used in " ^ prop_name ^ ":");
              List.iter print_endline used_axioms
          | Axiom -> print_endline (prefix ^ prop_name ^ " is an axiom itself."))
      | None ->
          print_endline (prefix ^ "Error: Proposition '" ^ prop_name ^ "' not found."))
  | Infer (t, loc) ->
      let prefix = "[" ^ Pretty.pp_loc loc ^ "] " in
      (* infer type *)
      let ty_term = Typecheck.infertype e t in
      (* replace holes *)
      let ty_filled = Typecheck.replace_metas e ty_term in
      Hashtbl.clear e.metas;
      print_endline (prefix ^ "#infer: " ^ Pretty.term_to_string e ty_filled)
  | Check (t, ty, loc) ->
      let prefix = "[" ^ Pretty.pp_loc loc ^ "] " in
      (* process provided type to make sure valid type *)
      Typecheck.check_is_type e ty;
      let ty_filled = Typecheck.replace_metas e ty in
      Hashtbl.clear e.metas;
      (* process term provided *)
      (* call elaborator to check if term matches type *)
      Typecheck.checktype e t ty_filled;
      let _ = Typecheck.replace_metas e t in
      Hashtbl.clear e.metas;

      print_endline
        (prefix ^ "#check successful: Term is well-typed as "
        ^ Pretty.term_to_string e ty_filled)
  | Reduce (t, loc) ->
      let prefix = "[" ^ Pretty.pp_loc loc ^ "] " in
      let reduced_term = Pretty.reduce e t in
      print_endline (prefix ^ "#reduce: " ^ Pretty.term_to_string e reduced_term)
