open Types
open Statement

let process_directive (e : ctx) (dir : directive) : unit =
  match dir with
  | PrintAxioms (prop_name, loc) -> (
      let prefix = "[" ^ Pretty.pp_loc loc ^ "] " in
      match Hashtbl.find_opt e.env prop_name with
      | Some record -> (
          match record.data with
          | Theorem used_axioms | Def (used_axioms, _, _) ->
              print_endline (prefix ^ "Axioms used in " ^ prop_name ^ ":");
              List.iter print_endline used_axioms
          | Axiom -> print_endline (prefix ^ prop_name ^ " is an axiom itself."))
      | None ->
          print_endline (prefix ^ "Error: Proposition '" ^ prop_name ^ "' not found."))
  | Infer (t, loc) ->
      let prefix = "[" ^ Pretty.pp_loc loc ^ "] " in
      (* infer type *)
      let t = Typecheck.elaborate e t None in
      let t_delta = Reduce.delta_reduce e t in
      let ty_term = Typecheck.infertype e [] t_delta in
      print_endline (prefix ^ "#infer: " ^ Pretty.term_to_string e ty_term)
  | Check (t, ty, loc) ->
      let prefix = "[" ^ Pretty.pp_loc loc ^ "] " in
      (* process provided type to make sure valid type *)
      let ty_filled = Typecheck.elaborate e ty None in
      ignore (Typecheck.elaborate e t (Some ty_filled));

      print_endline
        (prefix ^ "#check successful: Term is well-typed as "
        ^ Pretty.term_to_string e ty_filled)
  | Reduce (t, loc) ->
      let prefix = "[" ^ Pretty.pp_loc loc ^ "] " in
      let t = Typecheck.elaborate e t None in
      let reduced_term = Reduce.reduce e t in
      print_endline (prefix ^ "#reduce: " ^ Pretty.term_to_string e reduced_term)
  | Opaque (name, loc) -> (
      match Hashtbl.find_opt e.env name with
      | Some record -> (
          match record.data with
          | Def (axioms, body, false) ->
              Hashtbl.replace e.env name { record with data = Def (axioms, body, true) }
          | Def (_, _, true) ->
              print_endline
                ("[" ^ Pretty.pp_loc loc ^ "] Warning: '" ^ name ^ "' is already opaque.")
          | _ ->
              print_endline
                ("[" ^ Pretty.pp_loc loc ^ "] Error: '" ^ name
               ^ "' exists but is not a definition."))
      | None ->
          print_endline
            ("[" ^ Pretty.pp_loc loc ^ "] Error: Definition '" ^ name ^ "' not found."))
