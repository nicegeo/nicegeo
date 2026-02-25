open Printexc
open E_elab

let () =
  record_backtrace true;

  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 1
  end;
  
  let env = Elab.create_with_env () in

  let filename = Sys.argv.(1) in
  let ic = open_in filename in

  let decls : E_elab.Decl.declaration list = try Elab.parse_decls ic filename with Error.ElabError e -> print_endline ("Error parsing file " ^ filename ^ ": " ^ Error.pp_exn e); exit 1 in

  (* Process proof.txt *)
  let all_decls_good = List.fold_left (fun x decl -> try Elab.process_decl env decl; x with Error.ElabError e -> print_endline ("Error adding declaration " ^   Decl.decl_name decl ^ ": " ^ Error.pp_exn e); false) true decls in
  if not all_decls_good then begin
    print_endline "Error(s) encountered while processing proof file. Exiting.";
    exit 1
  end;
  print_endline "Axioms used in prop1:";
  List.iter print_endline (Elab.list_axioms env "prop1");
  print_endline "Valid proofs!"