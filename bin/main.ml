open Printexc
open E_elab

let () =
  record_backtrace true;

  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 1
  end;
  
  let filename = Sys.argv.(1) in
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  
  let decls : E_elab.Decl.declaration list =
    try
      E_elab.Parser.main E_elab.Lexer.token lexbuf
    with
    | Failure msg ->
        Printf.eprintf "Parsing error: %s\n" msg;
        Printf.eprintf "At offset: %d-%d\n" (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf);
        close_in ic;
        exit 1
    | exn ->
        Printf.eprintf "Parsing exception: %s\n" (Printexc.to_string exn);
        Printf.eprintf "At offset: %d-%d\n" (Lexing.lexeme_start lexbuf) (Lexing.lexeme_end lexbuf);
        close_in ic;
        exit 1
  in

  let env = Elab.create_with_env () in

  let tone = Nice_messages.tone_from_env () in
  let all_decls_good =
    List.fold_left
      (fun ok_so_far decl ->
        try
          Elab.process_decl env decl;
          ok_so_far
        with Failure msg ->
          Printf.printf "Error adding declaration %s: %s\n" (Decl.decl_name decl) msg;
          (match Nice_messages.pick_message tone Nice_messages.After_error with
          | Some extra -> Printf.printf "%s" (Nice_messages.format_for_output extra)
          | None -> ());
          false)
      true decls
  in
  if not all_decls_good then begin
    print_endline "Error(s) encountered while processing proof file. Exiting.";
    exit 1
  end;
  print_endline "Axioms used in prop1:";
  List.iter print_endline (Elab.list_axioms env "prop1");
  print_endline "Valid proofs!"