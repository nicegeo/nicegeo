(* open System_e_kernel *)
(* open System_e_kernel.Env *)
open Printexc
(* module Elab = E_elab.Elab *)
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

  (* Process proof.txt *)
  let all_decls_good = List.fold_left (fun x decl -> try Elab.process_decl env decl; x with Failure msg -> print_endline ("Error adding declaration " ^ E_elab.Decl.decl_name decl ^ ": " ^ msg); false) true decls in
  if not all_decls_good then begin
    print_endline "Error(s) encountered while processing proof file. Exiting.";
    exit 1
  end;
  print_endline "Axioms used in prop1:";
  List.iter print_endline (Elab.list_axioms env "prop1");
  print_endline "Valid proofs!"