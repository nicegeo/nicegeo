open System_e_kernel
open Decl
open Env
open Printexc

let getEnv =
  let env = mk_axioms_env () in

  (* Add the axioms in env.txt *)
  let envFilename = "lib/env.txt" in
  let env_ic = open_in envFilename in
  let env_lexbuf = Lexing.from_channel env_ic in
  
  let env_decls : declaration list = Parser.main Lexer.token env_lexbuf in
  close_in env_ic;
  let all_decls_good = List.fold_left (fun x decl -> try addDeclaration decl env; x with Failure msg -> print_endline ("Error adding declaration: " ^ msg); false) true env_decls in
  if not all_decls_good then begin
    print_endline "Error(s) encountered while processing env.txt. Exiting.";
    exit 1
  end;

  env

let () =
  record_backtrace true;

  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 1
  end;
  
  let filename = Sys.argv.(1) in
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  
  let decls : declaration list = Parser.main Lexer.token lexbuf in
  close_in ic;

  let env = getEnv in

  (* Process proof.txt *)
  List.fold_left (fun _ decl -> addDeclaration decl env) () decls;
  print_endline "Valid proofs!"