open Term
open Decl

(* Create an expression where func is applied to all arguments in order *)
(* Ex: f a b c -> App(App (App (f, a), b), c) *)
let application_multiple_arguments (func: term) (args: term list): term = 
  List.fold_left
    (fun application_so_far first_arg -> App (application_so_far, first_arg))
    func
    args

let mk_axioms_env () =
  let env = Hashtbl.create 16 in

  let envFilename = "./kernel/env.txt" in
  let env_ic = open_in envFilename in
  let env_lexbuf = Lexing.from_channel env_ic in
  
  let env_decls : declaration list = 
    try
      Parser.main Lexer.token env_lexbuf 
    with 
    | Failure msg ->
        Printf.eprintf "Parsing error in env.txt: %s\n" msg;
        Printf.eprintf "At offset: %d-%d\n" (Lexing.lexeme_start env_lexbuf) (Lexing.lexeme_end env_lexbuf);
        close_in env_ic;
        exit 1
    | exn ->
        Printf.eprintf "Parsing exception in env.txt: %s\n" (Printexc.to_string exn);
        Printf.eprintf "At offset: %d-%d\n" (Lexing.lexeme_start env_lexbuf) (Lexing.lexeme_end env_lexbuf);
        close_in env_ic;
        exit 1
  in
  close_in env_ic;
  let all_decls_good = List.fold_left (fun x decl -> try addDeclaration decl env; x with Failure msg -> print_endline ("Error adding declaration: " ^ msg); false) true env_decls in
  if not all_decls_good then begin
    print_endline "Error(s) encountered while processing env.txt. Exiting.";
    exit 1
  end;

  env