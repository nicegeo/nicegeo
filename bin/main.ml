open System_e_kernel
open Infer
open Env

let () =
  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 1
  end;
  
  let filename = Sys.argv.(1) in
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  
  let (claim, proof) = Parser.main Lexer.token lexbuf in
  close_in ic;

  let env = mk_axioms_env () in
  let local_ctx = Hashtbl.create 16 in

  let inferredType = inferType env local_ctx proof in
  let isValidProof = isDefEq env inferredType claim in

  if isValidProof then
    print_endline "Valid proof!"
  else
    print_endline "Invalid proof!"
