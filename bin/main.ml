open Printexc
open Elab
open Automation

let () =
  record_backtrace true;

  if Array.length Sys.argv < 2 then (
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 1);

  let filename = Sys.argv.(1) in
  
  Tactics.register ();

  let env = Elab.Interface.create () in
  (try Elab.Interface.process_env env
   with Error.ElabError info ->
     print_endline ("Internal error while processing env.ncg: " ^ Error.pp_exn env info);
     exit 255);

  let tone = Nice_messages.tone_from_env () in
  let stmts =
    try Elab.Interface.get_all_statements filename
    with Error.ElabError info ->
      print_endline ("Error processing file " ^ filename ^ ": " ^ Error.pp_exn env info);
      (match Nice_messages.pick_message tone Nice_messages.After_error with
      | Some extra -> Printf.printf "\n%s\n\n" extra
      | None -> ());
      exit 1
  in

  let errors_exist =
    List.exists
      (fun stmt ->
        try
          Elab.Interface.process_statement env stmt;
          false
        with Error.ElabError info ->
          print_endline
            ("Error processing file " ^ filename ^ ": " ^ Error.pp_exn env info);
          print_endline "";
          Hashtbl.clear env.lctx;
          true)
      stmts
  in

  if errors_exist then (
    (match Nice_messages.pick_message tone Nice_messages.After_error with
    | Some extra -> Printf.printf "\n%s\n\n" extra
    | None -> ());
    exit 1)
  else print_endline "Valid proofs!"
