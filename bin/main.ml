open Printexc
open Elab

let () =
  record_backtrace true;

  if Array.length Sys.argv < 2 then (
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 1);

  let filename = Sys.argv.(1) in
  let env = Elab.Interface.create () in
  (try Elab.Interface.process_file env "synthetic/env.ncg"
   with Error.ElabError info ->
     print_endline ("Internal error while processing env.ncg: " ^ Error.pp_exn env info);
     (* Uncomment this to get a stack trace *)
     (* raise exn *)
     exit 255);

  let tone = Nice_messages.tone_from_env () in
  try
    let stmts = Elab.Interface.parse_statements filename in
    let had_errors =
      List.fold_left
        (fun acc stmt ->
          try
            Elab.Interface.process_statement env stmt;
            acc (* If no error, keep the accumulator (error state) unchanged *)
          with Error.ElabError e ->
            print_endline ("Error processing file " ^ filename ^ ": " ^ Error.pp_exn env e);
            true (* If there was an error, set the accumulator to true *))
        false (* Begin by assuming there are no errors *)
        stmts
    in
    if had_errors then (
      (match Nice_messages.pick_message tone Nice_messages.After_error with
      | Some extra -> Printf.printf "%s" (Nice_messages.format_for_output extra)
      | None -> ());
      exit 1)
    else print_endline "Valid proofs!"
  with Error.ElabError e ->
    (* Parse-level errors still abort early because later statements cannot be recovered. *)
    print_endline ("Error processing file " ^ filename ^ ": " ^ Error.pp_exn env e);
    (match Nice_messages.pick_message tone Nice_messages.After_error with
    | Some extra -> Printf.printf "%s" (Nice_messages.format_for_output extra)
    | None -> ());
    exit 1
