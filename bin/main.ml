open Printexc
open Elab

let () =
  record_backtrace true;

  if Array.length Sys.argv < 2 then begin
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0);
    exit 1
  end;

  let filename = Sys.argv.(1) in
  let env = Elab.Interface.create_with_env () in
  let tone = Nice_messages.tone_from_env () in
  try
    Elab.Interface.process_file env filename;
    print_endline "Valid proofs!"
  with Error.ElabError e ->
    print_endline ("Error processing file " ^ filename ^ ": " ^ Error.pp_exn env e);
    (match Nice_messages.pick_message tone Nice_messages.After_error with
    | Some extra -> Printf.printf "%s" (Nice_messages.format_for_output extra)
    | None -> ());
    exit 1
