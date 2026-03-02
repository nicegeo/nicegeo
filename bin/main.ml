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

  try Elab.process_file env filename
  with Error.ElabError e -> print_endline ("Error processing file " ^ filename ^ ": " ^ Error.pp_exn env e); exit 1;;
  
  print_endline "Valid proofs!"