open Printexc

let () =
  (* Taken from https://stackoverflow.com/questions/65868770/lack-of-information-when-ocaml-crashes#comment128358969_65873074,
  turns on stack traces *)
  record_backtrace true;

  Alcotest.run "kernel" [ Test_kernel.suite ]
