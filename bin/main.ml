open System_e_kernel
open Term
open Infer

let str_contains s sub =
  let n = String.length sub in
  n = 0
  || let rec loop i =
       i + n <= String.length s
       && (String.sub s i n = sub || loop (i + 1))
     in
     loop 0

let mk_env () =
  let env = Hashtbl.create 16 in
  (* Point : Sort 0 (type) *)
  Hashtbl.add env "Point" (Sort 0);
  (* Line : Sort 0 *)
  Hashtbl.add env "Line" (Sort 0);
  (* Free var p : Point (for testing) *)
  Hashtbl.add env "p" (Const "Point");
  env

let () =
  let env = mk_env () in

  let local_ctx = Hashtbl.create 16 in
  (* Const "Point" -> Sort 0 *)
  let t1 = inferType env local_ctx (Const "Point") in
  assert (t1 = Sort 0);
  print_endline "Const \"Point\" -> Sort 0: OK";

  (* Bvar 0 with empty stack -> should fail *)
  (try
     ignore (inferType env local_ctx (Bvar 0));
     print_endline "Bvar 0 in []: UNEXPECTED SUCCESS"
   with Failure msg ->
     assert (str_contains msg "out of scope");
     print_endline "Bvar 0 in [] -> expected failure: OK");

  print_endline "\nAll checks passed."
