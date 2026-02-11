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

let () =
  let env = mk_axioms_env () in

  let local_ctx = Hashtbl.create 16 in
  (* Const "Point" -> Sort 1 *)
  let t1 = inferType env local_ctx (Const "Point") in
  assert (t1 = Sort 1);
  print_endline "Const \"Point\" -> Sort 1: OK";

  (* Bvar 0 with empty stack -> should fail *)
  (try
     ignore (inferType env local_ctx (Bvar 0));
     print_endline "Bvar 0 in []: UNEXPECTED SUCCESS"
   with Failure msg ->
     assert (str_contains msg "out of scope");
     print_endline "Bvar 0 in [] -> expected failure: OK");

  print_endline "\nAll checks passed."
