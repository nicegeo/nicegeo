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

  (* Const "Point" -> Sort 0 *)
  let t1 = inferType env [] (Const "Point") in
  assert (t1 = Sort 0);
  print_endline "Const \"Point\" -> Sort 0: OK";

  (* Fvar "p" (in env) -> Point *)
  let t2 = inferType env [] (Fvar "p") in
  assert (t2 = Const "Point");
  print_endline "Fvar \"p\" -> Point: OK";

  (* Bvar 0 under stack [Point] -> Point *)
  let t3 = inferType env [ Const "Point" ] (Bvar 0) in
  assert (t3 = Const "Point");
  print_endline "Bvar 0 in [Point] -> Point: OK";

  (* Bvar 0 = head, Bvar 1 = second; so [Line; Point] gives Bvar 0->Line, Bvar 1->Point *)
  let t4 = inferType env [ Const "Line"; Const "Point" ] (Bvar 1) in
  assert (t4 = Const "Point");
  print_endline "Bvar 1 in [Line; Point] -> Point: OK";

  (* Fvar "q" not in env -> should fail *)
  (try
     ignore (inferType env [] (Fvar "q"));
     print_endline "Fvar \"q\" (missing): UNEXPECTED SUCCESS"
   with Failure msg ->
     assert (str_contains msg "unknown free variable");
     print_endline "Fvar \"q\" (missing) -> expected failure: OK");

  (* Bvar 0 with empty stack -> should fail *)
  (try
     ignore (inferType env [] (Bvar 0));
     print_endline "Bvar 0 in []: UNEXPECTED SUCCESS"
   with Failure msg ->
     assert (str_contains msg "out of scope");
     print_endline "Bvar 0 in [] -> expected failure: OK");

  print_endline "\nAll checks passed."
