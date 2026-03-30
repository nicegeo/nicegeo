module Error = Elab.Error

let with_temp_file contents f =
  let path, oc = Filename.open_temp_file "nicegeo-interface-" ".txt" in
  output_string oc contents;
  close_out oc;
  Fun.protect
    ~finally:(fun () ->
      try if Sys.file_exists path then Sys.remove path with Sys_error _ -> ())
    (fun () -> f path)

let error_type_tag = function
  | Error.ParseError _ -> "ParseError"
  | Error.AlreadyDefined _ -> "AlreadyDefined"
  | Error.TypeMismatch _ -> "TypeMismatch"
  | Error.CannotInferHole -> "CannotInferHole"
  | Error.KernelError _ -> "KernelError"
  | Error.UnknownName _ -> "UnknownName"
  | Error.InternalError _ -> "InternalError"
  | Error.FunctionExpected _ -> "FunctionExpected"
  | Error.TypeExpected _ -> "TypeExpected"
  | Error.UnificationFailure _ -> "UnificationFailure"

let fail_expected name =
  Alcotest.fail ("Expected Error.ElabError in " ^ name ^ ", but succeeded")

let make_env () = Elab.Interface.create_with_env_path "../../../../synthetic/env.ncg"

let check_process_file_error ~name ~contents ~expect =
  with_temp_file contents @@ fun path ->
  let env = make_env () in
  match Elab.Interface.process_file env path with
  | () -> fail_expected name
  | exception Error.ElabError { error_type; _ } ->
      Printf.printf "Actual error for %s: %s\n%!" name (error_type_tag error_type);
      expect error_type

let check_interface_error ~name ~contents ~action ~expect =
  with_temp_file contents @@ fun path ->
  let env = make_env () in
  Elab.Interface.process_file env path;
  match action env with
  | () -> fail_expected name
  | exception Error.ElabError { error_type; _ } ->
      Printf.printf "Actual error for %s: %s\n%!" name (error_type_tag error_type);
      expect error_type

let expect_parse_error = function
  | Elab.Error.ParseError _ -> ()
  | _ -> Alcotest.fail "Expected ParseError"

let expect_already_defined expected_name = function
  | Elab.Error.AlreadyDefined name ->
      Alcotest.(check string) "already defined name" expected_name name
  | _ -> Alcotest.fail "Expected AlreadyDefined"

let expect_type_mismatch = function
  | Elab.Error.TypeMismatch _ -> ()
  | _ -> Alcotest.fail "Expected TypeMismatch"

let expect_cannot_infer_hole = function
  | Elab.Error.CannotInferHole -> ()
  | _ -> Alcotest.fail "Expected CannotInferHole"

let expect_unknown_name expected_name = function
  | Elab.Error.UnknownName { name } ->
      Alcotest.(check string) "unknown name" expected_name name
  | _ -> Alcotest.fail "Expected UnknownName"

let expect_function_expected = function
  | Elab.Error.FunctionExpected _ -> ()
  | _ -> Alcotest.fail "Expected FunctionExpected"

let expect_type_expected = function
  | Elab.Error.TypeExpected _ -> ()
  | _ -> Alcotest.fail "Expected TypeExpected"

let expect_unification_failure = function
  | Elab.Error.UnificationFailure _ -> ()
  | _ -> Alcotest.fail "Expected UnificationFailure"

let test_parse_error () =
  check_process_file_error
    ~name:"parse error"
    ~contents:"Theorem bad_parse : Prop := =>"
    ~expect:expect_parse_error

let test_already_defined () =
  check_process_file_error
    ~name:"already defined"
    ~contents:"Axiom dup : Prop\nAxiom dup : Prop\n"
    ~expect:(expect_already_defined "dup")

let test_type_mismatch () =
  check_process_file_error
    ~name:"type mismatch"
    ~contents:"Theorem bad_mismatch : Prop := Type\n"
    ~expect:expect_type_mismatch

let test_cannot_infer_hole () =
  check_process_file_error
    ~name:"cannot infer hole"
    ~contents:"Theorem bad_hole : Prop := _\n"
    ~expect:expect_cannot_infer_hole

let test_unknown_name () =
  check_process_file_error
    ~name:"unknown name"
    ~contents:"Theorem bad_unknown : Prop := foo\n"
    ~expect:(expect_unknown_name "foo")

let test_function_expected () =
  check_process_file_error
    ~name:"function expected"
    ~contents:"Theorem bad_app : Prop := Prop Prop\n"
    ~expect:expect_function_expected

let test_type_expected () =
  check_process_file_error
    ~name:"type expected"
    ~contents:"Theorem bad_type : (fun (x : Prop) => x) := Prop\n"
    ~expect:expect_type_expected

let test_valid_file () =
  with_temp_file "Axiom p : Prop\nTheorem good : Prop := p\n" @@ fun path ->
  let env = make_env () in
  Elab.Interface.process_file env path

let suite =
  let open Alcotest in
  ( "Interface",
    [
      test_case "parse error" `Quick test_parse_error;
      test_case "already defined" `Quick test_already_defined;
      test_case "cannot infer hole" `Quick test_cannot_infer_hole;
      test_case "unknown name" `Quick test_unknown_name;
      test_case "function expected" `Quick test_function_expected;
      test_case "type expected" `Quick test_type_expected;
      test_case "valid file" `Quick test_valid_file;
    ] )
