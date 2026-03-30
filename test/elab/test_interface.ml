module Error = Elab.Error

let with_temp_file contents f =
  let path, oc = Filename.open_temp_file "nicegeo-interface-" ".txt" in
  output_string oc contents;
  close_out oc;
  Fun.protect
    ~finally:(fun () ->
      try if Sys.file_exists path then Sys.remove path with Sys_error _ -> ())
    (fun () -> f path)

let make_env () = Elab.Interface.create_with_env_path "../../../../synthetic/env.ncg"

let process_file ~contents =
  with_temp_file contents @@ fun path ->
  let env = make_env () in
  Elab.Interface.process_file env path

let test_parse_error () =
  Alcotest.match_raises
    "parse error"
    (function
      | Elab.Error.ElabError { error_type = Elab.Error.ParseError _; _ } -> true
      | _ -> false)
    (fun () -> process_file ~contents:"Theorem bad_parse : Prop := =>")

let test_already_defined () =
  Alcotest.match_raises
    "already defined"
    (function
      | Elab.Error.ElabError { error_type = Elab.Error.AlreadyDefined "dup"; _ } -> true
      | _ -> false)
    (fun () -> process_file ~contents:"Axiom dup : Prop\nAxiom dup : Prop\n")

let test_type_mismatch () =
  Alcotest.match_raises
    "type mismatch"
    (function
      | Elab.Error.ElabError { error_type = Elab.Error.TypeMismatch _; _ } -> true
      | _ -> false)
    (fun () -> process_file ~contents:"Theorem bad_mismatch : Prop := Type\n")

let test_cannot_infer_hole () =
  Alcotest.match_raises
    "cannot infer hole"
    (function
      | Elab.Error.ElabError { error_type = Elab.Error.CannotInferHole; _ } -> true
      | _ -> false)
    (fun () -> process_file ~contents:"Theorem bad_hole : Prop := _\n")

let test_unknown_name () =
  Alcotest.match_raises
    "unknown name"
    (function
      | Elab.Error.ElabError { error_type = Elab.Error.UnknownName { name = "foo" }; _ }
        ->
          true
      | _ -> false)
    (fun () -> process_file ~contents:"Theorem bad_unknown : Prop := foo\n")

let test_function_expected () =
  Alcotest.match_raises
    "function expected"
    (function
      | Elab.Error.ElabError { error_type = Elab.Error.FunctionExpected _; _ } -> true
      | _ -> false)
    (fun () -> process_file ~contents:"Theorem bad_app : Prop := Prop Prop\n")

let test_type_expected () =
  Alcotest.match_raises
    "type expected"
    (function
      | Elab.Error.ElabError { error_type = Elab.Error.TypeExpected _; _ } -> true
      | _ -> false)
    (fun () -> process_file ~contents:"Theorem bad_type : (fun (x : Prop) => x) := Prop")

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
