open Elab.Nice_messages

let test_nice_default_tone_calm () =
  (* OCaml versions vary on [Unix.unsetenv]. Simulate “unset/unknown” by using an unrecognized value. *)
  Unix.putenv "NICEGEO_TONE" "unknown";
  match tone_from_env () with
  | Calm -> ()
  | _ -> Alcotest.fail "Expected Calm when NICEGEO_TONE is unset/unknown"

let test_nice_tone_from_env_cheerful () =
  Unix.putenv "NICEGEO_TONE" "cheerful";
  match tone_from_env () with
  | Cheerful -> ()
  | _ -> Alcotest.fail "Expected Cheerful when NICEGEO_TONE=cheerful"

let test_nice_pick_message_after_error () =
  match pick_message Calm After_error with
  | Some msg when msg <> "" -> ()
  | _ -> Alcotest.fail "Expected a non-empty encouragement message"

let suite =
  let open Alcotest in
  ( "Nice Messages",
    [
      test_case "Default tone" `Quick test_nice_default_tone_calm;
      test_case "Cheerful tone" `Quick test_nice_tone_from_env_cheerful;
      test_case "Pick message after error" `Quick test_nice_pick_message_after_error;
    ] )
