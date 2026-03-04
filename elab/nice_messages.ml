type tone =
  | Calm
  | Cheerful
  | Minimal
  | Funny

type context =
  | After_error (* later we can add more: After_success, After_timeout, etc. *)

let default_tone = Calm
let () = Random.self_init ()

let tone_from_env () : tone =
  match Sys.getenv_opt "NICEGEO_TONE" with
  | Some "cheerful" -> Cheerful
  | Some "minimal" -> Minimal
  | Some "funny" -> Funny
  | _ -> default_tone

let messages_for (t : tone) (ctx : context) : string list =
  match (t, ctx) with
  | Calm, After_error ->
      [
        "🌿 Take your time; tricky proofs are normal.";
        "🌙 It’s okay if this step didn’t work yet.";
        "🕯️ Deep thinking takes time—no rush.";
        "🧭 Small steps still move the proof forward.";
        "📌 You can always revisit this step later.";
      ]
  | Cheerful, After_error ->
      [
        "✨ Nice try! Let’s tackle this step together.";
        "🚀 You’re getting closer—keep going!";
        "🧩 Every great proof has a few wrong turns.";
        "💪 This goal is tough, but so are you.";
        "🎯 One more attempt might be the one that works.";
      ]
  | Minimal, After_error ->
      [
        "→ Keep going.";
        "∠ Try another angle.";
        "🔁 Reframe the goal.";
        "⏳ Step back, then try again.";
        "✅ You’ve got this.";
      ]
  | Funny, After_error ->
      [
        "😄 Even Euclid had to backtrack sometimes.";
        "😅 Parallel lines aren’t the only thing that don’t meet first try.";
        "🧠 Proofs are just puzzles that forgot they’re supposed to be fun.";
        "😉 If this were easy, the axioms would be jealous.";
        "🪄 Some lemmas just want extra attention. This might be one of them.";
      ]

let pick_message tone ctx : string option =
  match messages_for tone ctx with
  | [] -> None
  | lst ->
      let len = List.length lst in
      let idx = Random.int len in
      Some (List.nth lst idx)

let format_for_output (msg : string) : string = "\n" ^ msg ^ "\n\n"
