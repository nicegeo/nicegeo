open Elab.Tactic


type mood =
  | Calm
  | Cheerful
  | Minimal
  | Funny

type tactic_error_category =
  | ReflexivityNotDefeq
  | ExactFailed
  | ApplyUnificationFailed
  | NoGoalsLeft
  | IntroExpectedArrow
  | SplitExpectedAnd
  | LeftRightExpectedOr
  | RewriteFailed
  | ExistsExpected
  | ChooseExpected
  | DestructExpectedAnd
  | CustomFailure of string

type nice_message = {
  text : string;
  mood : mood;
}
let mood_names = [ "calm"; "cheerful"; "minimal"; "funny" ]
let available_moods = String.concat ", " mood_names


let mood_of_string s =
  match String.lowercase_ascii s with
  | "calm" -> Some Calm
  | "cheerful" -> Some Cheerful
  | "minimal" -> Some Minimal
  | "funny" -> Some Funny
  | _ -> None

let string_of_mood = function
  | Calm -> "calm"
  | Cheerful -> "cheerful"
  | Minimal -> "minimal"
  | Funny -> "funny"

let default_mood : mood ref =
  ref
    (match Sys.getenv_opt "NICEGEO_TACTIC_MOOD" with
    | Some s -> Option.value (mood_of_string s) ~default:Minimal
    | None -> Minimal)

let set_default_mood mood = default_mood := mood
let get_default_mood () = !default_mood

let () = Random.self_init ()

let messages_for = function
  | ReflexivityNotDefeq ->
      [
        { text = "Hey, they looked definitionally equal to me too, no stress."; mood = Calm };
        { text = "The two sides are not definitionally equal."; mood = Minimal };
        { text = "Reflexivity stared very hard, but the two sides did not blink."; mood = Funny };
      ]
  | ExactFailed ->
      [
        { text = "Writing terms is an exacting task, you can do this!"; mood = Funny };
        { text = "The provided term does not solve the current goal."; mood = Minimal };
        { text = "This term is close, but it does not match the goal yet."; mood = Calm };
      ]
  | ApplyUnificationFailed ->
      [
        { text = "You are great at applying yourself, keep going!"; mood = Funny };
        { text = "The theorem could not be applied to the current goal."; mood = Minimal };
        { text = "This does not line up with the goal yet, but the idea may still be useful."; mood = Calm };
      ]
(* Removing the messages for NoGoalsLeft to make compatible with current test strutures *)
  | NoGoalsLeft ->
      [
        { text = ""; mood = Cheerful };
        { text = ""; mood = Cheerful };
        { text = ""; mood = Minimal };
      ]
  | IntroExpectedArrow ->
      [
        { text = "intro needs the goal to be an implication or forall."; mood = Minimal };
        { text = "Nothing to introduce here yet."; mood = Calm };
        { text = "intro reached for a hypothesis, but the goal had no handle."; mood = Funny };
      ]
  | SplitExpectedAnd ->
      [
        { text = "split needs the goal to be a conjunction."; mood = Minimal };
        { text = "This goal is not made of two parts yet."; mood = Calm };
        { text = "split brought scissors, but this goal is not an And."; mood = Funny };
      ]
  | LeftRightExpectedOr ->
      [
        { text = "left/right need the goal to be a disjunction."; mood = Minimal };
        { text = "This goal does not have left and right branches."; mood = Calm };
        { text = "No fork in the road here: the goal is not an Or."; mood = Funny };
      ]
  | RewriteFailed ->
      [
        { text = "rewrite could not find the left-hand side in the goal."; mood = Minimal };
        { text = "The equality is valid, but I could not find where to use it."; mood = Calm };
        { text = "rewrite looked everywhere and came back empty-handed."; mood = Funny };
      ]
  | ExistsExpected ->
      [
        { text = "exists needs the goal to be existential."; mood = Minimal };
        { text = "This goal is not asking for a witness yet."; mood = Calm };
      ]
  | ChooseExpected ->
      [
        { text = "choose needs an argument whose type is existential."; mood = Minimal };
        { text = "I could not unpack this as an existential statement."; mood = Calm };
      ]
  | DestructExpectedAnd ->
      [
        { text = "destruct_ands needs a term whose type is a conjunction."; mood = Minimal };
        { text = "I could not break this term into And-components."; mood = Calm };
      ]
  | CustomFailure msg ->
      [
        { text = msg; mood = Minimal };
        { text = msg; mood = Calm };
        { text = msg; mood = Cheerful };
        { text = msg; mood = Funny };
      ]

let choose_message ?(mood = !default_mood) category =
  let msgs = messages_for category in
  let matching = List.filter (fun m -> m.mood = mood) msgs in
  let pool = if matching = [] then msgs else matching in
  match pool with
  | [] -> "The tactic failed."
  | _ -> (List.nth pool (Random.int (List.length pool))).text

let bullet_lines xs =
  xs |> List.map (fun s -> "  - " ^ s) |> String.concat "\n"

let nice_failure ~(tactic : string) ~(category : tactic_error_category)
    ?mood ?goal ?given ?msg ?(details = []) () : tactic_result =
  let mood = Option.value mood ~default:!default_mood in
    let base_message =
    match msg with
    | Some m -> m
    | None -> choose_message ~mood category
    in  
    let parts =
    [
    Some
      (match category with
      | NoGoalsLeft ->
          Printf.sprintf
            "%s%s"
            base_message
            (" " ^ choose_message ~mood category)
      | _ ->
          Printf.sprintf "%s failed: %s" tactic base_message);
      Option.map (fun g -> "Goal:\n  " ^ g) goal;
      Option.map (fun x -> "Given:\n  " ^ x) given;
      if details = [] then None else Some ("Details:\n" ^ bullet_lines details);
    ]
  in
  Failure (String.concat "\n" (List.filter_map Fun.id parts))

let simple_failure msg =
  nice_failure ~tactic:"tactic" ~category:(CustomFailure msg) ()

let no_goals tactic =
  nice_failure
    ~tactic
    ~category:NoGoalsLeft
    ~msg:"No goals remaining."
    ()


let set_error_mood name st =
  match mood_of_string name with
  | Some mood ->
      set_default_mood mood;
      Success st
  | None ->
      Failure
        ("unknown mood: " ^ name ^ "\navailable moods: " ^ available_moods)