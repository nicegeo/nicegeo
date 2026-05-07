open Elab.Proofstate
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

val mood_of_string : string -> mood option
val string_of_mood : mood -> string
val available_moods : string
val set_default_mood : mood -> unit
val get_default_mood : unit -> mood
val choose_message : ?mood:mood -> tactic_error_category -> string

val nice_failure :
  tactic:string ->
  category:tactic_error_category ->
  ?mood:mood ->
  ?goal:string ->
  ?given:string ->
  ?msg:string ->
  ?details:string list ->
  unit ->
  Elab.Tactic.tactic_result

val simple_failure : string -> tactic_result
val no_goals : string -> tactic_result
val set_error_mood : string -> proof_state -> tactic_result
