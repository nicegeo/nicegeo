(** Handling of nice messages (the "nice" in "nicegeo"). *)

(** The different tones that messages can have. *)
type tone =
  | Calm
  | Cheerful
  | Minimal
  | Funny

(** Contexts in which a message may be shown. *)
type context = After_error

(** The default tone to use if no environment variable is set. *)
val default_tone : tone

(** Reads the [NICEGEO_TONE] environment variable to select a tone. Defaults to
    [default_tone] if absent or unrecognised. *)
val tone_from_env : unit -> tone

(** Return all available messages for the given tone and context. *)
val messages_for : tone -> context -> string list

(** Pick a random message for the given tone and context, or [None] if no messages exist.
*)
val pick_message : tone -> context -> string option

(** Adds newlines to a message for output. *)
val format_for_output : string -> string
