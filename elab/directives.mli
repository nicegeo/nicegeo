(** Execution of elaborator directives (e.g. #print axioms, #infer). *)

(** [process_directive ctx dir] executes [dir] against [ctx] and prints the result to
    stdout.

    - [PrintAxioms(name, loc)] prints the axioms transitively used by theorem [name].
    - [Infer(t, loc)] infers and prints the type of term [t].
    - [Check(t, ty, loc)] checks that [t] has type [ty] and prints a success message.
    - [Reduce(t, loc)] beta-reduces [t] and prints the result. *)
val process_directive : Types.ctx -> Statement.directive -> unit
