open Alcotest
open Kernel
open Elab.Kernel_pretty

let term : Term.term testable =
  Alcotest.testable
    (fun fmt t -> Format.fprintf fmt "%s" (term_to_string_pretty t))
    (fun t1 t2 -> t1 = t2)

let termDefEq env localCtx : Term.term testable =
  Alcotest.testable
    (fun fmt t -> Format.fprintf fmt "%s" (Elab.Kernel_pretty.term_to_string_pretty t))
    (fun t1 t2 -> Infer.Internals.isDefEq env localCtx t1 t2)
