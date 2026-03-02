open Alcotest
open System_e_kernel

let term : Term.term testable =
  Alcotest.testable
    (fun fmt t ->
      Format.fprintf fmt "%s" (E_elab.Kernel_pretty.term_to_string_pretty t))
    (fun t1 t2 -> t1 = t2)

let termDefEq env localCtx : Term.term testable =
  Alcotest.testable
    (fun fmt t ->
      Format.fprintf fmt "%s" (E_elab.Kernel_pretty.term_to_string_pretty t))
    (fun t1 t2 -> Infer.isDefEq env localCtx t1 t2)
