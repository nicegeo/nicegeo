open Alcotest
open Kernel

val term : Term.term testable
val termDefEq : Term.environment -> Term.localcontext -> Term.term testable
