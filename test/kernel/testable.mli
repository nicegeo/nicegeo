open Alcotest
open Kernel

val term : Term.term testable
val termDefEq : Interface.environment -> Term.localcontext -> Term.term testable
