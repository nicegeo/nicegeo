open Term
(* TODO make .mli file, move this to a different folder from kernel *)

(* --- Exception types --- *)

(* TODO revisit arguments later if all needed *)
exception TypeError of environment * localcontext * term

(* TODO any display of the error messages will happen in the elaborator, but maybe start here before that to separate the refactor into steps *)
