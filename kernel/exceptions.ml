open Term
(* TODO make .mli file, move this to a different folder from kernel *)

(* --- Exception types --- *)

exception TypeError of term (* TODO take other args needed to print *)

(* TODO any display of the error messages will happen in the elaborator, but maybe start here before that to separate the refactor into steps *)
