(* For constructing elaborator-level terms in tests *)

open E_elab.Term

let l = dummy_range

let name s = {inner=Name s; loc=l}
let bvar n = {inner=Bvar n; loc=l}
let fvar n = {inner=Fvar n; loc=l}
let hole n = {inner=Hole n; loc=l}
let app t1 t2 = {inner=App (t1, t2); loc=l}
(* "named" fun, fun with named argument *)
let nfun arg_name ty body = {inner=Fun (Some arg_name, ty, body); loc=l}
(* "unnamed" fun, fun with no argument name *)
let ufun ty body = {inner=Fun (None, ty, body); loc=l}
let narrow arg_name ty ret = {inner=Arrow (Some arg_name, ty, ret); loc=l}
let uarrow ty ret = {inner=Arrow (None, ty, ret); loc=l}
let sort n = {inner=Sort n; loc=l}

