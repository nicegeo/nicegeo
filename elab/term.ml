type term =
  | Name of string
  | Hole
  | Fun of string * term * term  (* argument name, type, body *)
  | Arrow of string * term * term  (* argument name, type, return type *)
  | App of term * term
  | Sort of int

let axiom_list = [ "Point"; "Line"; "Circle"; "Exist"; "Exists.intro"; "Exists.elim"; "And"; "And.intro"; "And.elim"; "Empty"; "Empty.elim"; "False"; "False.elim"; "Eq"; "Eq.intro"; "Eq.elim"; "Or"; "Or.inl"; "Or.inr"; "Or.elim"; "Len"; "Lt"; "LtTrans"; "LtTricot"; "Zero"; "ZeroLeast"; "Add"; "AddComm"; "AddAssoc"; "AddZero"; "LtAdd"; "Length"; "CenterCircle"; "OnCircle"; "InCircle"; "CirclesInter"; "circle_of_ne"; "circlesinter_of_inside_on_circle"; "inside_circle_of_center"; "PtsOfCirclesinter"; "OnCircleIffLengthE"]

let rec term_to_string (t : term) : string = 
  match t with 
  | Name a -> if List.mem a axiom_list then a ^ ";" else ""
  | Hole -> ""
  | Fun (id, ty, bd) -> 
    if List.mem id axiom_list then id ^ ";" ^ term_to_string ty ^ ";" ^ term_to_string bd ^ ";"
    else term_to_string ty ^ ";" ^ term_to_string bd ^ ";"
  | Arrow (id, ll, rr) -> 
    if List.mem id axiom_list then id ^ ";" ^ term_to_string ll ^ ";" ^ term_to_string rr ^ ";"
    else  term_to_string ll ^ ";" ^ term_to_string rr ^ ";"
  | App (ll, rr) -> term_to_string ll ^ ";" ^ term_to_string rr ^ ";"
  | Sort _ -> ""
