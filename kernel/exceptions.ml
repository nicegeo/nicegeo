open Term
(* TODO make .mli file, document this file, etc *)

(* --- Exception types --- *)

type type_error_kind =
  | ForallSortError of term * term

type type_error_info =
  {
    env : environment;
    ctx : localcontext;
    trm : term;
    err_kind : type_error_kind
  }

(* TODO revisit arguments later if all needed *)
exception TypeError of type_error_info

(* --- Printing errors ---*)

(* TODO any display of the error messages will happen in the elaborator, but will start here to divide work into steps. this is taken directly from the old printing code in infer.ml but I am using it to preserve old behavior while also figuring out what printing info is needed in the type_error_info *)

let rec term_to_string (t : term) : string =
  match t with
  | Const name -> name
  | Sort level -> "Sort " ^ string_of_int level
  | Fvar name -> name
  | Bvar idx -> "Bvar " ^ string_of_int idx
  | Lam (dom, body) -> "fun " ^ term_to_string dom ^ " => (" ^ term_to_string body ^ ")"
  | Forall (dom, body) -> term_to_string dom ^ " -> " ^ term_to_string body
  | App (f, a) -> "(" ^ term_to_string f ^ " " ^ term_to_string a ^ ")"

let context_to_string (ctx : localcontext) : string =
  Hashtbl.fold (fun k v acc -> acc ^ k ^ " : " ^ term_to_string v ^ "\n") ctx ""

let err_to_string (info : type_error_info) : string =
  match info.err_kind with
  | ForallSortError (domainTypeType, returnTypeType) ->
      Printf.sprintf 
       "Domain and return types of a Forall must be sorts.\n\
        Local Context:\n%s\n\
        Term: %s\n\
        Domain Type Sort: %s\n\
        Return Type Sort: %s\n\n"
       (context_to_string info.ctx)
       (term_to_string info.trm)
       (term_to_string domainTypeType)
       (term_to_string returnTypeType)
