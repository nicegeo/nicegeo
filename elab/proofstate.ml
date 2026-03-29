open Term
open Types 

type hyp = {
  hyp_name : string; 
  hyp_bid : int; 
  hyp_def : term option;  (*why is it an option? [needs to handle have x := expr ] *)
  hyp_type : term;
}

type local_ctx = hyp list 

type goal = {
  ctx : local_ctx; 
  goal_type : term; 
  goal_id : int;
}

type proof_state = {
  statement : term; 
  open_goals : goal list; 
  elab_ctx : ctx;  (*more on this*)
}


(* helper functions for constructing terms *)
let mk_term k = { inner = k; loc = dummy_range }

let mk_hole id             = mk_term (Hole id)
let mk_sort n              = mk_term (Sort n)
let mk_name s              = mk_term (Name s)
let mk_bvar bid            = mk_term (Bvar bid)
let mk_app  f x            = mk_term (App (f, x))
let mk_arrow x bid ty ret  = mk_term (Arrow (x, bid, ty, ret))
let mk_fun   x bid ty body = mk_term (Fun  (x, bid, ty, body))

let fresh_id () : int = gen_hole_id ()

let fresh_goal (st : proof_state) (ctx : local_ctx) (ty : term) : term * proof_state = 
  let id = fresh_id () in 
  let hole = mk_hole id in 
  let context = List.map (fun h -> h.hyp_bid) ctx in 
  Hashtbl.replace st.elab_ctx.metas id {ty = Some ty; context; sol = None};
  let g = {ctx; goal_type = ty; goal_id = id} in 
  (hole, {st with open_goals = st.open_goals @ [g]}) 

let close_goal (id : int) (st : proof_state) : proof_state = 
  {st with open_goals = List.filter (fun g -> g.goal_id <> id) st.open_goals}

let assign_meta (id : int) (tm :term) (st : proof_state) : proof_state = 
  let existing = Hashtbl.find_opt st.elab_ctx.metas id in 
  let context = Option.fold ~none:[] ~some:(fun m -> m.context) existing in 
  let ty = Option.bind existing (fun m -> m.ty) in 
  Hashtbl.replace st.elab_ctx.metas id {ty; context; sol = Some tm};
  st 

let current_goal (st : proof_state) : goal option = 
  match st.open_goals with 
  | [] -> None 
  | g :: _ -> Some g 


let is_complete (st : proof_state) : bool = st.open_goals = [] 

let init_state ?(elab_ctx = Interface.create()) (ty : term) : proof_state = 
  let id = fresh_id () in 
  Hashtbl.replace elab_ctx.metas id {ty = Some ty; context = []; sol = None}; 
  let g = {ctx = []; goal_type = ty; goal_id = id} in 
  {statement = mk_hole id; open_goals = [g]; elab_ctx}

(** Apply current meta assignments throughout a term, chasing chains.
    Unsolved holes are left in place. *)
let rec apply_meta (ectx : ctx) (tm : term) : term = 
  match tm.inner with 
  | Hole i ->
      (match Hashtbl.find_opt ectx.metas i with
        |Some {sol = Some t; _} -> apply_meta ectx t
        |_ -> tm
      ) 
  | Fun (x, bid, ty, body) -> 
      mk_term (Fun (x, bid, apply_meta ectx ty, apply_meta ectx body))
  | Arrow (x, bid, ty, ret) -> 
      mk_term (Arrow (x, bid, apply_meta ectx ty, apply_meta ectx ret))
  | App (f, a) -> 
      mk_term (App (apply_meta ectx f, apply_meta ectx a))
  | _ -> tm 











