open Term
open Types 

type hypo = {
  hypo_name : string;
  hypo_type : term;
}

type local_ctx = hypo list 

type goal = {
  goal_type : term; 
  goal_id : int;
}
type proof_state = {
  l_ctx : local_ctx; 
  elab_ctx : ctx; 
}

type curr_goals = (int, proof_state) Hashtbl.t 

type global_count = int 
let fresh_id (id : global_count) : int * global_count = 
  let new_id = id + 1 in
  (new_id, new_id)