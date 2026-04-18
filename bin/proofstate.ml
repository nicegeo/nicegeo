open Elab
open Printexc

type context_item = {
  name : string;
  ty : string;
}

type env_item = {
  env_name : string;
  env_kind : string;
  env_ty : string;
}

type meta_item = {
  meta_id : int;
  meta_ty : string option;
  meta_sol : string option;
  meta_context : int list;
}

type tactic_step_item = {
  step_index : int;
  step_name : string;
  step_args : string list;
  step_goal_before : string option;
  step_goals_after : string list;
  step_status : string;
  step_at_cursor : bool;
}

type proofstate_snapshot = {
  decl_name : string;
  decl_kind : string;
  decl_file : string;
  decl_start_line : int;
  decl_start_col : int;
  decl_end_line : int;
  decl_end_col : int;
  goal_type : string;
  goal_type_reduced : string;
  head_context : context_item list;
  term_context : context_item list;
  hyps : (string * int * string) list;
  environment : env_item list;
  metas : meta_item list;
  tactic_steps : tactic_step_item list;
  tactics_applied : int;
  open_goal_types : string list;
}

let usage_standalone (prog : string) : unit =
  Printf.eprintf "Usage:\n  %s [--json] <filename> <line> <col>\n" prog

let parse_args (args : string list) : (bool * string * int * int) option =
  let use_json, rest = List.partition (fun s -> s = "--json") args in
  let json = use_json <> [] in
  match rest with
  | [ filename; line_s; col_s ] -> (
      try Some (json, filename, int_of_string line_s, int_of_string col_s)
      with Failure _ -> None)
  | _ -> None

let json_escape (s : string) : string = String.escaped s
let pos_col (p : Lexing.position) : int = p.pos_cnum - p.pos_bol + 1

let pos_lex_lt (line_a : int) (col_a : int) (line_b : int) (col_b : int) : bool =
  line_a < line_b || (line_a = line_b && col_a < col_b)

let tac_ends_before_or_at_cursor (tac : Statement.tactic) (line : int) (col : int) : bool
    =
  let e = tac.loc.end_ in
  pos_lex_lt e.pos_lnum (pos_col e) line col || (e.pos_lnum = line && pos_col e = col)

let cursor_strictly_after_range_end (r : Term.range) (line : int) (col : int) : bool =
  let e = r.end_ in
  pos_lex_lt e.pos_lnum (pos_col e) line col

let tactics_prefix_from_tactics_only (tacs : Statement.tactic list) (line : int)
    (col : int) : int =
  let rec go n = function
    | [] -> n
    | tac :: rest ->
        if tac_ends_before_or_at_cursor tac line col then go (n + 1) rest else n
  in
  go 0 tacs

let decl_kind_to_string (k : Statement.decl_type) : string =
  match k with
  | Statement.Theorem _ -> "theorem"
  | Statement.Axiom -> "axiom"
  | Statement.Def _ -> "definition"

let decl_end_loc (d : Statement.declaration) : Lexing.position =
  match d.kind with
  | Statement.Theorem body -> (
      match body with
      | Statement.DefEq tm -> tm.loc.end_
      | Statement.Proof ps -> ps.qed_loc.end_)
  | Statement.Def body -> body.loc.end_
  | Statement.Axiom -> d.ty.loc.end_

let same_file (a : string) (b : string) : bool =
  a = b || Filename.basename a = Filename.basename b

let range_contains (r : Term.range) (line : int) (col : int) : bool =
  let s_line = r.start.pos_lnum in
  let e_line = r.end_.pos_lnum in
  let s_col = pos_col r.start in
  let e_col = pos_col r.end_ in
  if line < s_line || line > e_line then false
  else if s_line = e_line then col >= s_col && col <= e_col
  else if line = s_line then col >= s_col
  else if line = e_line then col <= e_col
  else true

(** Cursor on [Qed] or after it runs the full script; otherwise count tactics fully before
    cursor. *)
let tactics_prefix_count (ps : Statement.proof_script) (line : int) (col : int) : int =
  let n = List.length ps.tactics in
  if
    range_contains ps.qed_loc line col
    || cursor_strictly_after_range_end ps.qed_loc line col
  then n
  else tactics_prefix_from_tactics_only ps.tactics line col

let find_repo_root (start_path : string) : string option =
  let rec go dir =
    let candidate = Filename.concat dir "dune-project" in
    if Sys.file_exists candidate then Some dir
    else
      let parent = Filename.dirname dir in
      if parent = dir then None else go parent
  in
  go (Filename.dirname start_path)

let load_default_env_for_paths (reference_file : string) : Types.ctx =
  let env = Elab.Interface.create () in
  (try
     match find_repo_root reference_file with
     | Some root ->
         Elab.Interface.process_file env (Filename.concat root "synthetic/env.ncg")
     | None -> Elab.Interface.process_env env
   with Error.ElabError info ->
     print_endline ("Internal error while processing env.ncg: " ^ Error.pp_exn env info);
     exit 255);
  env

let extract_head_binders (ectx : Types.ctx) (ty : Term.term) : (string * string) list =
  let rec go acc lctx (t : Term.term) =
    match t.inner with
    | Term.Arrow (arg_name_opt, bid, ty_arg, ty_ret) ->
        (* Hashtbl.replace ectx.lctx bid (arg_name_opt, ty_arg); *)
        let lctx = Types.{ bid; ty = ty_arg; name = arg_name_opt } :: lctx in
        let name = match arg_name_opt with Some s -> s | None -> "_" in
        let ty_str = Pretty.term_to_string ectx ~lctx ty_arg in
        go (acc @ [ (name, ty_str) ]) lctx ty_ret
    | _ -> acc
  in
  go [] [] ty

let snapshot_environment (e : Types.ctx) : env_item list =
  Hashtbl.fold
    (fun name (entry : Types.enventry) acc ->
      let kind =
        match entry.data with
        | Types.Axiom -> "axiom"
        | Types.Theorem _ -> "theorem"
        | Types.Def _ -> "definition"
      in
      let ty_str = Pretty.term_to_string e entry.ty in
      { env_name = name; env_kind = kind; env_ty = ty_str } :: acc)
    e.env
    []
  |> List.sort (fun a b -> String.compare a.env_name b.env_name)

let snapshot_metas ?(lctx : Types.local_ctx = []) (e : Types.ctx) : meta_item list =
  Hashtbl.fold
    (fun mid (m : Types.metavar) acc ->
      let ty_s =
        match m.ty with Some t -> Some (Pretty.term_to_string e ~lctx t) | None -> None
      in
      let sol_s =
        match m.sol with Some t -> Some (Pretty.term_to_string e ~lctx t) | None -> None
      in
      { meta_id = mid; meta_ty = ty_s; meta_sol = sol_s; meta_context = m.context } :: acc)
    e.metas
    []
  |> List.sort (fun a b -> compare a.meta_id b.meta_id)

let pp_goal_type (e : Types.ctx) (g : Proofstate.goal) : string =
  Pretty.term_to_string e ~lctx:g.lctx g.goal_type

let snapshot_tactic_steps (e : Types.ctx) (goal_ty_tm : Term.term)
    (tacs : Statement.tactic list) (line : int) (col : int) : tactic_step_item list =
  let e = { e with metas = Hashtbl.copy e.metas } in
  let init_state = Proofstate.init_state ~elab_ctx:e goal_ty_tm in
  let rec loop idx (st : Proofstate.proof_state) acc (remaining : Statement.tactic list) =
    match remaining with
    | [] -> List.rev acc
    | (tac : Statement.tactic) :: rest -> (
        let goal_before =
          Option.map (pp_goal_type st.elab_ctx) (Proofstate.current_goal st)
        in
        let lctx_for_args =
          match Proofstate.current_goal st with Some g -> g.lctx | None -> []
        in
        let at_cursor = range_contains tac.loc line col in
        let args_pp =
          List.map (Pretty.term_to_string st.elab_ctx ~lctx:lctx_for_args) tac.args
        in
        let mk_step status (next_state : Proofstate.proof_state) =
          {
            step_index = idx;
            step_name = tac.name;
            step_args = args_pp;
            step_goal_before = goal_before;
            step_goals_after =
              List.map (pp_goal_type next_state.elab_ctx) next_state.open_goals;
            step_status = status;
            step_at_cursor = at_cursor;
          }
        in
        match Tactic.apply_tactic_step st tac with
        | Tactic.Tactic_step_unknown ->
            let step = mk_step "unknown tactic" st in
            List.rev (step :: acc)
        | Tactic.Tactic_step_failed msg ->
            let step = mk_step ("failure: " ^ msg) st in
            List.rev (step :: acc)
        | Tactic.Tactic_step_ok new_st ->
            let step = mk_step "ok" new_st in
            loop (idx + 1) new_st (step :: acc) rest)
  in
  loop 1 init_state [] tacs

(** Binders along the path to the cursor inside [tm], for pretty-printing with [elab_ctx]
    and [lctx] (hypotheses + inner binders). *)
let binder_path_at_cursor (elab_ctx : Types.ctx) (base_lctx : Types.local_ctx)
    (tm : Term.term) (line : int) (col : int) : (string * string) list =
  let rec go acc lctx (t : Term.term) : (string * string) list =
    if not (range_contains t.loc line col) then acc
    else
      match t.inner with
      | Term.Fun (arg_name_opt, bid, ty_arg, body) ->
          if range_contains ty_arg.loc line col then go acc lctx ty_arg
          else
            let ty_str = Pretty.term_to_string elab_ctx ~lctx ty_arg in
            let name = Option.value ~default:"_" arg_name_opt in
            let new_lctx = Types.{ name = Some name; ty = ty_arg; bid } :: lctx in
            go (acc @ [ (name, ty_str) ]) new_lctx body
      | Term.Arrow (arg_name_opt, bid, ty_arg, ret) ->
          if range_contains ty_arg.loc line col then go acc lctx ty_arg
          else
            let ty_str = Pretty.term_to_string elab_ctx ~lctx ty_arg in
            let name = Option.value ~default:"_" arg_name_opt in
            let new_lctx = Types.{ name = Some name; ty = ty_arg; bid } :: lctx in
            go (acc @ [ (name, ty_str) ]) new_lctx ret
      | Term.App (f, arg) ->
          if range_contains f.loc line col then go acc lctx f else go acc lctx arg
      | _ -> acc
  in
  go [] base_lctx tm

let tactic_arg_binder_path (st : Proofstate.proof_state) (elab_ctx : Types.ctx)
    (ps : Statement.proof_script) (line : int) (col : int) : context_item list =
  let base_lctx = match Proofstate.current_goal st with None -> [] | Some g -> g.lctx in
  let try_arg (raw : Term.term) : (string * string) list =
    if not (range_contains raw.loc line col) then []
    else binder_path_at_cursor elab_ctx base_lctx raw line col
  in
  let rec first_some f = function
    | [] -> None
    | x :: xs -> ( match f x with [] -> first_some f xs | ys -> Some ys)
  in
  let rec scan (l : Statement.tactic list) : (string * string) list =
    match l with
    | [] -> []
    | (tac : Statement.tactic) :: rest -> (
        match first_some try_arg tac.args with Some xs -> xs | None -> scan rest)
  in
  scan ps.tactics |> List.map (fun (n, ty_str) -> { name = n; ty = ty_str })

let term_context_at_cursor (env_before_decl : Types.ctx) (goal_ty_tm : Term.term)
    (kind : Statement.decl_type) (elab_ctx : Types.ctx) (st : Proofstate.proof_state)
    (line : int) (col : int) : context_item list =
  match kind with
  | Statement.Theorem (Statement.DefEq proof_tm) | Statement.Def proof_tm ->
      let proof_tm = Typecheck.elaborate env_before_decl proof_tm (Some goal_ty_tm) in
      let cursor_in_proof = range_contains proof_tm.loc line col in
      if not cursor_in_proof then []
      else
        binder_path_at_cursor elab_ctx [] proof_tm line col
        |> List.map (fun (n, ty_str) -> { name = n; ty = ty_str })
  | Statement.Theorem (Statement.Proof ps) ->
      tactic_arg_binder_path st elab_ctx ps line col
  | Statement.Axiom -> []

let snapshot_proofstate (filename : string) (line : int) (col : int) :
    proofstate_snapshot option =
  let env = load_default_env_for_paths filename in
  let stmts = Elab.Interface.get_all_statements filename in
  let rec find_and_prepare (acc_env : Types.ctx) (remaining : Statement.statement list) :
      (Statement.declaration * Types.ctx) option =
    match remaining with
    | [] -> None
    | stmt :: rest -> (
        match stmt with
        | Statement.Declaration d ->
            let decl_range = { Term.start = d.name_loc.start; end_ = decl_end_loc d } in
            if
              same_file d.name_loc.start.pos_fname filename
              && range_contains decl_range line col
            then Some (d, acc_env)
            else (
              Elab.Interface.process_statement acc_env stmt;
              find_and_prepare acc_env rest)
        | _ ->
            Elab.Interface.process_statement acc_env stmt;
            find_and_prepare acc_env rest)
  in
  match find_and_prepare env stmts with
  | None -> None
  | Some (d, env_before_decl) -> (
      let goal_ty_tm = Typecheck.elaborate env_before_decl d.ty None in
      let init_st = Proofstate.init_state ~elab_ctx:env_before_decl goal_ty_tm in
      let st, tactics_applied =
        match d.kind with
        | Statement.Theorem (Statement.Proof ps) ->
            let k = tactics_prefix_count ps line col in
            (Tactic.apply_first_k_tactics init_st ps.tactics k, k)
        | _ -> (init_st, 0)
      in
      let environment = snapshot_environment env_before_decl in
      let tactic_steps =
        match d.kind with
        | Statement.Theorem (Statement.Proof ps) ->
            snapshot_tactic_steps env_before_decl goal_ty_tm ps.tactics line col
        | _ -> []
      in
      let term_context =
        term_context_at_cursor env_before_decl goal_ty_tm d.kind st.elab_ctx st line col
      in
      let open_goal_types =
        List.map
          (fun (g : Proofstate.goal) ->
            Pretty.term_to_string st.elab_ctx ~lctx:g.lctx g.goal_type)
          st.open_goals
      in
      match st.open_goals with
      | [] ->
          let metas = snapshot_metas st.elab_ctx in
          Some
            {
              decl_name = d.name;
              decl_kind = decl_kind_to_string d.kind;
              decl_file = d.name_loc.start.pos_fname;
              decl_start_line = d.name_loc.start.pos_lnum;
              decl_start_col = pos_col d.name_loc.start;
              decl_end_line = (decl_end_loc d).pos_lnum;
              decl_end_col = pos_col (decl_end_loc d);
              goal_type = "(no open goals)";
              goal_type_reduced = "(no open goals)";
              head_context = [];
              term_context;
              hyps = [];
              environment;
              metas;
              tactic_steps;
              tactics_applied;
              open_goal_types;
            }
      | g :: _ ->
          let metas = snapshot_metas ~lctx:g.lctx st.elab_ctx in
          let gty = g.goal_type in
          let gty_red = Reduce.reduce st.elab_ctx gty in
          let goal_type = Pretty.term_to_string st.elab_ctx ~lctx:g.lctx gty in
          let goal_type_reduced =
            Pretty.term_to_string st.elab_ctx ~lctx:g.lctx gty_red
          in
          let head_context =
            extract_head_binders st.elab_ctx gty_red
            |> List.map (fun (n, ty_str) -> { name = n; ty = ty_str })
          in
          let hyps =
            g.lctx
            |> List.map (fun (h : Types.lctx_entry) ->
                   ( Option.value ~default:"_" h.name,
                     h.bid,
                     Pretty.term_to_string st.elab_ctx ~lctx:g.lctx h.ty ))
          in
          Some
            {
              decl_name = d.name;
              decl_kind = decl_kind_to_string d.kind;
              decl_file = d.name_loc.start.pos_fname;
              decl_start_line = d.name_loc.start.pos_lnum;
              decl_start_col = pos_col d.name_loc.start;
              decl_end_line = (decl_end_loc d).pos_lnum;
              decl_end_col = pos_col (decl_end_loc d);
              goal_type;
              goal_type_reduced;
              head_context;
              term_context;
              hyps;
              environment;
              metas;
              tactic_steps;
              tactics_applied;
              open_goal_types;
            })

let print_snapshot_text (snap : proofstate_snapshot) : unit =
  Printf.printf "Declaration: %s (%s)\n" snap.decl_name snap.decl_kind;
  Printf.printf
    "Range: %s:%d:%d-%d:%d\n\n"
    snap.decl_file
    snap.decl_start_line
    snap.decl_start_col
    snap.decl_end_line
    snap.decl_end_col;
  let pp_ctx title (ctx : context_item list) =
    Printf.printf "%s:\n" title;
    (match ctx with
    | [] -> Printf.printf "  (none)\n"
    | _ -> List.iter (fun { name; ty } -> Printf.printf "  %s : %s\n" name ty) ctx);
    Printf.printf "\n"
  in
  pp_ctx "Head context" snap.head_context;
  Printf.printf "Goal:\n  ⊢ %s\n" snap.goal_type;
  if snap.goal_type <> snap.goal_type_reduced then
    Printf.printf "Goal (β-reduced):\n  ⊢ %s\n" snap.goal_type_reduced;
  if List.length snap.open_goal_types > 1 then (
    Printf.printf "\nAll open goals (%d):\n" (List.length snap.open_goal_types);
    List.iteri (fun i g -> Printf.printf "  [%d] ⊢ %s\n" (i + 1) g) snap.open_goal_types;
    Printf.printf "\n");
  pp_ctx "Term context (variables in scope at cursor)" snap.term_context;
  Printf.printf "Global environment (%d names):\n" (List.length snap.environment);
  (match snap.environment with
  | [] -> Printf.printf "  (none)\n"
  | _ ->
      List.iter
        (fun { env_name; env_kind; env_ty } ->
          Printf.printf "  %s (%s) : %s\n" env_name env_kind env_ty)
        snap.environment);
  Printf.printf "\nMetas (%d):\n" (List.length snap.metas);
  (match snap.metas with
  | [] -> Printf.printf "  (none)\n"
  | _ ->
      List.iter
        (fun m ->
          let ty_part = match m.meta_ty with Some s -> " : " ^ s | None -> "" in
          let sol_part =
            match m.meta_sol with Some s -> Printf.sprintf "  := %s" s | None -> ""
          in
          let ctx_part =
            if m.meta_context = [] then ""
            else
              "  ctx=[" ^ String.concat "," (List.map string_of_int m.meta_context) ^ "]"
          in
          Printf.printf "  ?%d%s%s%s\n" m.meta_id ty_part sol_part ctx_part)
        snap.metas);
  Printf.printf "\nGoal hypotheses (proof state hyps):\n";
  (match snap.hyps with
  | [] -> Printf.printf "  (none)\n"
  | _ ->
      List.iter
        (fun (name, bid, ty) -> Printf.printf "  %s [%d] : %s\n" name bid ty)
        (List.rev snap.hyps));
  Printf.printf "\nTactic progress:\n";
  (match snap.tactic_steps with
  | [] -> Printf.printf "  (none)\n"
  | _ ->
      List.iter
        (fun s ->
          let args =
            if s.step_args = [] then "" else " " ^ String.concat " " s.step_args
          in
          let before =
            match s.step_goal_before with Some g -> g | None -> "(no current goal)"
          in
          let after =
            if s.step_goals_after = [] then "(solved)"
            else String.concat " | " s.step_goals_after
          in
          let cursor_tag = if s.step_at_cursor then "  <cursor>" else "" in
          Printf.printf
            "  [%d] %s%s  status=%s%s\n      before: %s\n      after:  %s\n"
            s.step_index
            s.step_name
            args
            s.step_status
            cursor_tag
            before
            after)
        snap.tactic_steps);
  Printf.printf "\n"

let print_snapshot_json (filename : string) (line : int) (col : int)
    (snap : proofstate_snapshot) : unit =
  let ctx_items (xs : context_item list) : string =
    xs
    |> List.map (fun { name; ty } ->
           Printf.sprintf
             "{\"name\":\"%s\",\"type\":\"%s\"}"
             (json_escape name)
             (json_escape ty))
    |> String.concat ","
    |> fun s -> "[" ^ s ^ "]"
  in
  let hyps_items =
    snap.hyps |> List.rev
    |> List.map (fun (name, bid, ty) ->
           Printf.sprintf
             "{\"name\":\"%s\",\"bid\":%d,\"type\":\"%s\"}"
             (json_escape name)
             bid
             (json_escape ty))
    |> String.concat ","
    |> fun s -> "[" ^ s ^ "]"
  in
  let json_opt_string = function
    | None -> "null"
    | Some s -> Printf.sprintf "\"%s\"" (json_escape s)
  in
  let json_int_list (xs : int list) : string =
    "[" ^ String.concat "," (List.map string_of_int xs) ^ "]"
  in
  let json_string_list (xs : string list) : string =
    xs |> List.map (fun s -> Printf.sprintf "\"%s\"" (json_escape s)) |> String.concat ","
    |> fun s -> "[" ^ s ^ "]"
  in
  let env_items =
    snap.environment
    |> List.map (fun e ->
           Printf.sprintf
             "{\"name\":\"%s\",\"kind\":\"%s\",\"type\":\"%s\"}"
             (json_escape e.env_name)
             (json_escape e.env_kind)
             (json_escape e.env_ty))
    |> String.concat ","
    |> fun s -> "[" ^ s ^ "]"
  in
  let meta_items =
    snap.metas
    |> List.map (fun m ->
           Printf.sprintf
             "{\"id\":%d,\"type\":%s,\"solution\":%s,\"context\":%s}"
             m.meta_id
             (json_opt_string m.meta_ty)
             (json_opt_string m.meta_sol)
             (json_int_list m.meta_context))
    |> String.concat ","
    |> fun s -> "[" ^ s ^ "]"
  in
  let tactic_items =
    snap.tactic_steps
    |> List.map (fun s ->
           Printf.sprintf
             "{\"index\":%d,\"name\":\"%s\",\"args\":%s,\"goalBefore\":%s,\"goalsAfter\":%s,\"status\":\"%s\",\"atCursor\":%s}"
             s.step_index
             (json_escape s.step_name)
             (json_string_list s.step_args)
             (json_opt_string s.step_goal_before)
             (json_string_list s.step_goals_after)
             (json_escape s.step_status)
             (if s.step_at_cursor then "true" else "false"))
    |> String.concat ","
    |> fun s -> "[" ^ s ^ "]"
  in
  let open_goals_json = json_string_list snap.open_goal_types in
  Printf.printf
    "{\"ok\":true,\"query\":{\"file\":\"%s\",\"line\":%d,\"col\":%d},\"declaration\":{\"name\":\"%s\",\"kind\":\"%s\",\"file\":\"%s\",\"startLine\":%d,\"startCol\":%d,\"endLine\":%d,\"endCol\":%d},\"proofState\":{\"goalType\":\"%s\",\"goalTypeReduced\":\"%s\",\"headContext\":%s,\"termContext\":%s,\"hyps\":%s,\"environment\":%s,\"metas\":%s,\"tacticSteps\":%s,\"tacticsApplied\":%d,\"openGoals\":%s}}\n"
    (json_escape filename)
    line
    col
    (json_escape snap.decl_name)
    (json_escape snap.decl_kind)
    (json_escape snap.decl_file)
    snap.decl_start_line
    snap.decl_start_col
    snap.decl_end_line
    snap.decl_end_col
    (json_escape snap.goal_type)
    (json_escape snap.goal_type_reduced)
    (ctx_items snap.head_context)
    (ctx_items snap.term_context)
    hyps_items
    env_items
    meta_items
    tactic_items
    snap.tactics_applied
    open_goals_json

let run (prog : string) (args : string list) : unit =
  match parse_args args with
  | None ->
      Printf.eprintf
        "Invalid arguments.\n\
         Expected: [--json] <filename> <line> <col>   (line and column are 1-based \
         integers)\n\
         Example:\n\
         dune exec %s -- [--json] <filename> <line> <col>\n\n"
        prog;
      usage_standalone prog;
      exit 2
  | Some (use_json, filename, line, col) -> (
      try
        Automation.Tactics.register ();
        match snapshot_proofstate filename line col with
        | None ->
            if use_json then
              Printf.printf
                "{\"ok\":false,\"error\":\"No declaration found at this \
                 position.\",\"query\":{\"file\":\"%s\",\"line\":%d,\"col\":%d}}\n"
                (json_escape filename)
                line
                col
            else Printf.printf "No declaration found at %s:%d:%d\n" filename line col;
            exit 1
        | Some snap ->
            if use_json then print_snapshot_json filename line col snap
            else print_snapshot_text snap;
            exit 0
      with
      | Failure _ ->
          Printf.eprintf "line/col must be integers\n";
          exit 2
      | Error.ElabError e ->
          let empty = Elab.Interface.create () in
          if use_json then
            Printf.printf
              "{\"ok\":false,\"error\":\"%s\",\"query\":{\"file\":\"%s\",\"line\":%d,\"col\":%d}}\n"
              (json_escape (Error.pp_exn empty e))
              (json_escape filename)
              line
              col
          else Printf.eprintf "%s\n" (Error.pp_exn empty e);
          exit 1)

let () =
  record_backtrace true;
  match Array.to_list Sys.argv with prog :: args -> run prog args | [] -> exit 2
