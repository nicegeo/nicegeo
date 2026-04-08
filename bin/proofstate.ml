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
      | Statement.Proof tactics -> (
          match List.rev tactics with t :: _ -> t.loc.end_ | [] -> d.ty.loc.end_))
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
  let rec go acc (t : Term.term) =
    match t.inner with
    | Term.Arrow (arg_name_opt, bid, ty_arg, ty_ret) ->
        Hashtbl.replace ectx.lctx bid (arg_name_opt, ty_arg);
        let name = match arg_name_opt with Some s -> s | None -> "_" in
        let ty_str = Proofstate.pp_term ectx ty_arg in
        go (acc @ [ (name, ty_str) ]) ty_ret
    | _ -> acc
  in
  go [] ty

let snapshot_environment (e : Types.ctx) : env_item list =
  Hashtbl.fold
    (fun name (entry : Types.enventry) acc ->
      let kind =
        match entry.data with
        | Types.Axiom -> "axiom"
        | Types.Theorem _ -> "theorem"
        | Types.Def _ -> "definition"
      in
      let ty_str = Proofstate.pp_term e entry.ty in
      { env_name = name; env_kind = kind; env_ty = ty_str } :: acc)
    e.env
    []
  |> List.sort (fun a b -> String.compare a.env_name b.env_name)

let snapshot_metas (e : Types.ctx) : meta_item list =
  Hashtbl.fold
    (fun mid (m : Types.metavar) acc ->
      let ty_s =
        match m.ty with Some t -> Some (Proofstate.pp_term e t) | None -> None
      in
      let sol_s =
        match m.sol with Some t -> Some (Proofstate.pp_term e t) | None -> None
      in
      { meta_id = mid; meta_ty = ty_s; meta_sol = sol_s; meta_context = m.context } :: acc)
    e.metas
    []
  |> List.sort (fun a b -> compare a.meta_id b.meta_id)

let restore_lctx (dst : Types.ctx) (saved : (int, string option * Term.term) Hashtbl.t) :
    unit =
  Hashtbl.clear dst.lctx;
  Hashtbl.iter (Hashtbl.add dst.lctx) saved

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
      let st = Proofstate.init_state ~elab_ctx:env_before_decl goal_ty_tm in
      let environment = snapshot_environment env_before_decl in
      match st.open_goals with
      | [] -> None
      | g :: _ ->
          let metas = snapshot_metas st.elab_ctx in
          let lctx0 = Hashtbl.copy st.elab_ctx.lctx in
          let gty = g.goal_type in
          let gty_red = Reduce.reduce st.elab_ctx gty in
          let goal_type = Proofstate.pp_term st.elab_ctx gty in
          let goal_type_reduced = Proofstate.pp_term st.elab_ctx gty_red in
          let head_context =
            restore_lctx st.elab_ctx lctx0;
            extract_head_binders st.elab_ctx gty_red
            |> List.map (fun (n, ty_str) -> { name = n; ty = ty_str })
          in
          restore_lctx st.elab_ctx lctx0;
          let term_context =
            match d.kind with
            | Statement.Theorem (Statement.DefEq proof_tm) ->
                let cursor_in_proof = range_contains proof_tm.loc line col in
                if not cursor_in_proof then []
                else
                  let term_context =
                    let rec go acc (t : Term.term) : (string * string) list =
                      if not (range_contains t.loc line col) then acc
                      else
                        match t.inner with
                        | Term.Fun (arg_name_opt, bid, ty_arg, body) ->
                            if range_contains ty_arg.loc line col then go acc ty_arg
                            else (
                              Hashtbl.replace st.elab_ctx.lctx bid (arg_name_opt, ty_arg);
                              let ty_str = Proofstate.pp_term st.elab_ctx ty_arg in
                              let name =
                                match arg_name_opt with Some s -> s | None -> "_"
                              in
                              go (acc @ [ (name, ty_str) ]) body)
                        | Term.Arrow (arg_name_opt, bid, ty_arg, ret) ->
                            if range_contains ty_arg.loc line col then go acc ty_arg
                            else (
                              Hashtbl.replace st.elab_ctx.lctx bid (arg_name_opt, ty_arg);
                              let ty_str = Proofstate.pp_term st.elab_ctx ty_arg in
                              let name =
                                match arg_name_opt with Some s -> s | None -> "_"
                              in
                              go (acc @ [ (name, ty_str) ]) ret)
                        | Term.App (f, arg) ->
                            if range_contains f.loc line col then go acc f else go acc arg
                        | _ -> acc
                    in
                    go [] proof_tm
                  in
                  term_context |> List.map (fun (n, ty_str) -> { name = n; ty = ty_str })
            | Statement.Theorem (Statement.Proof _) -> []
            | _ -> []
          in
          let hyps =
            g.ctx
            |> List.map (fun (h : Proofstate.hyp) ->
                (h.hyp_name, h.hyp_bid, Proofstate.pp_term st.elab_ctx h.hyp_type))
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
  Printf.printf "\n";
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
        snap.hyps);
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
    snap.hyps
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
  Printf.printf
    "{\"ok\":true,\"query\":{\"file\":\"%s\",\"line\":%d,\"col\":%d},\"declaration\":{\"name\":\"%s\",\"kind\":\"%s\",\"file\":\"%s\",\"startLine\":%d,\"startCol\":%d,\"endLine\":%d,\"endCol\":%d},\"proofState\":{\"goalType\":\"%s\",\"goalTypeReduced\":\"%s\",\"headContext\":%s,\"termContext\":%s,\"hyps\":%s,\"environment\":%s,\"metas\":%s}}\n"
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
