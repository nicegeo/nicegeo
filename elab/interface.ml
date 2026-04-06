module KTerm = Kernel.Term

let create () : Types.ctx =
  {
    env = Hashtbl.create 16;
    kenv = Hashtbl.create 16;
    metas = Hashtbl.create 16;
    lctx = Hashtbl.create 16;
  }

let process_statement (env : Types.ctx) (stmt : Statement.statement) : unit =
  match stmt with
  | Statement.Declaration decl -> Typecheck.process_decl env decl
  | Statement.Directive dir -> Directives.process_directive env dir
  | Statement.Import _ ->
      raise
        (Error.ElabError
           {
             context = { loc = None; decl_name = None };
             error_type = Error.ImportUnexpected;
           })
(* TODO: Deal with clashing names in imports *)

(* Creates an elaborator environment by parsing the environment file at `path_to_env`. *)
let create_with_env_path (path_to_env : string) : Types.ctx =
  let e = create () in
  let ic = open_in path_to_env in
  let lexbuf = Lexing.from_channel ic in
  let stmts = Parser.main Lexer.token lexbuf in
  let _ = List.map (process_statement e) stmts in
  e

(* Creates an elaborator environment with the default environment path. *)
let create_with_env () : Types.ctx = create_with_env_path "synthetic/env.ncg"

let parse_term (s : string) : Term.term =
  let lexbuf = Lexing.from_string s in
  Parser.single_term Lexer.token lexbuf

let parse_statements (filename : string) : Statement.statement list =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf filename;
  let decls =
    try Parser.main Lexer.token lexbuf
    with exn ->
      let msg = match exn with Failure msg -> msg | _ -> Printexc.to_string exn in
      let pos1 = lexbuf.lex_start_p in
      let pos2 = lexbuf.lex_curr_p in
      raise
        (Error.ElabError
           {
             context = { loc = Some { start = pos1; end_ = pos2 }; decl_name = None };
             error_type =
               Error.ParseError { input = Lexing.lexeme lexbuf; error_msg = msg };
           })
  in
  decls

let process_file (env : Types.ctx) (filename : string) : unit =
  let stmts = parse_statements filename in
  List.iter (process_statement env) stmts

let rec get_all_statements (filename : string) : Statement.statement list =
  List.fold_left_map
    (fun can_import -> function
      | Statement.Import { filename = fname } ->
          if can_import then (true, get_all_statements fname)
          else
            raise
              (Error.ElabError
                 {
                   context = { loc = None; decl_name = None };
                   error_type = Error.ImportNotAtTop;
                 })
      | s -> (false, [ s ]))
    true
    (parse_statements filename)
  |> snd |> List.flatten
