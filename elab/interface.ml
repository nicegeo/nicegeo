module KTerm = Kernel.Term

let parse_term (s : string) : Term.term =
  let lexbuf = Lexing.from_string s in
  Parser.single_term Lexer.token lexbuf

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

(* Creates an elaborator environment with the default environment path. *)
let process_env (env : Types.ctx) : unit = process_file env "synthetic/env.ncg"
