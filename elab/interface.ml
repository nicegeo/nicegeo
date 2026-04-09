module KTerm = Kernel.Term

let parse_term (s : string) : Term.term =
  let lexbuf = Lexing.from_string s in
  Parser.single_term Lexer.token lexbuf

let create () : Types.ctx =
  {
    env = Hashtbl.create 16;
    kenv = Kernel.Interface.create ();
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

(** [parse_statements filename] parses all statements from the file [filename]. The output
    may contain import statements. Raises [Error.ElabError] with a [ParseError] payload on
    failure. *)
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

(** Like List.filter_map, but stops at the first None and also returns the remaining
    unprocessed list. *)
let rec take_while_map (f : 'a -> 'b option) (l : 'a list) : 'b list * 'a list =
  match l with
  | [] -> ([], [])
  | x :: xs -> (
      match f x with
      | None -> ([], l)
      | Some b ->
          let ys, rest = take_while_map f xs in
          (b :: ys, rest))

let rec get_all_statements (filename : string) : Statement.statement list =
  let stmts, rem =
    take_while_map
      (function
        | Statement.Import { filename = fname } -> Some (get_all_statements fname)
        | _ -> None)
      (parse_statements filename)
  in
  (* Error if rem contains any import statements *)
  List.iter
    (function
      | Statement.Import _ ->
          raise
            (Error.ElabError
               {
                 context = { loc = None; decl_name = None };
                 error_type = Error.ImportNotAtTop;
               })
      | _ -> ())
    rem;
  List.flatten stmts @ rem

let process_file (env : Types.ctx) (filename : string) : unit =
  let stmts = get_all_statements filename in
  List.iter (process_statement env) stmts

(* Creates an elaborator environment with the default environment path. *)
let process_env (env : Types.ctx) : unit = process_file env "synthetic/env.ncg"
