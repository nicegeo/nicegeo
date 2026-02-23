module KTerm = System_e_kernel.Term

let create () : Types.ctx = {
  env = Hashtbl.create 16;
  kenv = Hashtbl.create 16;

  metas = Hashtbl.create 16;
  lctx = Hashtbl.create 16;
}

let create_with_env_path (path_to_env : string) : Types.ctx =
  let e = create () in
  let ic = open_in path_to_env in
  let lexbuf = Lexing.from_channel ic in
  let decls = Parser.main Lexer.token lexbuf in
  let _ = List.map (Typecheck.process_decl e) decls in
  e

let create_with_env () : Types.ctx = 
  create_with_env_path "elab/env.txt"

let process_decl (env: Types.ctx) (decl: Decl.declaration) : unit =
  Typecheck.process_decl env decl

let list_axioms (env: Types.ctx) (name: string) = 
  match Hashtbl.find_opt env.env name with
  | Some entry ->
      (match entry.data with
      | Types.Axiom -> failwith (name ^ " is an axiom")
      | Types.Theorem axioms -> axioms)
  | None -> failwith ("unknown declaration: " ^ name)