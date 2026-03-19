(** The general strategy for filling in user-specified holes essentially boils down to
    creating unique variables each time we encounter a hole, generating constraints
    (equations) that a correctly typed program would have to satisfy with bidirectional
    type checking, and then using pattern unification to find solutions (i.e. specific
    terms to place at that hole) for each variable.

    In order to simplify the unification algorithm, we want solutions to holes to be
    closed terms, meaning that all variables used in that term are also introduced inside
    that term (e.g. `fun c => fun d => c d` is a closed term but `fun d => c d` isn't
    since the latter uses `c` without defining it), although references to previously
    defined theorems/axioms are still allowed. The reasoning for that is that as we
    traverse the term that we're type checking, the de Bruijn indices of each bound
    variable and the local context might change (since a given Bvar index points to
    different definitions depending on how many surrounding function definitions there
    are, and free variables get introduced/removed as necessary when type checking
    functions). By requiring that holes are always closed terms, interpreting a closed
    term doesn't require looking at any external Bvars or Fvars, so we don't have to
    remember what Bvar/Fvar mapping to use for each hole.

    The way we ensure that holes only ever need to be closed terms is that we
    automatically convert holes into functions that get immediately called with all of the
    bound variables in the expression at that point (e.g. if a hole appears in an
    expression at a point where `x: A` and `y: B` have already been defined then we'd
    convert the term to `?H x y` where `?H` is the hole we want to solve for, at which
    point we'd expect that `?H` to be a function `A -> B -> T` for some type `T`).

    You can uncomment the print statements in this file to see how the algorithm works in
    more detail.

    See lecture 3 of https://github.com/andrejbauer/faux-type-theory for more information
    on the algorithm. *)
open Statement

open Term
open Convert
open Types
module KInfer = Kernel.Infer
module KExceptions = Kernel.Exceptions

let raise_at (tm : term) (e : Error.error_type) : 'a =
  let loc = Some tm.loc in
  raise (Error.ElabError { context = { loc; decl_name = None }; error_type = e })

type normterm =
  | Fun of string option * int * term * term
  | Arrow of string option * int * term * term
      (** (variable, args) where variable is a variable of some kind (either a name, a
          bound variable, or a free variable), and that variable is applied to all
          arguments in `args` from first to last (so this represents the expressions
          `variable arg0 arg1 ... argN`) *)
  | VarSpine of term * term list
      (** (hole, args) that represents the expression `hole arg0 arg1 ... argN` where
          `hole` is a hole that we need to solve for and args are arbitrary terms *)
  | MetaSpine of term * term list
  | Sort of int

(** [subst e tm pat replacement] substitutes all occurrences of `pat` with `replacement` in `tm` *)
let rec subst (e: ctx) (tm : term) (pat : termkind) (replacement : term) =
  match tm.inner with
  | Name _ | Bvar _ -> if tm.inner = pat then replacement else tm
  | Fun (x, bid, ty, body) ->
      let ty_subst = subst e ty pat replacement in
      let body_subst = subst e body pat replacement in
      { inner = Fun (x, bid, ty_subst, body_subst); loc = tm.loc }
  | Arrow (x, bid, ty_arg, ty_ret) ->
      let ty_arg_subst = subst e ty_arg pat replacement in
      let ty_ret_subst = subst e ty_ret pat replacement in
      { inner = Arrow (x, bid, ty_arg_subst, ty_ret_subst); loc = tm.loc }
  | App (f, arg) ->
      let f_subst = subst e f pat replacement in
      let arg_subst = subst e arg pat replacement in
      { inner = App (f_subst, arg_subst); loc = tm.loc }
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; _ } -> subst e tm_sol pat replacement
      | _ -> tm)
  | _ -> tm

let rec whnf_beta (e : ctx) (tm : term) : term =
  match tm.inner with
  | App (f, arg) -> (
      let fn = whnf_beta e f in
      match fn.inner with
      | Fun (_, bid, _, body) -> whnf_beta e (subst e body (Bvar bid) arg)
      | _ -> { inner = App (fn, arg); loc = tm.loc })
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; _ } -> whnf_beta e tm_sol
      | _ -> tm)
  | _ -> tm

(* precondition: tm is already in whnf (call whnf_beta) *)
let rec to_norm (e : ctx) (tm : term) : normterm =
  match tm.inner with
  | Fun (arg, bid, ty_arg, body) -> Fun (arg, bid, ty_arg, body)
  | Arrow (arg, bid, ty_arg, ty_ret) -> Arrow (arg, bid, ty_arg, ty_ret)
  | App (f, arg) -> (
      let f_norm = to_norm e f in
      match f_norm with
      | VarSpine (head, args) -> VarSpine (head, args @ [ arg ])
      | MetaSpine (head, args) -> MetaSpine (head, args @ [ arg ])
      | Fun _ ->
          raise_at tm (Error.InternalError "to_norm input should already be in whnf")
      | Arrow (n, bid, ty_arg, ty_ret) ->
          raise_at
            tm
            (Error.FunctionExpected
               {
                 not_func = tm;
                 not_func_type = { inner = Arrow (n, bid, ty_arg, ty_ret); loc = tm.loc };
                 arg;
               })
      | Sort n ->
          raise_at
            tm
            (Error.FunctionExpected
               { not_func = tm; not_func_type = { inner = Sort n; loc = tm.loc }; arg }))
  | Name _ | Bvar _ -> VarSpine (tm, [])
  | Sort n -> Sort n
  | Hole _ -> MetaSpine (tm, [])

let rec last (lst : 'a list) : 'a =
  match lst with
  | [] -> failwith "last of empty list"
  | [ x ] -> x
  | _ :: rest -> last rest

let rec original_bid (graph : rw_graph) (bid : int) : int =
  match Hashtbl.find_opt graph bid with
  | Some new_bid -> original_bid graph new_bid
  | None -> bid

let rec valid_pattern (e: ctx) (graph : rw_graph) (m : int) (tm : term) (ctx : int list) : bool =
  match tm.inner with
  | Bvar bid -> (
    (* either bound in the solution itself or part of the hole's own context *)
    (* print_endline ("checking if bound variable " ^ string_of_int bid ^ " is valid in solution for ?m" ^ string_of_int m);
    print_endline ("current context: " ^ String.concat ", " (List.map string_of_int ctx));
    print_endline ("current hole context: " ^ String.concat ", " (List.map string_of_int (Hashtbl.find e.metas m).context));
    print_endline ("original bid of " ^ string_of_int bid ^ " is " ^ string_of_int (original_bid graph bid)); *)
    (List.exists (fun context_bid -> context_bid = bid) ctx) ||
    ((Hashtbl.find e.metas m).context |> List.exists (fun context_bid -> original_bid graph bid = context_bid)))
  | Fun (_, bid, ty_arg, body) -> valid_pattern e graph m ty_arg ctx && valid_pattern e graph m body (bid :: ctx)
  | Arrow (_, bid, ty_arg, ty_ret) -> valid_pattern e graph m ty_arg ctx && valid_pattern e graph m ty_ret (bid :: ctx)
  | App (f, arg) -> valid_pattern e graph m f ctx && valid_pattern e graph m arg ctx
  | Hole n -> (
    if n = m then false else
    match Hashtbl.find_opt e.metas n with
    | Some { sol = Some sol; _ } -> valid_pattern e graph m sol ctx
    | _ -> true)
  | Sort _ | Name _ -> true

let rec pattern_match_meta (e : ctx) (graph : rw_graph) (m : int) (args : term list) (tm : term) : unit =
  (* print_endline ("pattern matching meta " ^ string_of_int m ^ " with args " ^ String.concat " " (List.map (Pretty.term_to_string e) args) ^ " against term " ^ Pretty.term_to_string e tm); *)
  if List.length args > 0 then
    match tm.inner with
    (* If `m most_args last_arg = f arg` then we can just make sure that `m most_args = f` and `last_arg = arg`*)
    | App (f, arg) when (last args).inner = arg.inner ->
        pattern_match_meta e graph m (List.rev (List.tl (List.rev args))) f
    | _ -> print_endline "tried to higher order unify?"
  else if not (valid_pattern e graph m tm []) then
    (print_endline "invalid solution for meta"; ())
  else
    Hashtbl.replace
      e.metas
      m
      {
        (Hashtbl.find e.metas m) with
        sol = Some tm;
      }

(** recursively replaces Bvar pat with Bvar replacement in metavar solutions that appear in tm *)
let rec unsubst_metavars (e : ctx) (tm : term) (pat : int) (replacement : int) : term =
  match tm.inner with
  | Bvar bid -> if bid = pat then { inner = Bvar replacement; loc = tm.loc } else tm
  | Fun (x, bid, ty, body) ->
      let ty_subst = unsubst_metavars e ty pat replacement in
      let body_subst = unsubst_metavars e body pat replacement in
      { inner = Fun (x, bid, ty_subst, body_subst); loc = tm.loc }
  | Arrow (x, bid, ty_arg, ty_ret) ->
      let ty_arg_subst = unsubst_metavars e ty_arg pat replacement in
      let ty_ret_subst = unsubst_metavars e ty_ret pat replacement in
      { inner = Arrow (x, bid, ty_arg_subst, ty_ret_subst); loc = tm.loc }
  | App (f, arg) ->
      let f_subst = unsubst_metavars e f pat replacement in
      let arg_subst = unsubst_metavars e arg pat replacement in
      { inner = App (f_subst, arg_subst); loc = tm.loc }
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; ty; context } -> 
        Hashtbl.replace e.metas m {sol = Some (unsubst_metavars e tm_sol pat replacement); ty; context};
        tm
      | _ -> tm)
  | _ -> tm

(** Takes in two terms `t1` and `t2` (both defined in the same context `e`) and solves for
    holes assuming that `t1 = t2` "make t1 and t2 definitionally equal" *)
let rec unify ?(depth = 0) (e : ctx) (t1 : term) (g1 : rw_graph) (t2 : term) (g2 : rw_graph) : unit =
  let t1 = whnf_beta e t1 in
  let t2 = whnf_beta e t2 in
  (* print_endline (String.make depth ' ' ^ "unifying " ^ Pretty.term_to_string e t1 ^ " and " ^ Pretty.term_to_string e t2); *)
  let nt1 = to_norm e t1 in
  let nt2 = to_norm e t2 in
  (* t1 and t2 should be closed under the current e *)
  match (nt1, nt2) with
  (* Have `m1 args1 = m2 args2` so just assume `m1` and `m2` should be the same thing and
    `args1 = args2` *)
  | ( MetaSpine ({ inner = Hole m1; _ }, args1),
      MetaSpine ({ inner = Hole m2; loc = l2 }, args2) ) ->
      (* could theoretically do some freaky stuff here *)
      if List.length args1 <> List.length args2 then
        print_endline "tried to unify different length meta spines"
      else (if m1 = m2 then ()
      else
        (* Have the hole with the smaller ID point to the larger ID to ensure that there aren't any holes that refer to each other
    in a cycle *)
        let m1, m2 = if m1 < m2 then (m1, m2) else (m2, m1) in
        Hashtbl.replace
          e.metas
          m1
          { (Hashtbl.find e.metas m1) with sol = Some { inner = Hole m2; loc = l2 } });
      List.iter2 (fun arg1 arg2 -> unify ~depth:(depth + 1) e arg1 g1 arg2 g2) args1 args2
  | MetaSpine ({ inner = Hole m; _ }, args), _ -> pattern_match_meta e g1 m args t2
  | _, MetaSpine ({ inner = Hole m; _ }, args) -> pattern_match_meta e g2 m args t1
  | VarSpine (h1, args1), VarSpine (h2, args2) when h1.inner = h2.inner ->
      if List.length args1 <> List.length args2 then
        failwith "tried to unify different length var spines"
      else List.iter2 (fun arg1 arg2 -> unify ~depth:(depth + 1) e arg1 g1 arg2 g2) args1 args2
  | Arrow (_, bid1, ty_arg1, ty_ret1), Arrow (_, bid2, ty_arg2, ty_ret2) ->
      unify ~depth:(depth + 1) e ty_arg1 g1 ty_arg2 g2;
      let ty_ret2 = (if bid1 <> bid2 then
        (* make them equal *)
        Hashtbl.replace g2 bid1 bid2;
        subst e ty_ret2 (Bvar bid2) { inner = Bvar bid1; loc = ty_ret2.loc }) in
      unify ~depth:(depth + 1) e ty_ret1 g1 ty_ret2 g2;
      (if bid1 <> bid2 then
        (* unsubst? *)
        (* any holes solved in ty_ret2 may reference bid1 when it should reference bid2 *)
        ignore (unsubst_metavars e ty_ret2 bid1 bid2);
        Hashtbl.remove g2 bid2)
  | Fun (_, bid1, ty_arg1, body1), Fun (_, bid2, ty_arg2, body2) ->
      (* todo: eta i think here? *)
      unify ~depth:(depth + 1) e ty_arg1 g1 ty_arg2 g2;
      let body2 = (if bid1 <> bid2 then
        (* make them equal *)
        Hashtbl.replace g2 bid2 bid1;
        subst e body2 (Bvar bid2) { inner = Bvar bid1; loc = body2.loc }) in
      unify ~depth:(depth + 1) e body1 g1 body2 g2;
      (if bid1 <> bid2 then
        (* unsubst *)
        ignore (unsubst_metavars e body2 bid2 bid1);
        Hashtbl.remove g2 bid2)
  | Sort n1, Sort n2 when n1 = n2 -> ()
  | _ ->
      failwith
        ("failed to unify non-matching terms " ^ Pretty.term_to_string e t1 ^ " and "
       ^ Pretty.term_to_string e t2)

(** checks that tm has expected type ty, trying to fill in metavariables (holes). If it
    fails it throws an ElabError. *)
let rec checktype ?(depth = 0) (e : ctx) (tm : term) (ty : term) : unit =
  (* print_endline (String.make depth ' ' ^ "checking " ^ Pretty.term_to_string e tm ^ " has type " ^ Pretty.term_to_string e ty); *)
  match tm.inner with
  | Hole m -> (
    (* print_endline (String.make depth ' ' ^ "encountered hole ?m" ^ string_of_int m ^ " with expected type " ^ Pretty.term_to_string e ty); *)
      match Hashtbl.find_opt e.metas m with
      | Some { ty = ty1; context; sol } -> (
          match ty1 with
          | Some ty1 -> unify ~depth:(depth + 1) e ty (Hashtbl.create 0) ty1 (Hashtbl.create 0)
          | None -> Hashtbl.replace e.metas m { ty = Some ty; context; sol })
      | None -> raise_at tm (Error.InternalError ("unknown meta: " ^ string_of_int m)))
  | App _ | Name _ | Fun _ | Arrow _ | Sort _ | Bvar _ -> (
      let infer_ty = infertype ~depth:(depth + 1) e tm in
      try unify ~depth:(depth + 1) e infer_ty (Hashtbl.create 0) ty (Hashtbl.create 0)
      with Failure _ ->
        raise_at
          tm
          (Error.TypeMismatch { term = tm; inferred_type = infer_ty; expected_type = ty })
      )

(** Infer the type of the term `tm` in the context `e`, possibly throwing an ElabError *)
and infertype ?(depth = 0) (e : ctx) (tm : term) : term =
  (* print_endline (String.make depth ' ' ^ "inferring type of " ^ Pretty.term_to_string e tm); *)
  let res =
    match tm.inner with
    | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { ty = Some ty; _ } -> ty
      | Some { sol = Some sol; context; ty = _ } -> (
          let sol_ty = infertype ~depth:(depth + 1) e sol in
          Hashtbl.replace e.metas m { sol = Some sol; ty = Some sol_ty; context };
          sol_ty
        )
      | _ -> raise_at tm Error.CannotInferHole
      )
    | Name name -> (
        match Hashtbl.find_opt e.env name with
        | Some entry -> entry.ty
        | None -> raise_at tm (Error.UnknownName { name }))
    | Fun (arg, bid, ty_arg, body) ->
        check_is_type ~depth:(depth + 1) e ty_arg;
        Hashtbl.add e.lctx bid (arg, ty_arg);
        let ty_body = infertype ~depth:(depth + 1) e body in
        Hashtbl.remove e.lctx bid;
        { inner = Arrow (arg, bid, ty_arg, ty_body); loc = tm.loc }
    | Arrow (arg, bid, ty_arg, ty_ret) ->
        let ty_arg_ty = whnf_beta e (infertype ~depth:(depth + 1) e ty_arg) in
        let arg_sort = match ty_arg_ty.inner with
        | Sort n -> n
        | _ -> raise_at ty_arg (Error.TypeExpected { not_type = ty_arg; not_type_infer = ty_arg_ty }) in
        Hashtbl.add e.lctx bid (arg, ty_arg);
        let ty_ret_ty = whnf_beta e (infertype ~depth:(depth + 1) e ty_ret) in
        let ret_sort = match ty_ret_ty.inner with
        | Sort n -> n
        | _ -> raise_at ty_ret (Error.TypeExpected { not_type = ty_ret; not_type_infer = ty_ret_ty }) in
        Hashtbl.remove e.lctx bid;
        { inner = Sort (if ret_sort = 0 then 0 else max arg_sort ret_sort); loc = tm.loc }
    | App (f, arg) -> (
        let f_type = whnf_beta e (infertype ~depth:(depth + 1) e f) in
        match f_type.inner with
        | Arrow (_, bid, ty_arg, ty_ret) ->
            checktype ~depth:(depth + 1) e arg ty_arg;
            subst e ty_ret (Bvar bid) arg
        | _ ->
            raise_at
              f
              (Error.FunctionExpected { not_func = f; not_func_type = f_type; arg }))
    | Bvar b -> (
      match Hashtbl.find_opt e.lctx b with
      | Some (_, ty) -> ty
      | None -> raise_at tm (Error.InternalError "unknown bound variable in infertype")
    )
    | Sort n -> { inner = Sort (n + 1); loc = tm.loc }
  in
  (* print_endline ("inferred type " ^ Pretty.term_to_string e res ^ " for term " ^ Pretty.term_to_string e tm); *)
  res

and check_is_type ?(depth = 0) (e : ctx) (tm : term) : unit =
  (* print_endline (String.make depth ' ' ^ "checking " ^ Pretty.term_to_string e tm ^ " is a type"); *)
  match tm.inner with
  | Hole _ -> ()
  | _ -> (
    let inferred_ty = infertype ~depth:(depth + 1) e tm in
    let inferred_ty_whnf = whnf_beta e inferred_ty in
    match inferred_ty_whnf.inner with
    | Sort _ -> ()
    | _ -> raise_at tm (Error.TypeExpected { not_type = tm; not_type_infer = inferred_ty_whnf }))

let rec create_metas (e : ctx) (tm : term) (stack : int list) =
  match tm.inner with
  | Hole m ->
      Hashtbl.replace e.metas m { sol = None; ty = None; context = stack };
  | Fun (_, bid, ty_arg, body) ->
      create_metas e ty_arg stack;
      create_metas e body (stack @ [bid]);
  | Arrow (_, bid, ty_arg, ty_ret) ->
      create_metas e ty_arg stack;
      create_metas e ty_ret (stack @ [bid]);
  | App (f, arg) ->
      create_metas e f stack;
      create_metas e arg stack;
  | _ -> ()

(** Needs to be trusted for faithfulness of meaning. This returns tm unchanged except for
    replacing metavariables (holes) with their solutions. *)
let rec replace_metas (e : ctx) (tm : term) : term =
  match tm.inner with
  | Hole m -> (
      match Hashtbl.find_opt e.metas m with
      | Some { sol = Some tm_sol; _ } ->
          replace_metas e tm_sol
      | _ -> raise_at tm Error.CannotInferHole)
  | Fun (arg, bid, ty_arg, body) ->
      let ty_arg_filled = replace_metas e ty_arg in
      let body_filled = replace_metas e body in
      { inner = Fun (arg, bid, ty_arg_filled, body_filled); loc = tm.loc }
  | Arrow (arg, bid, ty_arg, ty_ret) ->
      let ty_arg_filled = replace_metas e ty_arg in
      let ty_ret_filled = replace_metas e ty_ret in
      { inner = Arrow (arg, bid, ty_arg_filled, ty_ret_filled); loc = tm.loc }
  | App (f, arg) ->
      let f_filled = replace_metas e f in
      let arg_filled = replace_metas e arg in
      { inner = App (f_filled, arg_filled); loc = tm.loc }
  | _ -> tm

let union (l1 : string list) (l2 : string list) : string list =
  let set = Hashtbl.create 0 in
  List.iter (fun x -> Hashtbl.replace set x ()) l1;
  List.iter (fun x -> Hashtbl.replace set x ()) l2;
  Hashtbl.fold (fun key _ acc -> key :: acc) set []

let rec list_axioms_used (e : ctx) (tm : term) : string list =
  match tm.inner with
  | Name name -> (
      match Hashtbl.find_opt e.env name with
      | Some { data = Theorem axioms; _ } -> axioms
      | Some { data = Axiom; _ } -> [ name ]
      | None -> raise_at tm (Error.UnknownName { name }))
  | Fun (_, _, ty_arg, body) -> union (list_axioms_used e ty_arg) (list_axioms_used e body)
  | Arrow (_, _, ty_arg, ty_ret) ->
      union (list_axioms_used e ty_arg) (list_axioms_used e ty_ret)
  | App (f, arg) -> union (list_axioms_used e f) (list_axioms_used e arg)
  | _ -> []

(* Needs to be trusted for faithfulness of meaning *)
let process_decl (e : ctx) (d : declaration) : unit =
  try
    match d.kind with
    | Theorem proof -> (
        if Hashtbl.mem e.env d.name then
          raise
            (Error.ElabError
               {
                 context = { loc = Some d.name_loc; decl_name = Some d.name };
                 error_type = Error.AlreadyDefined d.name;
               })
        else
          create_metas e d.ty [];
          check_is_type e d.ty;
          (* replace_metas only fills in metavariables *)
          let ty_filled = replace_metas e d.ty in
          Hashtbl.clear e.metas;
          create_metas e proof [];
          checktype e proof ty_filled;
          let proof_filled = replace_metas e proof in
          Hashtbl.clear e.metas;
          (* conv_to_kterm does a straightforward variant-to-variant conversion *)
          let ty_k = conv_to_kterm ty_filled in
          let proof_k = conv_to_kterm proof_filled in

          try
            let inferredType = KInfer.inferType e.kenv (Hashtbl.create 0) proof_k in
            let isValidProof =
              KInfer.isDefEq e.kenv (Hashtbl.create 0) inferredType ty_k
            in

            if isValidProof then (
              Hashtbl.add
                e.env
                d.name
                {
                  name = d.name;
                  ty = ty_filled;
                  data = Theorem (list_axioms_used e proof_filled);
                };
              Hashtbl.add e.kenv d.name ty_k)
            else
              raise
                (Error.ElabError
                   {
                     context = { loc = Some d.name_loc; decl_name = Some d.name };
                     error_type = Error.InternalError "kernel did not accept proof\n";
                   })
          with KExceptions.TypeError msg ->
            raise
              (Error.ElabError
                 {
                   context = { loc = Some d.name_loc; decl_name = Some d.name };
                   error_type = Error.KernelError { kernel_exn = msg };
                 }))
    | Axiom ->
        if Hashtbl.mem e.env d.name then
          raise
            (Error.ElabError
               {
                 context = { loc = Some d.name_loc; decl_name = Some d.name };
                 error_type = Error.AlreadyDefined d.name;
               })
        else
          create_metas e d.ty [];
          check_is_type e d.ty;
          (* replace_metas only fills in metavariables *)
          let ty_filled = replace_metas e d.ty in
          Hashtbl.clear e.metas;
          (* conv_to_kterm does a straightforward variant-to-variant conversion *)
          let ty_k = conv_to_kterm ty_filled in
          Hashtbl.add e.env d.name { name = d.name; ty = ty_filled; data = Axiom };
          Hashtbl.add e.kenv d.name ty_k
  with Error.ElabError x ->
    raise
      (Error.ElabError { x with context = { x.context with decl_name = Some d.name } })
