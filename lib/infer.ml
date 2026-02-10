open Term

(* Substitute the bound variable at index `bvar_idx` (relative to the top level
term, so what would have been at index `bvar_idx` in the localcontext stack for
the original term) with the provided value `bvar_val` in the term `t`*)
let rec subst_bvar (t: term) (bvar_idx: int) (bvar_val: term) : term = 
  match t with
    | Const _ | Sort _ | Fvar _ -> t
    | Bvar idx -> if bvar_idx = idx then bvar_val else Bvar idx
    | Lam (domain_type, body) -> 
        (* Add 1 to bvar_idx to account for the fact that a Lam introduces a bound
        variable *)
        Lam (subst_bvar domain_type bvar_idx bvar_val, subst_bvar body (bvar_idx + 1) bvar_val)
    | Forall (domain_type, ret_type) ->
        Forall (subst_bvar domain_type bvar_idx bvar_val, subst_bvar ret_type (bvar_idx + 1) bvar_val)
    | App (func, arg) -> 
        let func_subst = subst_bvar func bvar_idx bvar_val in
        let arg_subst = subst_bvar arg bvar_idx bvar_val in
        App (func_subst, arg_subst)

(* In the term t, converts a free variable fvar_name to a bound variable with index 
bvar_idx relative to the top level. Replaces all `FVar fvar_name` references with the
appropriate `Bvar idx` reference. This will return a term that by itself will have 
out-of-bounds Bvar references, so it should be placed in an appropriate Lam/Forall 
to be valid. *)
let rec rebind_bvar (t: term) (bvar_idx: int) (fvar_name: string) : term = 
  match t with
    | Const _ | Sort _  | Bvar _ -> t
    | Fvar name -> if fvar_name = name then Bvar bvar_idx else t
    | Lam (domain_type, body) -> 
        (* Add 1 to bvar_idx to account for the fact that a Lam introduces a bound
        variable *)
        Lam (rebind_bvar domain_type bvar_idx fvar_name, rebind_bvar body (bvar_idx + 1) fvar_name)
    | Forall (domain_type, ret_type) ->
        Forall (rebind_bvar domain_type bvar_idx fvar_name, rebind_bvar ret_type (bvar_idx + 1) fvar_name)
    | App (func, arg) -> 
        let func_subst = rebind_bvar func bvar_idx fvar_name in
        let arg_subst = rebind_bvar arg bvar_idx fvar_name in
        App (func_subst, arg_subst)

let fvar_counter = ref 0
let gen_new_fvar_name () : string = 
  let name = "fvar" ^ string_of_int !fvar_counter in
  incr fvar_counter;
  name

let rec term_to_string (t : term) : string =
  match t with
  | Const name -> "Const " ^ name
  | Sort level -> "Sort " ^ string_of_int level
  | Fvar name -> "Fvar " ^ name
  | Bvar idx -> "Bvar " ^ string_of_int idx
  | Lam (dom, body) -> "Lam (" ^ term_to_string dom ^ ", " ^ term_to_string body ^ ")"
  | Forall (dom, body) -> "Forall (" ^ term_to_string dom ^ ", " ^ term_to_string body ^ ")"
  | App (f, a) -> "App (" ^ term_to_string f ^ ", " ^ term_to_string a ^ ")"

let context_to_string (ctx : localcontext) : string =
  Hashtbl.fold (fun k v acc -> acc ^ k ^ " : " ^ term_to_string v ^ "\n") ctx ""

let rec inferType (env : environment) (localCtx : localcontext) (t : term) : term =
  match t with
  | Const name -> (
      try Hashtbl.find env name
      with Not_found -> failwith ("unknown constant: " ^ name)
    )
  | Fvar name -> (
      try Hashtbl.find localCtx name
      with Not_found -> failwith ("unknown free variable: " ^ name)
    )
  | Bvar idx -> (
      failwith ("bound variable index out of scope: " ^ string_of_int idx)
    )
  | App (func, arg) -> (
    let func_type = inferType env localCtx func in
    let inferred_arg_type = inferType env localCtx arg in
    match func_type with
      | Forall (expected_arg_type, return_type) -> 
          (* TODO: replace this with checking for definitional equality *)
        if expected_arg_type = inferred_arg_type then
          (* TODO: check if this is the right approach *)
          (* The actual type of the function application can depend on the
          actual value that it's evaluated at so we need to substitute the arg
          for any bvars referring to this arg in the return_type. *)
          subst_bvar return_type 0 arg
        else 
          let msg = 
            Printf.sprintf 
              "Function called with invalid argument type.\n\
               Local Context:\n%s\n\
               Term: %s\n\
               Func: %s\n\
               Arg: %s\n\n\
               Expected Arg Type: %s\n\
               Inferred Arg Type: %s\n"
              (context_to_string localCtx)
              (term_to_string t)
              (term_to_string func)
              (term_to_string arg)
              (term_to_string expected_arg_type)
              (term_to_string inferred_arg_type)
          in
          print_endline msg;
          failwith "Function called with invalid argument type"
      | _ -> failwith "Tried to apply non-function to an argument"
  )
  | Lam (domainType, body) -> (
      let new_fvar_name = gen_new_fvar_name () in
      (* add mapping new_fvar_name -> domainType to localCtx in recursive call *)
      (* this is fine because domainType won't have any unresolved BVars *)
      let newLocalCtx = 
        let t = Hashtbl.copy localCtx in
        Hashtbl.replace t new_fvar_name domainType;
        t
      in
      (* replace bound variable with new free variable *)
      let substed_term = subst_bvar body 0 (Fvar new_fvar_name) in
      let ret_type = inferType env newLocalCtx substed_term in
      (* replace the free variable with bound variable *)
      let rebound_type = rebind_bvar ret_type 0 new_fvar_name in
      Forall (domainType, rebound_type)
    )
  | Forall (domainType, returnType) -> (
      let domainTypeType = inferType env localCtx domainType in
      let returnTypeType = 
        let new_fvar_name = gen_new_fvar_name () in
        let newLocalCtx = 
          let t = Hashtbl.copy localCtx in
          Hashtbl.replace t new_fvar_name domainType;
          t
        in
        let substed_return_type = subst_bvar returnType 0 (Fvar new_fvar_name) in
        inferType env newLocalCtx substed_return_type in
      match (domainTypeType, returnTypeType) with
        | (Sort u, Sort v) -> (
          if v = 0 then Sort 0  (* Prop is impredicative *)
          else Sort (max u v)
        )
        | (Sort _, _) -> failwith "Return type of a Forall must be a sort"
        | (_, Sort _) -> failwith "Domain type of a Forall must be a sort"
        | _ -> failwith "Domain and return types of a Forall must be sorts"
    )
  | Sort level -> Sort (level + 1)

(* Create an expression where func is applied to all arguments in order *)
(* Ex: f a b c -> App(App (App (f, a), b), c) *)
let application_multiple_arguments (func: term) (args: term list): term = 
  List.fold_left
    (fun application_so_far first_arg -> App (application_so_far, first_arg))
    func
    args

let mk_axioms_env () =
  let env = Hashtbl.create 16 in
  Hashtbl.add env "Point" (Sort 1);
  Hashtbl.add env "Line" (Sort 1);
  Hashtbl.add env "Circle" (Sort 1);

  Hashtbl.add env "Exists.elim" (
    Forall (Sort 1, (* A: Type *)
    Forall (Forall (Bvar 0, Sort 0), (* p: A -> Prop *)
    Forall (Sort 0, (* b: Prop *)
    Forall (App (App (Const "Exists", Bvar 2), Bvar 1), (* e: Exists A p *)
    Forall ( (* h: Forall (a: A) (Forall (App p a) b) *)
      Forall (Bvar 3, (* a: A *)
      Forall (App (Bvar 3, Bvar 0), (* App p a *)
      Bvar 3)), (* b *)
    Bvar 2 (* b *)
  ))))));

  (* TODO: should Const "Type" be replaced with Sort 1 or something like that? *)
  Hashtbl.add env "Eq" (
    Forall (Sort 1,
      (Forall (Bvar 0, Forall (Bvar 1, Const "Prop")))
    )
  );
  (* Eq: (A: Type) -> a: A -> b: A -> Prop *)

  Hashtbl.add env "Eq.intro" (
    Forall (Sort 1, 
      Forall (Bvar 0,
        application_multiple_arguments (Const "Eq") [Bvar 1; Bvar 0; Bvar 0]
      )
    )
  );

  Hashtbl.add env "Eq.elim" (
    Forall (Sort 1, (* A: Type *)
    Forall (Bvar 0, (* a: A *)
    Forall (Forall (Bvar 1, Const "Prop"), (* motive: A -> Prop *)
    Forall (App (Bvar 0, Bvar 1), (* refl: motive a *)
    Forall (Bvar 3, (* b: A *)
    Forall (
      (* eq: Eq A a b *)
      application_multiple_arguments (Const "Eq") [Bvar 4; Bvar 3; Bvar 0], 
      (* motive b *)
      App (Bvar 3, Bvar 1)
    ))))))
  );
  env

(* 
Eq.elim A a (fun (b: A) -> b=a) (Eq.intro A a : a=a) b (h: Eq A a b) : b = a
*)