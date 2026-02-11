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
        if definitional_eq env localCtx expected_arg_type inferred_arg_type then
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
          failwith msg
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
        | _ -> 
          let msg = 
            Printf.sprintf 
              "Domain and return types of a Forall must be sorts.\n\
               Local Context:\n%s\n\
               Term: %s\n\
               Domain Type Sort: %s\n\
               Return Type Sort: %s\n\n"
              (context_to_string localCtx)
              (term_to_string t)
              (term_to_string domainTypeType)
              (term_to_string returnTypeType)
          in
          failwith msg
    )
  | Sort level -> Sort (level + 1)

and definitional_eq (env : environment) (localCtx : localcontext) (t1 : term) (t2 : term) : bool =
  let t1_reduced = reduce env localCtx t1 in
  let t2_reduced = reduce env localCtx t2 in
  t1_reduced = t2_reduced

and reduce (env : environment) (localCtx : localcontext) (t : term) : term =
  match t with
  | App (Lam (domainType, body), arg) -> (* beta reduction i think *)
      let arg_type = inferType env localCtx arg in
      if domainType = arg_type then
        let substed_body = subst_bvar body 0 arg in
        reduce env localCtx substed_body
      else
        failwith "Function called with invalid argument type during reduction"
  | App (func, arg) -> 
      let reduced_func = reduce env localCtx func in
      let reduced_arg = reduce env localCtx arg in
      App (reduced_func, reduced_arg)
  | Lam (domainType, body) -> 
    (* need to subst fvar *)
    let new_fvar_name = gen_new_fvar_name () in
    let domainTypeReduced = reduce env localCtx domainType in
    let newLocalCtx = 
      let t = Hashtbl.copy localCtx in
      Hashtbl.replace t new_fvar_name domainTypeReduced;
      t
    in
    let substed_body = subst_bvar body 0 (Fvar new_fvar_name) in
    let bodyReduced = reduce env newLocalCtx substed_body in
    Lam (domainTypeReduced, rebind_bvar bodyReduced 0 new_fvar_name)
  | Forall (domainType, returnType) -> 
    let new_fvar_name = gen_new_fvar_name () in
    let domainTypeReduced = reduce env localCtx domainType in
    let newLocalCtx = 
      let t = Hashtbl.copy localCtx in
      Hashtbl.replace t new_fvar_name domainTypeReduced;
      t
    in
    let substed_return_type = subst_bvar returnType 0 (Fvar new_fvar_name) in
    let returnTypeReduced = reduce env newLocalCtx substed_return_type in
    Forall (domainTypeReduced, rebind_bvar returnTypeReduced 0 new_fvar_name)
  | _ -> t

(* Create an expression where func is applied to all arguments in order *)
(* Ex: f a b c -> App(App (App (f, a), b), c) *)
let application_multiple_arguments (func: term) (args: term list): term = 
  List.fold_left
    (fun application_so_far first_arg -> App (application_so_far, first_arg))
    func
    args

let mk_axioms_env () =
  let env = Hashtbl.create 16 in
  (* Built-in geometric types *)
  Hashtbl.add env "Point" (Sort 1);
  Hashtbl.add env "Line" (Sort 1);
  Hashtbl.add env "Circle" (Sort 1);
  (* Empty: Type — the empty type (no inhabitants); used for negation (¬P = P -> Empty) *)
  Hashtbl.add env "Empty" (Sort 1);
  (* Empty.elim: (C : Type) -> Empty -> C — ex falso quodlibet: from a proof of Empty, derive any C *)
  let empty_elim_type =
    (* (C : Type) *)
    Forall (Sort 1,
      (* (e : Empty) -> C *)
      Forall (Const "Empty", Bvar 1))
  in
  Hashtbl.add env "Empty.elim" empty_elim_type;

  (* And: (A : Prop) -> (B : Prop) -> Prop — conjunction of two propositions *)
  let and_type =
    Forall (Sort 0, Forall (Sort 0, Sort 0))
  in
  Hashtbl.add env "And" and_type;

  (* And.intro: (A : Prop) -> (B : Prop) -> (a : A) -> (b : B) -> And A B *)
  let and_intro_type =
    Forall (Sort 0,
      Forall (Sort 0,
        Forall (Bvar 1, (* A *)
          Forall (Bvar 2, (* B *)
            App (App (Const "And", Bvar 3), Bvar 2)))))
  in
  Hashtbl.add env "And.intro" and_intro_type;

  (* And.elim: (A : Prop) -> (B : Prop) -> (C : Type) -> (f : A -> B -> C) -> (h : And A B) -> C *)
  let and_elim_type =
    Forall (Sort 0,
      Forall (Sort 0,
        Forall (Sort 1,
          Forall (Forall (Bvar 4, Forall (Bvar 3, Bvar 2)),
            Forall (App (App (Const "And", Bvar 4), Bvar 3), Bvar 2)))))
  in
  Hashtbl.add env "And.elim" and_elim_type;

  (* Exists.elim from main branch:
     (A : Type) -> (p : A -> Prop) -> (b : Prop) ->
     (e : Exists A p) ->
     (h : Forall (a : A), p a -> b) ->
     b
  *)
  Hashtbl.add env "Exists.elim"
    (Forall (Sort 1,                         (* A : Type *)
      Forall (Forall (Bvar 0, Sort 0),       (* p : A -> Prop *)
        Forall (Sort 0,                      (* b : Prop *)
          Forall (App (App (Const "Exists", Bvar 2), Bvar 1),  (* e : Exists A p *)
            Forall (
              Forall (Bvar 3,                (* a : A *)
                Forall (App (Bvar 4, Bvar 0), (* p a *)
                  Bvar 3)),                  (* b *)
              Bvar 2))))));                  (* result: b *)

  Hashtbl.add env "Eq" (
    Forall (Sort 1,
      (Forall (Bvar 0, Forall (Bvar 1, Sort 0)))
    )
  );
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
    Forall (Forall (Bvar 1, Sort 0), (* motive: A -> Prop *)
    Forall (App (Bvar 0, Bvar 1), (* refl: motive a *)
    Forall (Bvar 3, (* b: A *)
    Forall (
      (* eq: Eq A a b *)
      application_multiple_arguments (Const "Eq") [Bvar 4; Bvar 3; Bvar 0], 
      (* motive b *)
      App (Bvar 3, Bvar 1)
    ))))))
  );
  
  (* Length (magnitude) axioms *)
  Hashtbl.add env "Len" (Sort 1);
  (* There exists a total order "Lt" on Len *)
  Hashtbl.add env "Lt" (Forall (Const "Len", Forall (Const "Len", Sort 0)));
  Hashtbl.add env "LtTrans" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    Forall (Const "Len", (* c : Len -> *)
    Forall (App (App (Const "Lt", Bvar 2), Bvar 1), (* Lt a b -> *)
    Forall (App (App (Const "Lt", Bvar 2), Bvar 1), (* Lt b c -> *)
    (App (App (Const "Lt", Bvar 4), Bvar 2)) (*Lt a c *)
  ))))));
  Hashtbl.add env "LtTricot" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    (App (App (Const "Or", (*Lt a b \/ *)
      App (App (Const "Lt", Bvar 1), Bvar 0)),
      (App (App (Const "Or", (* Lt b a \/ Eq Len a b *)
        App (App (Const "Lt", Bvar 0), Bvar 1)),
        App (App (App (Const "Eq", Const "Len"), Bvar 1), Bvar 0)
      ))
    ))
  )));
  (* There exists an element zero of len that is the least of sort len *)
  Hashtbl.add env "Zero" (Const "Len");
  Hashtbl.add env "ZeroLeast" (
    Forall (Const "Len", (* a : Len -> *)
    App (App (Const "Or", (*Lt Zero a \/ Eq Len Zero a *)
      App (App (Const "Lt", Const "Zero"), Bvar 0)),
      App (App (App (Const "Eq", Const "Len"), Const "Zero"), Bvar 0))
    )
  );
  (* There is an operation Add on Len which is commutative and associative *)
  Hashtbl.add env "Add" (Forall (Const "Len", Forall (Const "Len", Const "Len")));
  Hashtbl.add env "AddComm" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    (App (App (App (Const "Eq", Const "Len"), (* Add a b = Add b a *)
      App (App (Const "Add", Bvar 1), Bvar 0)),
      App (App (Const "Add", Bvar 0), Bvar 1)
    ))
  )));
  Hashtbl.add env "AddAssoc" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    Forall (Const "Len", (* c : Len -> *)
    (App (App (App (Const "Eq", Const "Len"), (* Add (Add a b) c = Add a (Add b c) *)
      App (App (Const "Add",
        App (App (Const "Add", Bvar 2), Bvar 1)), (* Add a b *)
        Bvar 0 (* c *)
      )),
      App (App (Const "Add",
        Bvar 2), (* a *)
        App (App (Const "Add", Bvar 1), Bvar 0) (* Add b c *)
      )
    ))
  ))));
  Hashtbl.add env "AddZero" (
    Forall (Const "Len", (* a : Len -> *)
    (App (App (App (Const "Eq", Const "Len"), (* Eq Len (Add Zero a) a*)
      App (App (Const "Add", Const "Zero"), Bvar 0)),
      Bvar 0
    )) 
  ));
  Hashtbl.add env "LtAdd" (
    Forall (Const "Len", (* a : Len -> *)
    Forall (Const "Len", (* b : Len -> *)
    Forall (Const "Len", (* c : Len -> *)
    Forall (App (App (Const "Lt", Bvar 2), Bvar 1), (* Lt a b -> *)
    (App (App (Const "Lt", (* Lt (Add a c) (Add b c) *)
      App (App (Const "Add", Bvar 3), Bvar 1)), (* note that we increment the indices *)
      App (App (Const "Add", Bvar 2), Bvar 1)
    ))
  )))));
  Hashtbl.add env "Length" (Forall (Const "Point", Forall (Const "Point", Const "Len")));
  
  (* TODO: should Const "Type" be replaced with Sort 1 or something like that? *)
  Hashtbl.add env "Eq" (
    Forall (Sort 1,
      (Forall (Bvar 0, Forall (Bvar 1, Sort 0)))
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
    Forall (Forall (Bvar 1, Sort 0), (* motive: A -> Prop *)
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