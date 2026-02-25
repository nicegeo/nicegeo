open Kernel_exn_format
module KExceptions = System_e_kernel.Exceptions
module KTerm = System_e_kernel.Term
module E = Error



let locals_to_pairs (ctx : KTerm.localcontext) : (string * string) list =
  (* ctx is a Hashtbl: string -> term *)
  Hashtbl.fold (fun k v acc -> (k, term_to_string v) :: acc) ctx []

let raise_as_elab_error ?decl_name (exn : exn) : 'a =
  match exn with
  | KExceptions.TypeError info ->
      let ec =
        E.empty_context
        |> (fun c -> match decl_name with None -> c | Some d -> E.with_decl_name d c)
        |> E.with_term_name (term_to_string info.trm)
        |> E.with_local_context (locals_to_pairs info.ctx)
        |> E.with_note (type_err_to_string info)
      in
      (* Pick ONE final exception kind in your layer: *)
      E.raise_type_error ~error_context:ec "Kernel type error"
  | KExceptions.RedError info ->
      let ec =
        E.empty_context
        |> (fun c -> match decl_name with None -> c | Some d -> E.with_decl_name d c)
        |> E.with_term_name (term_to_string info.trm)
        |> E.with_local_context (locals_to_pairs info.ctx)
        |> E.with_note (red_err_to_string info)
      in
      (* Either map to KernelError or TypeError—your choice *)
      E.raise_kernel_error ~error_context:ec "Kernel reduction error"
  | _ ->
      E.raise_internal "Non-kernel exception escaped into kernel_to_elab_error"


(*how to use: Anywhere in the elab where we call kernel infer/reduction:
      try
       Kernel.infer env ctx t
      with e ->
       Kernel_to_elab_error.raise_as_elab_error ~decl_name:"myDecl" e)
       *)
       