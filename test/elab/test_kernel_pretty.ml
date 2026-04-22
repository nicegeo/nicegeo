open Elab.Kernel_pretty

let test_kernel_sort_names () =
  Alcotest.check'
    Alcotest.string
    ~msg:"Sort 0 pretty-prints as Prop"
    ~expected:"Prop"
    ~actual:(term_to_string_pretty (Kernel.Term.Sort 0));

  Alcotest.check'
    Alcotest.string
    ~msg:"Sort 1 pretty-prints as Type"
    ~expected:"Type"
    ~actual:(term_to_string_pretty (Kernel.Term.Sort 1))

let suite =
  let open Alcotest in
  ( "Kernel Pretty-printing",
    [ test_case "Kernel sort names" `Quick test_kernel_sort_names ] )
