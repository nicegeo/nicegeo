# System E Kernel

A typechecker kernel for a proof system based on the formal system **E** (Euclid’s Elements). The file `proof.txt` contains an example proof.

- Dependent type theory (no inductive types)
- All the built-in types and rules from System E
(like Point and Circle)

## Build the project and run tests
First, install OCaml and opam and then create a switch for the project.
```bash
opam init
opam switch create nicegeo 5.4.1
eval $(opam env --switch=nicegeo)
```

Install the dependency:
```bash
opam install --deps-only --with-test .
```

Build the project:
```bash
dune build
```

Run the kernel on the test file:
```bash
dune exec system-e-kernel proof.txt
```

## Running Tests

```bash
dune runtest
```

## Project Structure
- `bin/main.ml` is the entry point. It reads in the proofs from the file and checks if it is correct.
- `kernel/` contains the trusted type checking logic. 
	- `kernel/infer.ml` defines the `inferType` and `isDefEq` functions.
	- `kernel/term.ml` defines the basic kernel-level `term` types.
- `elab/` is a layer on top of the kernel with many usability features separate from the kernel. It handles
  parsing, automatically filling holes inserted by the user, and has its own typechecking logic. It ultimately
  produces a kernel-level term (that should represent what the user intended to some degree) for the kernel to check. 
	- `elab/elab.ml` contains the main interface of the layer: creating a context, adding the axioms in `env.txt`,
	  and checking parsed proofs. 
	- `elab/typecheck.ml` contains the type checking and unification logic for automatically filling holes, and
	  calls the kernel to check the final produced term.
	- `elab/lexer.mll` and `elab/parser.mly` define the grammar for the text file parser. 
