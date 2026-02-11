# System E Kernel

A typechecker kernel for a proof system based on the formal system **E** (Euclid’s Elements). The file `proof.txt` contains an example proof.

- Dependent type theory (no inductive types)
- All the built-in types and rules from System E
(like Point and Circle)

## Using the kernel
First, install OCaml and opam.
Initialize opam with
```bash
opam init
eval $(opam env)
```

Install the dependency:
```bash
opam install dune menhir
```

Build the project:
```bash
dune build
```

Run the kernel on the test file:
```bash
dune exec system-e-kernel proof.txt
```