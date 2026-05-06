# NiceGeo

NiceGeo is a tactic-based geometry proof assistant inspired by Euclidean geometry systems such as LeanEuclid and System E. The project combines a trusted proof kernel, an elaboration layer, synthetic geometry foundations, and an interactive tactic framework to support formal geometric reasoning in a more intuitive and educational way.

The system is designed around a layered architecture where all proofs are ultimately verified by a small trusted kernel, while higher-level components such as tactics, automation, proof states, and future visualization interfaces improve usability and interaction.

---

## Features

- Dependent type theory based proof kernel
- Synthetic Euclidean geometry foundations
- Tactic-based interactive proofs
- Hole creation and automatic hole filling
- Bidirectional type checking and unification
- Proof state management
- Custom tactic framework
- Pretty-printing and error reporting
- Modular standard library for geometry
- Extensible architecture for automation and IDE integration

---

# Project Structure

## `kernel/`

Trusted core of the system responsible for soundness and proof verification.

Main components include:
- Type inference
- Definitional equality checking
- Reduction and normalization
- Core term language

Important files:
- `infer.ml`
- `term.ml`
- `exceptions.ml`


## `elab/`

Elaboration and frontend layer built on top of the kernel.

Handles:
- Parsing and lexing
- Bidirectional type checking
- Metavariables / holes
- Unification
- Reduction
- Conversion to kernel terms
- Pretty-printing and diagnostics

Important files:
- `typecheck.ml`
- `convert.ml`
- `reduce.ml`
- `pretty.ml`
- `nice_messages.ml`
- `interface.ml`
- `parser.mly`
- `lexer.ml`


## `automation/`

Interactive tactic framework and proof automation infrastructure.

Includes:
- Tactic definitions
- Proof state transformations
- Tactical combinators
- User-facing tactic error messages
- Automation utilities

Important files:
- `tactics.ml`
- `tactic_error_messages.ml`
- `proofstate.ml`

Current tactics include functionality similar to:
- `intro`
- `apply`
- `exact`
- `rewrite`
- `split`
- `have`
- `refl`
- `exists`


## `synthetic/`

Synthetic geometry environment and foundational geometry declarations.

Contains:
- Primitive geometry objects
- Axioms
- Geometry environment setup


## `euclib/`

Standard Euclidean geometry library.

Contains reusable:
- Geometry lemmas
- Theorems
- Euclidean propositions
- Construction helpers

The long-term goal is formalization of Euclid’s Book I propositions.


## `test/`

Unit tests and tactic tests for the system.

Includes tests for:
- Kernel behavior
- Elaboration
- Pretty-printing
- Tactics
- Proof state transitions
- Automation utilities


## `bin/`

Executable entry point and command-line interface.

Main file:
- `main.ml`


## `ide/`

IDE and editor integration support for interactive proof development.

This layer is intended to improve usability and accessibility by providing:
- Proof state visualization
- Context and goal display
- Better diagnostics and error reporting
- Hover/info views
- Future LSP-style features
- Integration with tactic execution and proof interaction

The long-term goal is to support a more interactive geometry proving experience similar to modern proof assistants such as Lean.

----


# Building the Project

## Requirements

- OCaml
- opam
- dune

Create the project switch:

```bash
opam init
opam switch create nicegeo 5.4.1
eval $(opam env --switch=nicegeo)
```

Install dependencies:

```bash
opam install --deps-only --with-test .
```

Build the project:

```bash
dune build
```


# Running NiceGeo

Run a proof file:

```bash
dune exec nicegeo file.ncg
```

Example:

```bash
dune exec nicegeo euclib/euclib.ncg
```


# Running Tests

```bash
dune runtest
```


# Current Development

Some actively developed features include:

- Better tactic automation
- User-written tactics
- Improved proof state visualization
- Enhanced error reporting
- IDE/LSP support
- Info views and hover support

---

# Design Philosophy

NiceGeo separates the trusted kernel from higher-level automation and interfaces. This allows advanced features such as tactics, automation, and future graphical proof systems while preserving logical soundness through kernel verification.

The project aims to make formal geometry proofs more approachable while still maintaining rigorous proof checking.

---

# Example Areas of the Codebase

| Area | Purpose |
|---|---|
| `kernel/` | Trusted proof checking |
| `elab/` | Elaboration and type checking |
| `automation/` | Tactics and proof automation |
| `synthetic/` | Geometry foundations |
| `euclib/` | Euclidean theorem library |
| `test/` | Tests and validation |

---

# Future Work

Planned future extensions include:

- Geometry-specific automation
- Interactive visual proofs
- Diagram-based proof construction
- Tabular proofs
- Stronger IDE integration
- Expanded Euclidean standard library
- Additional tactic combinators and tacticals

---

# Acknowledgements

This project draws inspiration from:
- LeanEuclid
- System E
- Interactive theorem provers and geometry proof systems

---

# Course Project

This project was deisgned and completed as a course (Build Your Own Proof Assistant,CS 598, UIUC).

[Course link](https://dependenttyp.es/classes/598sp2026.html)



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
dune exec nicegeo proof.ncg
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
	- `elab/interface.ml` contains the main interface of the layer: creating a context, adding the axioms in `synthetic/env.ncg`,
	  and checking parsed proofs. 
	- `elab/typecheck.ml` contains the type checking and unification logic for automatically filling holes, and
	  calls the kernel to check the final produced term.
	- `elab/lexer.ml` (implemented with sedlex) and `elab/parser.mly` define the grammar for the text file parser. 
