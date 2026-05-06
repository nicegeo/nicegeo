NiceGeo is a type-theory-based synthetic Euclidean geometry proof assistant. Its axiomatic system is based on System E, with significant inspiration from formalizations of System E in other proof assistants, like LeanEuclid. The project combines a trusted proof kernel, synthetic geometry foundations, an elaboration layer, and an interactive tactic framework to support formal geometric reasoning in a more intuitive and educational way. The "Nice" in NiceGeo reflects an overarching design philosophy on our part, in which we aim to have the proof assistant always give kind and helpful feedback.

The system is designed around a layered architecture where all proofs are ultimately verified by a small trusted kernel (the de Bruijn criterion), with an exhaustively-tested synthetic geometry layer sitting just above that kernel. Higher-level components such as tactics, automation, proof states, and future visualization interfaces improve usability and interaction.

NiceGeo was initially deisgned and implemented as a whole-course-project, through the effort of the entire class ([Build Your Own Proof Assistant, UIUC](https://dependenttyp.es/classes/598sp2026.html)). It is now open to contributions from the rest of the world. See [CONTRIBUTING.md](./CONTRIBUTING.md) to contribute!

# Features

## Implemented

- Dependent-type-theory-based proof kernel
- Exhaustively tested synthetic Euclidean geometry foundations (axiomatization of System E)
- Tactic-based interactive proofs
- Hole creation and automatic hole filling
- Bidirectional type checking and unification
- Proof state management
- Custom tactic framework
- Pretty-printing and error reporting
- Kind error messages
- Standard library (Euclib) for Euclidean geometry
- VSCode IDE plugin with many novel usability features
- Some geometry-specific proof automation

The E-based foundations are documented in [METATHEORY.md](./METATHEORY.md).

## What's Next

- Interactive visual proofs
- Tabular proofs
- More geometry-specific automation
- More advanced automation
- Interactive visual proofs
- Stronger IDE integration
- Expansions to Euclib

Please see our GitHub issues for more!

# Getting Started

Want to try out NiceGeo? Then pull the code in this repository, build it, and install the VSCode plugin.

## Building NiceGeo

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

To make sure it works, run the tests:

```bash
dune runtest
```

## Running NiceGeo via Command Line:

You can check a NiceGeo proof file via the command line as follows:

```bash
dune exec nicegeo file.ncg
```

Example:

```bash
dune exec nicegeo euclib/euclib.ncg
```

## The NiceGeo IDE

If you plan to do any serious NiceGeo development, you probably want to download our IDE. This is a VSCode plugin (with a `.vsix` extension) that can be found in the `ide` folder. Simply right-click it and install it from within VSCode. Further instructions can be found in the IDE.

# Project Structure

Below we detail our code structure a bit more.

## `kernel/`

Trusted core of the system responsible for proof checking. This has been extensively human-vetted, though further vetting is always welcome.

Main components include:
- Type inference
- Definitional equality checking
- Reduction and normalization
- Core term language

## `synthetic/`

Synthetic geometry environment, encoding our interpretation of the axioms from System E, as well as any primitives needed for stating and using these axioms. This sits just above the kernel in terms of trust. The elaboration of the synthetic letter is exhaustively tested, and the axioms themselves have been extensively human-vetted.

Contains:
- Primitives
- Axioms
- Geometry environment setup
- Exhaustive regression tests for elaboration of the above

## `elab/`

Elaboration layer, inspired by Lean's view of elaboration (although not nearly as liberal as Lean's).
This gets between the nicer-looking terms and types that users see, and the full terms and types that the kernel checks in the end.
Bugs in the elaborator layer cannot make it possible to prove false (unlike bugs in the kernel and synthetic layers),
but they can mislead the user. This is the lowest layer at which we welcome vibecoded/AI-aided contributions.

Handles:
- Parsing and lexing
- Bidirectional type checking
- Metavariables / holes
- Unification
- Some reduction
- Conversion to kernel terms
- Pretty-printing and diagnostics

## `automation/`

Interactive tactic framework and proof automation infrastructure.

Includes:
- Tactic definitions
- Proof state transformations
- Tactical combinators
- User-facing tactic error messages
- Automation utilities

Current tactics include functionality similar to:
- `intro`
- `apply`
- `exact`
- `rewrite`
- `split`
- `have`
- `refl`
- `exists`
- `lia`
- `sorry` or `admit`

There are also some geometry-specific tactics. Documentation of all available tactics can be found in this file
when tactics are registered, as well as in the IDE through the combined auto-complete and hover functionalities.

## `euclib/`

Euclidean geometry standard library.

Contains:
- Some simple geometry lemmas and theorems
- Some of Euclid's propositions
- Construction helpers

The long-term goal is formalization of Euclid’s Book I propositions, plus anything else that might be useful to anyone
who wants to do Euclidean geometry using NiceGeo. Contributions to Euclib to this end are strongly welcome, and are a great
way to test out NiceGeo.

## `test/`

Unit tests and tactic tests for the system. All new features should come with accompanying tests. Please feel free to add tests where you see any currently missing.

## `bin/`

Executable entry point and command-line interface, following the standard OCaml convention.

## `ide/`

IDE and editor integration support for interactive proof development.

This layer is intended to improve usability and accessibility by providing:
- Proof state visualization
- Context and goal display
- Expandable display of metavariables and their constraints for debugging
- Better diagnostics and error reporting
- Hover/info views
- Autocomplete
- Integration with tactic execution and proof interaction

While the IDE is currently under development, it already includes many novel features. We welcome contributions to the IDE. We also welcome the creation of new GitHub issues suggesting improvements to or documenting bugs in the IDE.
