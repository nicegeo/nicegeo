# NiceGeo IDE Extension Usage Guide

This guide explains how to install the extension, what features it provides, and what to expect while using it.
Current version of the extension: `0.2.0`

## 0) Install required dependency

- Install all project dependencies in your active opam switch:
  - `opam install --deps-only --with-test .`

## Sections

- Install the extension
- Open a NiceGeo file
- Feature 1: Diagnostics
- Feature 2: Autocompletion
- Feature 3: Proof Mode
- Quick test files

## 1) Install the extension

- In VS Code, open the Command Palette.
- Run: `Extensions: Install from VSIX...`
- Select the file at: `ide/nicegeo-ide-0.2.0.vsix`
- Reload VS Code if prompted.

## 2) Open a NiceGeo file

- Open any `.ncg` file.
- Example files are available in: `ide/examples/`

---

## 3) Feature 1: Diagnostics

Diagnostics show parsing/typechecking errors directly in the editor.

### How to use

- Open a `.ncg` file and edit/save it.
- Run manually from Command Palette if needed:
  - `NiceGeo: Run Diagnostics`
  - `NiceGeo: Show Diagnostics Output`

### What to expect

- Errors appear as editor diagnostics.
- Diagnostics can run on save or on type (based on settings).
- If tooling is missing (`dune`/`opam`), messages explain what to install/run.

---

## 4) Feature 2: Autocompletion

Autocomplete is context-aware and includes language syntax + proof context.

### How to use

- Trigger completion with `Ctrl+Space` (or your VS Code completion shortcut).
- It works in normal files and proof scripts.
- Toggle via setting:
  - `nicegeo.completion.enable` (default: `true`)

### What to expect

- **Keyword/directive suggestions**: `Theorem`, `Definition`, `#check`, etc.
- **Tactic suggestions** inside proof blocks (`Proof.` ... `Qed.`), with higher priority at tactic line positions.
- **Context suggestions** in proofs: local hypotheses, relevant environment names, and metas.
- **Declaration-name position behavior**:
  - After `Theorem ` / `Definition ` / `Axiom `, completion prioritizes reusable names and avoids noisy keyword lists.

---

## 5) Feature 3: Proof Mode

Proof Mode enables rich proof-state tracking at the cursor.

### How to use

- Enter Proof Mode:
  - Command Palette: `NiceGeo: Enter Proof Mode`
  - or status bar toggle
- Move cursor inside a theorem proof block.
- Open NiceGeo sidebar and view **Proof State** panel.

### What to expect

- Proof-state updates are active only when Proof Mode is ON.
- Tactics are applied incrementally up to cursor position.
- Sidebar shows:
  - Global environment
  - Metas (open/solved)
  - Goal parameters / hypotheses / goal
  - Term context at cursor
  - Tactic progress
  - Open goals (if multiple)
- Cursor behavior:
  - before tactic end: tactic not applied
  - at/after tactic end: tactic applied
  - at/after `Qed`: full script treated as applied