# NiceGeo IDE Extension Usage Guide

This is a short guide for using the NiceGeo IDE extension.

## 0) Install required dependency

- NiceGeo relies on `sedlex` in your active opam switch.
- Install it with:
  - `opam install sedlex`

## 1) Install the extension from `.vsix`

- In VS Code, open the Command Palette.
- Run: `Extensions: Install from VSIX...`
- Select the file at: `ide/nicegeo-ide-0.1.0.vsix`
- Reload VS Code if prompted.

## 2) Open a NiceGeo file

- Open any `.ncg` file in VS Code.
- Make sure the NiceGeo extension is installed/enabled.
- To get started quickly, use example files from: `ide/examples/`

## 3) Enter Proof Mode

- Turn on **Proof Mode** from:
  - command palette: `NiceGeo: Enter Proof Mode`, or
  - status bar toggle.
- Proof-state updates are active only when Proof Mode is ON.

## 4) Move cursor inside a proof

- Place the cursor inside a theorem `Proof ... Qed` block.
- The IDE runs tactics **incrementally up to the cursor** (prefix execution).
- You can move line-by-line to inspect intermediate states.

## 5) Read the Proof sidebar

In the NiceGeo sidebar, you will see:

- **Global environment** (known names/types before the declaration)
- **Metas** (open/solved holes)
- **Goal parameters / hypotheses / goal**
- **Term context (at cursor)** when applicable
- **Tactic progress** (executed vs remaining, with step outcomes)
- **Open goals** when more than one goal remains

## 6) What to expect

- If the cursor is before a tactic ends, that tactic is not yet applied.
- If the cursor is at/after a tactic end, that tactic is included.
- At/after `Qed`, the full proof script is treated as applied.
- Exit Proof Mode to stop automatic proof-state refresh.
