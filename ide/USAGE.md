# NiceGeo IDE Extension Usage Guide


This is a short guide for using the NiceGeo IDE extension.
Current version of the extension: `0.2.0`

## 0) Install required dependency

- Install all project dependencies in your active opam switch:
  - `opam install --deps-only --with-test .`

## 1) Install the extension from `.vsix`

- In VS Code, open the Command Palette.
- Run: `Extensions: Install from VSIX...`
- Select the file at: `ide/nicegeo-ide-0.2.0.vsix`
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

## 7) Use Hover

- Hover over global names (theorems/definitions/axioms) to see declaration info.
- Hover over local names to see local type info.
- Hover over tactics to see:
  - one-line summary,
  - expected parameters,
  - example usage.
- Tactic docs are loaded from backend tactic registration metadata.

## 8) Use Go-to-Definition

- Place cursor on a symbol and run:
  - `Go to Definition` (`F12` / context menu).
- For declaration references, the IDE jumps to the declaration range.
- For symbols declared in the same file, same-file declaration lookup is supported.

## 9) Quick visual test

- Open `ide/examples/hover_goto_demo.ncg`.
- Hover on symbols like `Keep`, `TrueI`, `A`, `a`.
- Hover on tactics in a `Proof ... Qed` script to inspect tactic docs.
- Try go-to-definition on symbol uses to verify navigation.
