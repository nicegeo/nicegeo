# NiceGeo IDE Dev Guide

This document explains how the `ide/` extension + LSP are structured, built, and debugged.

## What exists as of today

- Language support for `.ncg` files (language id: `nicegeo`)
- Syntax grammar + language configuration
- LSP-based diagnostics (server computes diagnostics, client renders them)
- Status bar indicator (`NiceGeo: idle/checking/ok/issues`)
- Output channel (`NiceGeo Diagnostics`)

## IDE project structure

```text
ide/
├── client/                     # VS Code/Cursor extension host side
│   ├── src/
│   │   ├── extension.ts        # Client entrypoint, starts language server
│   │   └── core/
│   │       ├── output.ts       # Output channel wrapper
│   │       └── status.ts       # Status bar wrapper
│   ├── package.json            # Extension manifest + settings + commands
│   └── tsconfig.json
├── server/                     # Language server side (LSP backend)
│   ├── src/
│   │   ├── server.ts           # LSP server entrypoint and event wiring
│   │   └── providers/
│   │       └── diagnostics.ts  # Diagnostics execution + parsing + publish
│   ├── package.json
│   └── tsconfig.json
├── demo-files/                 # Sample NiceGeo files for testing
├── syntaxes/                   # TextMate grammar
├── language-configuration.json # Brackets/comments/etc
└── DEV.md                      # This file
```

## Build and run

From repo root (`system-e-kernel/`):

- Build both server and client:
  - `npm --prefix "ide/server" run compile`
  - `npm --prefix "ide/client" run compile`
- Or use the VS Code task:
  - Task label: `build-nicegeo-ide`

## Debug in VS Code

From repo root workspace, use Run and Debug:

- Launch config: `NiceGeo IDE (Extension Host)`
- It automatically:
  - runs prelaunch task `build-nicegeo-ide`
  - starts extension from `ide/client`
  - opens `ide/demo-files` and `ide/demo-files/proof.ncg`

Config files:

- `.vscode/launch.json`
- `.vscode/tasks.json`

## How diagnostics currently work

High-level flow:

1. Client starts LSP server (`ide/server/out/server.js`).
2. Server listens to document events (`save`/`change`).
3. Server runs: `dune exec nicegeo -- <file>`.
4. Server parses file/line/column from output.
5. Server publishes diagnostics via LSP.
6. Client editor shows squiggles and Problems entries.
7. Server sends status notifications; client updates bottom status bar.

Important files:

- Client bootstrap: `ide/client/src/extension.ts`
- Server wiring: `ide/server/src/server.ts`
- Diagnostics provider: `ide/server/src/providers/diagnostics.ts`

## Extension settings

In editor settings (prefix: `nicegeo`):

- `nicegeo.diagnostics.trigger`: `onSave` | `onType` | `both`
- `nicegeo.diagnostics.debounceMs`: debounce time for on-type diagnostics

## Commands

From Command Palette:

- `NiceGeo: Show Diagnostics Output`
- `NiceGeo: Run Diagnostics`

## Adding new LSP features

Recommended pattern:

1. Add provider file in `ide/server/src/providers/` (e.g. `hover.ts`, `completion.ts`).
2. Register capability/handler in `ide/server/src/server.ts`.
3. Keep client thin; only add client code if UI/commands are needed.
4. Build server + client and test in Extension Host.

