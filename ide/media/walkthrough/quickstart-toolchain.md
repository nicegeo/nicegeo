# Toolchain

NiceGeo checks run through your machine’s **opam** / **dune** setup (or a **nicegeo** binary on `PATH`, depending on settings).

- From the NiceGeo project root, install deps: `opam install --deps-only --with-test .`
- If something is missing, diagnostics and the output channel explain what to install.

You can tune execution under **Settings → NiceGeo** (`nicegeo.execution.mode`: `dune` vs `installedBinary`).
