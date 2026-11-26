# Issue #38 Design Document: Fix `doc-gen4` `ENOMEM` Failure in CI and Validate Documentation Builds on PRs

## Root Cause Analysis
In GitHub Actions `push` run `45788382914` (job `139800885688`), `leanprover-community/docgen-action@v1` failed during `doc-gen4` `v4.35.0` execution with:
```
✖ [3577/7042] Running proofwidgets:srcUri.github
error: resource exhausted (error code: 12, not enough memory)
```
Four interacting causes produced this failure and masked it during PR review:
1. **Ubuntu 26.04 `fork()` overcommit rejection (`leanprover/doc-gen4#434`):** `.github/workflows/lean_action_ci.yml` specified `runs-on: ubuntu-latest`, which GitHub Actions migrated from `ubuntu-24.04` to `ubuntu-26.04`. In `doc-gen4` `v4.35.0` (`0e1ffe2`), `module_facet docInfo` blockingly calls `uriJob.await` inside `modJob.mapM`, accumulating hundreds of blocked worker threads in `lake` before `package_facet srcUri.github` spawns `git`. Ubuntu 26.04's heuristic virtual-memory overcommit (`vm.overcommit_memory=0`) rejects `fork()` of the large multi-threaded `lake` process with `errno 12` (`ENOMEM`) despite ample free physical RAM.
2. **PR blind spot:** `docgen-action@v1` only runs API documentation builds on `github.event_name == 'push'`, skipping documentation generation completely on `pull_request` events.
3. **Cache & guillemet defects in `docgen-action@v1` (`56dff2bb`):**
   - `docgen-action` maps `«formal-quantum-computation»` to `docbuild/.lake/build/doc/«formalQuantumComputation»`, missing the actual `QuantumComputation` and `QuantumInfo` doc trees.
   - `docgen-action@v1` (`56dff2bb`) lacks the `rm -f .lake/build/doc-data/*.docs_built` fix (causing warm cache hits to skip HTML generation for project modules) and does not cache the compiled `doc-gen4` binary (whose non-deterministic rebuild hash invalidates all 3,500 `docInfo` markers on every run).
4. **Deprecated Node 20 actions:** `docgen-action@v1` invokes Node 20 versions of `actions/cache`, `actions/upload-pages-artifact`, and `actions/deploy-pages`.

## Solution Architecture

1. **Runner & Overcommit Configuration (`.github/workflows/lean_action_ci.yml`):**
   - Pin `runs-on: ubuntu-24.04` on the `build` job.
   - Set `sudo sysctl -w vm.overcommit_memory=1` before running documentation generation as defense-in-depth against Linux `fork()` virtual-address-space accounting spikes.

2. **Reproducible Documentation Build Script (`scripts/build_docs.sh`) & `.gitignore`:**
   - Ignore `/docbuild/` and `/_pages/` in `.gitignore`.
   - Create `scripts/build_docs.sh` implementing the official nested `docbuild/` Lake project pattern for `doc-gen4` (matching `lean-toolchain`'s tag `v4.35.0` with `packagesDir = "../.lake/packages"`):
     - Only runs `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update isotropic-grover-proof` when `docbuild/lake-manifest.json` is absent (cold build), preserving the exact `doc-gen4` dependency manifest and binary trace hash across warm cached runs.
     - Always deletes `docbuild/.lake/build/doc-data/*.docs_built` prior to `lake build IsotropicGroverProof:docs` so HTML pages for `IsotropicGroverProof` are regenerated on every run.
     - Copies `docbuild/.lake/build/doc` to `_pages/docs` (preserving existing GitHub Pages `/docs/...` URLs) and verifies that `_pages/docs/IsotropicGroverProof.html`, `_pages/docs/IsotropicGroverProof/MainTheorem.html`, `_pages/docs/IsotropicGroverProof/QuantumChannel.html`, and `_pages/docs/IsotropicGroverProof/GroverCircuit.html` exist and contain expected declaration anchors.

3. **Explicit CI Caching, PR Validation, and Pages Deployment (`.github/workflows/lean_action_ci.yml`):**
   - Cache `docbuild/lakefile.toml`, `docbuild/lake-manifest.json`, `docbuild/.lake/build`, and `.lake/packages/{doc-gen4,MD4Lean,BibtexQuery,UnicodeBasic,leansqlite}` via `actions/cache/restore@v5` and `actions/cache/save@v5` keyed on `lean-toolchain` + `lake-manifest.json`.
   - Run `scripts/build_docs.sh` on **both `pull_request` and `push`** so PR checks catch any documentation build error before merge.
   - Upload `_pages/` with `actions/upload-pages-artifact@v5` and deploy with `actions/deploy-pages@v5` strictly when `github.event_name == 'push' && github.ref == 'refs/heads/main'`.
