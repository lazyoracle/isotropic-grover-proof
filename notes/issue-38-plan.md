# Fix CI Docgen Failure & Validate Docs on PRs Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Eliminate the `doc-gen4` `srcUri.github` `ENOMEM` (`errno 12`) failure in CI, cache `doc-gen4` + `docbuild` properly, validate API doc generation on PRs, and deploy cleanly to GitHub Pages on `main`.

**Architecture:** Create an executable `scripts/build_docs.sh` that manages the nested `docbuild/` Lake workspace for `doc-gen4` `v4.35.0`, preserves cached `docbuild/lake-manifest.json` on warm hits, clears `*.docs_built` HTML markers, builds `IsotropicGroverProof:docs`, populates `_pages/docs`, and asserts key generated HTML pages exist. Update `.github/workflows/lean_action_ci.yml` to pin `ubuntu-24.04`, set `vm.overcommit_memory=1`, cache `docbuild` + `doc-gen4` packages via `actions/cache@v5`, run `scripts/build_docs.sh` on all runs, and deploy `_pages/` via `actions/upload-pages-artifact@v5` and `actions/deploy-pages@v5` on `push` to `main`.

**Tech Stack:** Bash (`scripts/build_docs.sh`), Lake / `leanprover/doc-gen4` (`v4.35.0`), GitHub Actions (`ubuntu-24.04`, `actions/cache@v5`, `actions/upload-pages-artifact@v5`, `actions/deploy-pages@v5`).

**Spec:** `notes/issue-38-design.md`

## Global Constraints

- **Worktree isolation:** Work strictly inside `/home/anurag/isotropic-grover-proof/.claude/worktrees/issue-38`. Never modify `/home/anurag/isotropic-grover-proof` directly (note `.lake/packages` is intentionally symlinked to share Lake packages).
- **Lean binary path:** Ensure `$HOME/.elan/bin` is on `PATH` inside `scripts/build_docs.sh` when `~/.elan/bin` exists so both local invocations and GitHub Actions steps locate `lake` reliably.
- **No root `docs/` directory:** Never create a top-level `docs/` directory; write generated site output to `_pages/docs` and ignore `/docbuild/` and `/_pages/` in `.gitignore`.
- **Pages deployment guard:** `actions/upload-pages-artifact@v5` and `actions/deploy-pages@v5` must run **only** when `github.event_name == 'push' && github.ref == 'refs/heads/main'`, never on `pull_request`.

## Review Focus

- Root `lake-manifest.json` mutation risk: `scripts/build_docs.sh` must run `lake update` and `lake build` strictly inside `docbuild/` so the repository's root `lake-manifest.json` is never modified.
- Warm-cache 404 regression (`leanprover-community/docgen-action#33`): `scripts/build_docs.sh` must delete `docbuild/.lake/build/doc-data/*.docs_built` and clean stale `_pages` before copying `docbuild/.lake/build/doc` to `_pages/docs`, and test both cold and warm rebuilds locally.
- Warm-cache `doc-gen4` hash invalidation: `scripts/build_docs.sh` must skip `lake update` when `docbuild/lake-manifest.json` and `../.lake/packages/doc-gen4` already exist (restored from cache), and CI must cache `.lake/packages/{doc-gen4,MD4Lean,BibtexQuery,UnicodeBasic,leansqlite}` alongside `docbuild/`.
- Exact `doc-gen4` dependency directory names in `.lake/packages/`: verify `ls .lake/packages` after running `scripts/build_docs.sh` locally so the `actions/cache` `path:` list matches the exact case-sensitive directory names created by Lake (e.g. `UnicodeBasic` vs `unicodeBasic`, `BibtexQuery` vs `bibtexQuery`, `MD4Lean` vs `md4lean`).
- Non-hidden Pages directory: use `_pages/` (not `.pages/`) so `actions/upload-pages-artifact@v5` includes all files by default without hidden-directory exclusions.

---

### Task 1: Implement `scripts/build_docs.sh`, Verify Cold & Warm `doc-gen4` Builds Locally, and Update `.github/workflows/lean_action_ci.yml`

**Files:**
- Modify: `.gitignore`
- Create: `scripts/build_docs.sh`
- Modify: `.github/workflows/lean_action_ci.yml`

**Interfaces:**
- Consumes: `lean-toolchain` (`leanprover/lean4:v4.35.0`), `lakefile.toml` (`IsotropicGroverProof`), compiled `.lake/build`
- Produces: Executable `scripts/build_docs.sh` generating verified `_pages/docs/IsotropicGroverProof/*.html`, and updated `.github/workflows/lean_action_ci.yml` running docgen on PRs + deploying Pages on `main`.

- [ ] **Step 1: Write a local verification check that fails before `scripts/build_docs.sh` exists (RED)**

Update `.gitignore` with `/docbuild/` and `/_pages/`. Run `test -x scripts/build_docs.sh` to confirm RED (missing script).

- [ ] **Step 2: Implement `scripts/build_docs.sh` and run a full cold + warm local docgen verification (GREEN)**

Create executable `scripts/build_docs.sh` (`chmod +x scripts/build_docs.sh`) with `set -euo pipefail`:
1. Prepend `$HOME/.elan/bin` to `PATH` if `$HOME/.elan/bin` exists.
2. Extract `LEAN_REV="$(cut -d: -f2 < lean-toolchain | tr -d '[:space:]')"` (`v4.35.0`).
3. Ensure `docbuild/lakefile.toml` exists with `name = "docbuild"`, `reservoir = false`, `version = "0.1.0"`, `packagesDir = "../.lake/packages"`, requiring `doc-gen4` (`scope = "leanprover"`, `rev = "$LEAN_REV"`) and `isotropic-grover-proof` (`path = "../"`).
4. Inside `docbuild/`: if `[ ! -f lake-manifest.json ] || [ ! -d ../.lake/packages/doc-gen4 ]`, run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update isotropic-grover-proof`.
5. Delete `rm -f .lake/build/doc-data/*.docs_built` and run `lake build IsotropicGroverProof:docs`.
6. Return to repo root, `rm -rf _pages && mkdir -p _pages`, `cp -r docbuild/.lake/build/doc _pages/docs`, and verify that `_pages/docs/IsotropicGroverProof.html`, `_pages/docs/IsotropicGroverProof/MainTheorem.html`, `_pages/docs/IsotropicGroverProof/QuantumChannel.html`, and `_pages/docs/IsotropicGroverProof/GroverCircuit.html` exist and contain `isotropicGrover_main`, `depolarizingChannel`, and `noisyGrover_circuit_bornProb`.

Run `scripts/build_docs.sh` cold, inspect `ls -1 .lake/packages` to record the exact directory names of `doc-gen4` and its dependencies, then simulate a warm cache restore (`rm -rf _pages` and re-run `scripts/build_docs.sh`) confirming `docInfo` analysis is not repeated and `_pages/docs/IsotropicGroverProof/*.html` are regenerated in seconds. Confirm root `lake-manifest.json` is untouched (`git diff lake-manifest.json`).

- [ ] **Step 3: Update `.github/workflows/lean_action_ci.yml` with `ubuntu-24.04`, `vm.overcommit_memory=1`, `docs` caching, and `v5` Pages actions**

In `.github/workflows/lean_action_ci.yml`:
1. Change `runs-on: ubuntu-latest` to `runs-on: ubuntu-24.04`.
2. Replace `uses: leanprover-community/docgen-action@v1` with:
   - `Restore docs cache` (`actions/cache/restore@v5`) restoring `docbuild/lakefile.toml`, `docbuild/lake-manifest.json`, `docbuild/.lake/build`, and the exact `.lake/packages/<doc-gen4-dep>` directories verified in Step 2, keyed on `docs-v2-${{ runner.os }}-${{ runner.arch }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json') }}` (with `restore-keys: docs-v2-${{ runner.os }}-${{ runner.arch }}-${{ hashFiles('lean-toolchain') }}-`).
   - `Configure VM overcommit for doc-gen4` (`sudo sysctl -w vm.overcommit_memory=1`).
   - `Build API documentation` (`./scripts/build_docs.sh` — runs on both `pull_request` and `push`).
   - `Save docs cache` (`actions/cache/save@v5` when `success() && steps.docs-cache-restore.outputs.cache-hit != 'true'`).
   - `Upload website (API documentation)` (`actions/upload-pages-artifact@v5` with `path: _pages/`, gated on `github.event_name == 'push' && github.ref == 'refs/heads/main'`).
   - `Deploy to GitHub Pages` (`actions/deploy-pages@v5`, `id: deployment`, gated on `github.event_name == 'push' && github.ref == 'refs/heads/main'`).

- [ ] **Step 4: Validate YAML, bash syntax, `lake build --wfail`, and clean `git status`**

Run:
```bash
bash -n scripts/build_docs.sh
python3 -c 'import yaml; yaml.safe_load(open(".github/workflows/lean_action_ci.yml"))'
PATH="$HOME/.elan/bin:$PATH" lake build --wfail
git status --short
```
Expected: Valid bash & YAML, `lake build --wfail` exits 0 with 0 warnings, and `docbuild/` + `_pages/` are ignored by `.gitignore`.

- [ ] **Step 5: Commit**

```bash
git add .gitignore scripts/build_docs.sh .github/workflows/lean_action_ci.yml notes/issue-38-design.md notes/issue-38-plan.md
git commit -m "fix(ci): pin ubuntu-24.04, cache doc-gen4 properly, and validate docgen on PRs"
```
