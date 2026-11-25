# Toolchain v4.36.0 & Physlib QuantumInfo Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Upgrade Lean to `v4.36.0`, integrate `leanprover-community/physlib` (`QuantumInfo`) with prebuilt caches, migrate all existing proofs cleanly, and configure CI.

**Architecture:** Pin `lean-toolchain` to `leanprover/lean4:v4.36.0` and `Physlib` to `7910f51f9129ee4c5829216251c25a3a82042f1e` in `lakefile.toml` (which transitively brings `mathlib` `v4.36.0`). Restore both Mathlib and Physlib prebuilt caches, migrate `IsotropicGroverProof/*.lean` to `v4.36.0` with zero warnings, add a targeted `QuantumInfo` smoke check, and update `.github/workflows/lean_action_ci.yml` to pull Physlib's R2 cache.

**Tech Stack:** Lean 4 (`v4.36.0`), Lake, Mathlib (`v4.36.0`), Physlib (`QuantumInfo`), GitHub Actions.

**Spec:** `notes/issue-28-design.md`

## Global Constraints

- **Worktree isolation:** Work strictly inside `/home/anurag/isotropic-grover-proof/.claude/worktrees/issue-28`. Never modify `/home/anurag/isotropic-grover-proof` directly; note `.lake/packages` is intentionally symlinked to share downloaded packages.
- **Lean binary path:** Invoke `lake`, `lean`, and `elan` via `$HOME/.elan/bin/...` (ensure `$HOME/.elan/bin` is on `PATH`).
- **Exact versions:** `lean-toolchain` must be `leanprover/lean4:v4.36.0`; `Physlib` `rev` must be `"7910f51f9129ee4c5829216251c25a3a82042f1e"`.
- **Axiom & sorry hygiene:** Zero `sorry`s, zero compiler/linter warnings (`weak.linter.mathlibStandardSet = true`), and never `import QuantumInfo` (the barrel); only import `sorry`-free `QuantumInfo` submodules (`Braket`, `MState`, `Unitary`, `CPTP`, `POVM`).
- **Documentation directory:** Never create a top-level `docs/` directory (breaks `docgen-action@v1`); all notes stay in `notes/`.

## Review Focus

- Stale `v4.29` `.olean` artifacts in shared `.lake/packages/mathlib` blocking `v4.36` builds: run `lake exe cache get` after `lake update` (and clean stale dep builds if needed) so all dependency `.olean`s match `v4.36.0`.
- Accidental `sorryAx` leakage from `QuantumInfo`: pin `#guard_msgs in #print axioms` on a `QuantumInfo` smoke theorem using `Ket`, `MState.uniform`, `CPTPMap`, and `POVM` to prove only `[propext, Classical.choice, Quot.sound]` appear.
- Mathlib `v4.36.0` linter warnings (`weak.linter.mathlibStandardSet = true`): ensure `lake build` emits zero warnings across every module in `IsotropicGroverProof`.
- CI cold-cache timeout if Physlib R2 cache is not fetched before `lean-action@v1`: fetch Physlib R2 cache explicitly in `.github/workflows/lean_action_ci.yml` and tolerate transient R2 hiccups gracefully.
- Jekyll false trigger in `docgen-action@v1`: preserve `homepage: '.pages'` in `.github/workflows/lean_action_ci.yml`.

---

### Task 1: Upgrade Lean Toolchain, Add `Physlib` Dependency, and Migrate `IsotropicGroverProof` to `v4.36.0`

**Files:**
- Modify: `.gitignore`
- Modify: `lean-toolchain`
- Modify: `lakefile.toml`
- Modify: `lake-manifest.json`
- Modify: `IsotropicGroverProof/*.lean` (as needed for `v4.36.0` compatibility)
- Modify: `IsotropicGroverProof.lean` (or `IsotropicGroverProof/Defs.lean` for `QuantumInfo` smoke verification)

**Interfaces:**
- Consumes: Existing `IsotropicGroverProof` modules on `v4.29.0-rc6`
- Produces: Cleanly compiling `IsotropicGroverProof` library on `leanprover/lean4:v4.36.0` with `Physlib` (`7910f51f9129ee4c5829216251c25a3a82042f1e`) + `mathlib` (`v4.36.0`), prebuilt caches fetched, and a verified `sorryAx`-free `QuantumInfo` smoke test.

- [ ] **Step 1: Update `.gitignore`, `lean-toolchain`, and `lakefile.toml`**

Update `.gitignore` to ignore `/.lake`, `/.claude/`, and `/.superpowers/`.
Set `lean-toolchain` to `leanprover/lean4:v4.36.0`.
Update `lakefile.toml` to enable `enableArtifactCache = true` and `restoreAllArtifacts = true`, and replace the standalone `mathlib` `v4.29.0-rc6` requirement with `Physlib` (`git = "https://github.com/leanprover-community/physlib.git"`, `rev = "7910f51f9129ee4c5829216251c25a3a82042f1e"`).

- [ ] **Step 2: Resolve manifest, fetch Mathlib + Physlib caches, and write failing `QuantumInfo` smoke test (RED)**

Run with `$HOME/.elan/bin` on `PATH`:
```bash
export PATH="$HOME/.elan/bin:$PATH"
rm -rf .lake/packages/mathlib/.lake/build .lake/build
lake update
lake exe cache get
LAKE_CONFIG="$PWD/.lake/packages/Physlib/lake-cache.toml" \
  lake cache get --scope="physlib-master/leanprover-lean4-v4.36.0/physlib"
```
Add a TDD smoke check in `IsotropicGroverProof/Defs.lean` (or a small check at the bottom of `Defs.lean`) importing `QuantumInfo.States.Pure.Braket`, `QuantumInfo.States.Mixed.MState`, `QuantumInfo.Operators.Unitary`, `QuantumInfo.Channels.CPTP`, and `QuantumInfo.Measurements.POVM`, asserting `MState.uniform (d := Fin (2 ^ n))` has trace 1 (`(MState.uniform (d := Fin (2 ^ n))).tr`) and checking `#guard_msgs in #print axioms` against a bogus expected output first (or run `lake build` to observe RED failures from `v4.29` → `v4.36` breakages and the smoke assertion).

- [ ] **Step 3: Fix all `v4.29` → `v4.36` Lean/Mathlib changes and finalize the `QuantumInfo` smoke test (GREEN)**

Fix every compilation error and linter warning across `IsotropicGroverProof/*.lean` without introducing `sorry` or changing any public theorem signature. Set the `#guard_msgs in #print axioms` smoke check to verify exact foundational axioms (`propext`, `Classical.choice`, `Quot.sound` — or the exact subset used) with zero `sorryAx` and zero custom axioms, plus `#guard_msgs in #print axioms isotropicGrover_main` confirming only `[propext, Classical.choice, Quot.sound, IsotropicGrover.poissonIntegral_cos_sq_d3]` (in Lean's printed order).

- [ ] **Step 4: Run full build to verify pristine compilation**

Run: `PATH="$HOME/.elan/bin:$PATH" lake build`
Expected: Exit code 0, zero errors, zero warnings.

- [ ] **Step 5: Commit**

```bash
git add .gitignore lean-toolchain lakefile.toml lake-manifest.json IsotropicGroverProof IsotropicGroverProof.lean
git commit -m "build: bump Lean to v4.36.0 and integrate Physlib QuantumInfo"
```

### Task 2: Configure GitHub Actions CI (`lean_action_ci.yml`) for Physlib R2 Cache

**Files:**
- Modify: `.github/workflows/lean_action_ci.yml`

**Interfaces:**
- Consumes: Updated `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` from Task 1.
- Produces: `.github/workflows/lean_action_ci.yml` that pre-populates Mathlib + Physlib R2 caches before `leanprover/lean-action@v1` and preserves `docgen-action@v1` (`homepage: '.pages'`).

- [ ] **Step 1: Inspect and test exact cache-fetch shell snippet locally**

Verify in `.claude/worktrees/issue-28` that:
```bash
export PATH="$HOME/.elan/bin:$PATH"
TC=$(tr -d '[:space:]' < lean-toolchain | tr '/:' '--')
test "$TC" = "leanprover-lean4-v4.36.0"
test -f ".lake/packages/Physlib/lake-cache.toml"
```
exits 0 and matches Physlib's R2 scope string `physlib-master/leanprover-lean4-v4.36.0/physlib`.

- [ ] **Step 2: Update `.github/workflows/lean_action_ci.yml`**

Add a pre-build step before `leanprover/lean-action@v1` (or install `elan`, restore/fetch `lake exe cache get` and `LAKE_CONFIG="$PWD/.lake/packages/Physlib/lake-cache.toml" lake cache get --scope="physlib-master/${TC}/physlib" || true`) so `leanprover/lean-action@v1` restores prebuilt `QuantumInfo` artifacts from Lake's cache instead of compiling 38k LOC from source. Keep `leanprover/lean-action@v1` and `leanprover-community/docgen-action@v1` with `homepage: '.pages'`.

- [ ] **Step 3: Validate YAML syntax and re-verify `lake build`**

Run:
```bash
python3 -c 'import yaml, sys; yaml.safe_load(open(".github/workflows/lean_action_ci.yml"))'
PATH="$HOME/.elan/bin:$PATH" lake build
```
Expected: Valid YAML parse and `lake build` exits 0 with zero warnings.

- [ ] **Step 4: Commit**

```bash
git add .github/workflows/lean_action_ci.yml
git commit -m "ci: fetch Physlib R2 artifact cache in Lean Action CI"
```
