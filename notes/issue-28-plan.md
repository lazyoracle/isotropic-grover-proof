# Toolchain v4.35.0 & formal-quantum-computation + Physlib Integration Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Upgrade Lean to `v4.35.0`, integrate `google-deepmind/formal-quantum-computation` (`QuantumComputation`) and transitive `Physlib` (`QuantumInfo`) + `Mathlib` (`v4.35.0`), migrate all existing proofs cleanly, and configure fast CI caching.

**Architecture:** Pin `lean-toolchain` to `leanprover/lean4:v4.35.0` and require `formal-quantum-computation` at `489edc7039aa4cdded53724b39ea90e33d2c88b4` in `lakefile.toml` (transitively resolving `physlib` `v4.35.0` and `mathlib` `v4.35.0`). Fetch Mathlib prebuilt cache, build required `QuantumInfo` and `QuantumComputation` modules, migrate `IsotropicGroverProof/*.lean` with zero warnings, verify axiom hygiene via `#guard_msgs in #print axioms`, and update `.github/workflows/lean_action_ci.yml` to cache `.lake/build` plus `physlib` and `formal-quantum-computation` build directories.

**Tech Stack:** Lean 4 (`v4.35.0`), Lake, Mathlib (`v4.35.0`), Physlib (`QuantumInfo` `v4.35.0`), `google-deepmind/formal-quantum-computation` (`QuantumComputation`), GitHub Actions.

**Spec:** `notes/issue-28-design.md`

## Global Constraints

- **Worktree isolation:** Work strictly inside `/home/anurag/isotropic-grover-proof/.claude/worktrees/issue-28`. Never modify `/home/anurag/isotropic-grover-proof` directly; `.lake/packages` is intentionally symlinked to share downloaded packages.
- **Lean binary path:** Always include `$HOME/.elan/bin` on `PATH` when invoking `elan`, `lean`, or `lake`.
- **Exact versions:** `lean-toolchain` must be `leanprover/lean4:v4.35.0`; `formal-quantum-computation` `rev` must be `"489edc7039aa4cdded53724b39ea90e33d2c88b4"` (bringing `physlib` `v4.35.0` and `mathlib` `v4.35.0`).
- **Axiom & sorry hygiene:** Zero `sorry`s, zero compiler/linter warnings (`weak.linter.mathlibStandardSet = true`). Never import `QuantumComputationSpecs` or the top-level `QuantumInfo` barrel; import only targeted `sorry`-free `QuantumInfo` and `QuantumComputation` modules.
- **Documentation directory:** Never create a top-level `docs/` directory (breaks `docgen-action@v1`); all notes stay in `notes/`.

## Review Focus

- Stale `.olean` artifacts in shared `.lake/packages`: clear stale `.lake/build` directories under `.lake/packages` before running `lake exe cache get` and `lake build` on `v4.35.0`.
- Accidental `sorryAx` leakage: never import `QuantumComputationSpecs` or `QuantumInfo` barrel; pin `#guard_msgs in #print axioms` on smoke checks importing `QuantumInfo.Channels.CPTP`, `QuantumComputation.Algorithms.Grover.Amplitude`, and `QuantumComputation.Circuits.ResourceCounting`.
- Lean `v4.35.0` `module` compatibility & linter warnings: ensure `IsotropicGroverProof` compiles with zero warnings under `weak.linter.mathlibStandardSet = true`.
- CI build speed: cache `.lake/build`, `.lake/packages/physlib/.lake/build`, and `.lake/packages/formal-quantum-computation/.lake/build` (not 7 GB Mathlib, which `lake exe cache get` handles) in `.github/workflows/lean_action_ci.yml`.
- Preserve `docgen-action@v1` with `homepage: '.pages'` in `.github/workflows/lean_action_ci.yml`.

---

### Task 1: Upgrade Lean Toolchain to `v4.35.0`, Add `formal-quantum-computation` (`QuantumComputation` + `QuantumInfo`), and Migrate Codebase

**Files:**
- Modify: `.gitignore`
- Modify: `lean-toolchain`
- Modify: `lakefile.toml`
- Modify: `lake-manifest.json`
- Modify: `IsotropicGroverProof/*.lean` (as needed for `v4.35.0` compatibility)
- Modify: `IsotropicGroverProof/Defs.lean` (or `IsotropicGroverProof/MainTheorem.lean` for `#guard_msgs in #print axioms` smoke checks)

**Interfaces:**
- Consumes: Existing `IsotropicGroverProof` modules on `v4.29.0-rc6`
- Produces: Cleanly compiling `IsotropicGroverProof` library on `leanprover/lean4:v4.35.0` with `formal-quantum-computation` (`489edc7039aa4cdded53724b39ea90e33d2c88b4`), `physlib` (`v4.35.0`), and `mathlib` (`v4.35.0`), plus verified `sorryAx`-free `QuantumInfo` + `QuantumComputation` smoke checks.

- [ ] **Step 1: Update `.gitignore`, `lean-toolchain`, and `lakefile.toml`**

Update `.gitignore` to ignore `/.lake`, `/.claude/`, and `/.superpowers/`.
Set `lean-toolchain` to `leanprover/lean4:v4.35.0`.
Update `lakefile.toml` to require `formal-quantum-computation` (`git = "https://github.com/google-deepmind/formal-quantum-computation"`, `rev = "489edc7039aa4cdded53724b39ea90e33d2c88b4"`), which transitively brings `physlib` `v4.35.0` (`QuantumInfo`) and `mathlib` `v4.35.0`.

- [ ] **Step 2: Resolve manifest, fetch Mathlib cache, and write failing smoke check (RED)**

Run with `$HOME/.elan/bin` on `PATH`:
```bash
export PATH="$HOME/.elan/bin:$PATH"
rm -rf .lake/packages/*/.lake/build .lake/build
lake update
lake exe cache get
```
Add a smoke check importing `QuantumInfo.States.Mixed.MState`, `QuantumInfo.Channels.CPTP`, `QuantumComputation.Algorithms.Grover.Amplitude`, and `QuantumComputation.Circuits.ResourceCounting` (e.g., checking `Grover.p_succ_eq_sin_sq` and `(MState.uniform (d := Fin 2)).tr`) and run `lake build` to observe RED compilation/migration errors.

- [ ] **Step 3: Fix all `v4.29` → `v4.35` changes and finalize `#guard_msgs in #print axioms` checks (GREEN)**

Fix every compilation error and linter warning across `IsotropicGroverProof/*.lean` without introducing `sorry` or altering public theorem signatures. Pin `#guard_msgs in #print axioms` on both the `QuantumInfo`/`QuantumComputation` smoke theorem (verifying zero `sorryAx` and zero custom axioms) and `isotropicGrover_main`.

- [ ] **Step 4: Run full build to verify pristine compilation**

Run: `PATH="$HOME/.elan/bin:$PATH" lake build`
Expected: Exit code 0, zero errors, zero warnings.

- [ ] **Step 5: Commit**

```bash
git add .gitignore lean-toolchain lakefile.toml lake-manifest.json notes/issue-28-design.md notes/issue-28-plan.md IsotropicGroverProof IsotropicGroverProof.lean
git commit -m "build: bump Lean to v4.35.0 and integrate formal-quantum-computation + Physlib"
```

### Task 2: Configure GitHub Actions CI (`lean_action_ci.yml`) for `physlib` + `formal-quantum-computation` Build Caching

**Files:**
- Modify: `.github/workflows/lean_action_ci.yml`

**Interfaces:**
- Consumes: Updated `lean-toolchain` (`v4.35.0`), `lakefile.toml`, and `lake-manifest.json` from Task 1.
- Produces: `.github/workflows/lean_action_ci.yml` that fetches Mathlib cache via `lean-action`, restores/saves `.lake/build`, `.lake/packages/physlib/.lake/build`, and `.lake/packages/formal-quantum-computation/.lake/build` via `actions/cache`, runs `lake build --wfail`, and preserves `docgen-action@v1` (`homepage: '.pages'`).

- [ ] **Step 1: Verify exact package directory names in `.lake/packages` and `lake-manifest.json`**

Check `ls .lake/packages` inside `.claude/worktrees/issue-28` so the `actions/cache` paths in `.github/workflows/lean_action_ci.yml` match the exact package directory names (`physlib` and `formal-quantum-computation` / `quantum_computation`).

- [ ] **Step 2: Update `.github/workflows/lean_action_ci.yml`**

Adopt `formal-quantum-computation`'s split cache pattern:
1. Run `leanprover/lean-action@v1` with `use-mathlib-cache: true`, `use-github-cache: false`, `build: false`, `test: false`, `lint: false` to install `elan`, clone packages, and unpack Mathlib cache.
2. Restore `.lake/build` and the exact `.lake/packages/<pkg>/.lake/build` directories for `physlib` and `formal-quantum-computation` via `actions/cache/restore@v4` (or `@v5` matching `lean-action`) keyed by `lean-toolchain` + `lake-manifest.json`.
3. Run `leanprover/lean-action@v1` with `use-mathlib-cache: false`, `use-github-cache: false`, `build-args: '--wfail'`.
4. Save the build cache on miss when build succeeds.
5. Run `leanprover-community/docgen-action@v1` with `homepage: '.pages'`.

- [ ] **Step 3: Validate YAML syntax and re-verify `lake build --wfail`**

Run:
```bash
python3 -c 'import yaml; yaml.safe_load(open(".github/workflows/lean_action_ci.yml"))'
PATH="$HOME/.elan/bin:$PATH" lake build --wfail
```
Expected: Valid YAML parse and `lake build --wfail` exits 0.

- [ ] **Step 4: Commit**

```bash
git add .github/workflows/lean_action_ci.yml
git commit -m "ci: cache physlib and formal-quantum-computation builds in Lean Action CI"
```
