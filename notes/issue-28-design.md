# Issue #28 Design Document: Bump Lean Toolchain to v4.36.0 and Integrate Physlib `QuantumInfo`

## Problem Context
To eliminate custom quantum state/measurement encoding assumptions ("axioms by definition") and connect isotropic sphere errors to standard finite-dimensional quantum channels (`Ket`, `MState`, `𝐔[d]`, `CPTPMap`, `POVM`), this repository will depend on the `QuantumInfo` library inside `leanprover-community/physlib`.

Currently, `isotropic-grover-proof` pins `leanprover/lean4:v4.29.0-rc6` and `mathlib` `v4.29.0-rc6`, whereas `leanprover-community/physlib` (`7910f51f9129ee4c5829216251c25a3a82042f1e`) targets `leanprover/lean4:v4.36.0` and `mathlib` `v4.36.0` (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`).

## Architecture & Decisions

1. **Toolchain & Lake Dependency (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`):**
   - Set `lean-toolchain` to `leanprover/lean4:v4.36.0`.
   - Enable Lake artifact caching in `lakefile.toml` (`enableArtifactCache = true`, `restoreAllArtifacts = true`) so precompiled `Physlib` / `QuantumInfo` R2 artifacts restore cleanly.
   - Require `Physlib` (`https://github.com/leanprover-community/physlib.git` at `rev = "7910f51f9129ee4c5829216251c25a3a82042f1e"`), which transitively resolves `mathlib` `v4.36.0`.
   - Update `.gitignore` to ignore `/.claude/` and `/.superpowers/` alongside `/.lake`.

2. **Targeted `QuantumInfo` Imports (Zero `sorryAx` Policy):**
   - Never use the top-level `import QuantumInfo` barrel, because higher-level modules such as `QuantumInfo.States.Mixed.Fidelity` and `QuantumInfo.Capacity.Capacity` contain `@[sorryful]` theorems.
   - Import only `sorry`-free foundational modules (`QuantumInfo.States.Pure.Braket`, `QuantumInfo.States.Mixed.MState`, `QuantumInfo.Operators.Unitary`, `QuantumInfo.Channels.CPTP`, `QuantumInfo.Measurements.POVM`), verified via `#guard_msgs in #print axioms` checks.

3. **Mathlib `v4.29` → `v4.36` Migration:**
   - Update proof scripts across `IsotropicGroverProof/*.lean` for any renamed lemmas, simp normal forms, or instance changes in Mathlib `v4.36.0`, keeping 0 `sorry`s, 0 warnings, and identical theorem statements.

4. **CI Cache Integration (`.github/workflows/lean_action_ci.yml`):**
   - Fetch `Physlib`'s public anonymous R2 cache (`LAKE_CONFIG="$PWD/.lake/packages/Physlib/lake-cache.toml" lake cache get --scope="physlib-master/leanprover-lean4-v4.36.0/physlib"`) alongside Mathlib's cache so GitHub Actions does not compile `QuantumInfo` from source on cold runs, while preserving `docgen-action@v1` with `homepage: '.pages'`.
