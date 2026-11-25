# Issue #28 Design Document: Bump Lean Toolchain to v4.35.0 and Integrate `formal-quantum-computation` + `Physlib` (`QuantumInfo`)

## Problem Context
`google-deepmind/formal-quantum-computation` (`489edc7039aa4cdded53724b39ea90e33d2c88b4`) builds directly on `leanprover-community/physlib` (`QuantumInfo`) and `mathlib4` at pinned release tags **`v4.35.0`**. Its `QuantumComputation` library is `sorry`-free and custom-`axiom`-free (`QuantumComputationSpecs` is isolated in a separate library target) and already provides:
- `QuantumComputation.Algorithms.Grover` (`Grover.oracleUnitary`, `Grover.diffuserUnitary`, `Grover.groverMatrix`, `Grover.p_succ`, `Grover.groverState_target_sum`, `Grover.grover_success_matrix_entry`, `Grover.p_succ_pos`)
- `QuantumComputation.Circuits` (`Circuit n`, `Circuit.eval`, and syntactic primitive gate count `Circuit.size`)
- `QuantumComputation.Primitives` (`hadamardUnitary`, `compProj`, `compProjObs`, `compMeasurement`)
- Transitive access to `Physlib`'s `QuantumInfo` (`Ket`, `MState`, `𝐔[Fin (2^n)]`, `CPTPMap`, `POVM`).

Depending on `formal-quantum-computation` gives us both `QuantumInfo` and verified Grover/circuit definitions on stable `v4.35.0` release tags with zero duplication.

## Architecture & Decisions

1. **Toolchain & Lake Dependency (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`):**
   - Set `lean-toolchain` to `leanprover/lean4:v4.35.0`.
   - Require `formal-quantum-computation` (`git = "https://github.com/google-deepmind/formal-quantum-computation"`, `rev = "489edc7039aa4cdded53724b39ea90e33d2c88b4"`), which transitively pins `physlib` `v4.35.0` and `mathlib` `v4.35.0`.
   - Update `.gitignore` to ignore `/.claude/` and `/.superpowers/` alongside `/.lake`.

2. **Targeted Imports (Zero `sorryAx` Policy):**
   - Never import `QuantumComputationSpecs` (benchmark specs with `sorry`) or the top-level `QuantumInfo` barrel (`Fidelity`/`Capacity` contain `@[sorryful]`).
   - Import only `sorry`-free modules from `QuantumInfo` (`States.Pure.Braket`, `States.Mixed.MState`, `Operators.Unitary`, `Channels.CPTP`, `Measurements.POVM`) and `QuantumComputation` (`Algorithms.Grover.*`, `Circuits.*`, `Primitives.*`), verified via `#guard_msgs in #print axioms`.

3. **Mathlib `v4.29` → `v4.35` Migration:**
   - Update proof scripts across `IsotropicGroverProof/*.lean` for `v4.35.0` compatibility with 0 `sorry`s, 0 errors, and 0 warnings.

4. **CI Build Caching (`.github/workflows/lean_action_ci.yml`):**
   - Follow `formal-quantum-computation`'s CI caching pattern: fetch Mathlib's `lake exe cache get` via `lean-action`, and cache `.lake/build`, `.lake/packages/physlib/.lake/build`, and `.lake/packages/formal-quantum-computation/.lake/build` via `actions/cache` while preserving `docgen-action@v1` (`homepage: '.pages'`).
