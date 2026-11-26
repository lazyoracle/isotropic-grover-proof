# Connect Grover's Algorithm to Noisy Isotropic Circuits Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Connect `QuantumComputation.Algorithms.Grover` directly to the isotropic sphere trajectory and `CPTPMap` / `Circuit.size` theorems from `QuantumChannel.lean`, and streamline `GroverCircuit.lean`.

**Architecture:** Task 1 simplifies existing real-vector helpers in `GroverCircuit.lean` via `QuantumChannel` (`ketToReal` + orthonormal linear combination helper) and connects `groverIterGates` / `groverFullGates` to `Grover.groverState` and `Grover.p_succ`. Task 2 proves the end-to-end noisy Grover theorems at the canonical macro-gate level, arbitrary unitary-decomposition level (`List 𝐔[Fin (2^n)]`), and syntactic `Circuit n` (`c.size`) level (with a concrete `Circuit 1` witness), removes the temporary smoke lemma, and pins `#guard_msgs in #print axioms`.

**Tech Stack:** Lean 4 (`v4.35.0`), `Physlib` (`QuantumInfo`), `formal-quantum-computation` (`QuantumComputation.Algorithms.Grover`, `QuantumComputation.Circuits`).

**Spec:** `notes/issue-31-design.md`

## Global Constraints

- **Worktree isolation:** Work strictly inside `/home/anurag/isotropic-grover-proof/.claude/worktrees/issue-31`. Never modify `/home/anurag/isotropic-grover-proof` directly.
- **Lean binary path:** Always include `$HOME/.elan/bin` on `PATH` when invoking `lean` or `lake`.
- **Zero non-standard axioms & zero `sorry`s:** Every declaration in `IsotropicGroverProof` must depend exclusively on a subset of `[propext, Classical.choice, Quot.sound]`, with 0 `sorry`s and 0 warnings (`lake build --wfail`). Never import `QuantumComputationSpecs` or the top-level `QuantumInfo` barrel.
- **Preserve public API:** Keep existing public definitions and theorems in `GroverCircuit.lean` (`targetBasisState`, `targetPerpState`, `uniformSuperposition`, `groverState2D`, `groverState2D_prob`, and their `isotropicGrover_*` theorems) intact while simplifying their proofs; only remove the temporary `quantumInfo_quantumComputation_smoke` lemma introduced in #28.
- **Documentation directory:** Never create a top-level `docs/` directory.

## Review Focus

- Matrix-vector convention between `hadamardMatrix n` and `Ket.basis 0`: verify `(hadamardMatrix n *ᵥ (Ket.basis (0 : Fin (2 ^ n))).vec) = Grover.groverState target 0` (using `Grover.groverMatrix_apply_zero target 0` in `QuantumComputation.Algorithms.Grover.Amplitude`, since `(M *ᵥ Ket.basis 0) i = M i 0`!).
- `uniform_superposition` in `QuantumInfo.States.Pure.Braket`: verify `(uniform_superposition : Ket (Fin (2 ^ n))).vec = Grover.groverState target 0` (`fun _ => (1 / √(2 ^ n) : ℝ)` cast to `ℂ`), using `Fintype.card_fin`.
- Left-to-right gate execution order in `groverIterGates`: in each Grover iteration, `Grover.oracleUnitary target` runs *before* `Grover.diffuserUnitary`, so `groverIterGates target (k + 1) = groverIterGates target k ++ [Grover.oracleUnitary target, Grover.diffuserUnitary]`, matching `Grover.groverState target (k + 1) = diffuserMatrix *ᵥ oracleMatrix target *ᵥ groverState target k`.
- Non-vacuity of syntactic `Circuit n` theorem: include a concrete `Circuit 1` example proving `‖(c.evolve (Ket.basis 0).vec) target‖ ^ 2 = Grover.p_succ 0 2` so the hypothesis is demonstrated non-vacuous on actual `PrimitiveGate` syntax.
- Full parameter domain `σ ∈ Set.Icc 0 1` and `K : ℕ` (including `K = 0`, `σ = 0`, `σ = 1`) with zero `0 < G` or `1 < 2 ^ n` restrictions on the new `QuantumInfo`/`QuantumComputation` Grover theorems!

---

### Task 1: Streamline `GroverCircuit.lean` Boilerplate and Bridge `groverIterGates` / `groverFullGates` to `Grover.groverState` and `Grover.p_succ`

**Files:**
- Modify: `IsotropicGroverProof/GroverCircuit.lean`

**Interfaces:**
- Consumes: `ketToReal`, `norm_ketToReal`, `succProb_ketToReal_eq_born`, `applyUnitaryKet`, `idealUnitaryTrajectory` (`QuantumChannel.lean`), `Grover.oracleUnitary`, `Grover.diffuserUnitary`, `Grover.groverState`, `Grover.groverState_target_sum`, `Grover.p_succ`, `hadamardUnitary` (`QuantumComputation`).
- Produces:
  - Simplified proofs in `GroverCircuit.lean` (`targetBasisState_eq_ketToReal`, `uniformSuperposition_eq_ketToReal`, deduplicated 2D search-plane norm proofs)
  - `noncomputable def unitaryListProd {n : ℕ} : List 𝐔[Fin (2 ^ n)] → 𝐔[Fin (2 ^ n)]`
  - `noncomputable def groverIterGates {n : ℕ} (target : Fin (2 ^ n)) : ℕ → List 𝐔[Fin (2 ^ n)]`
  - `noncomputable def groverFullGates {n : ℕ} (target : Fin (2 ^ n)) (K : ℕ) : List 𝐔[Fin (2 ^ n)]`
  - `lemma length_groverIterGates`, `lemma length_groverFullGates`, `theorem unitaryListProd_groverFullGates_val`
  - `theorem applyUnitaryKet_basis_zero_of_groverMatrix`, `theorem idealUnitaryTrajectory_of_groverMatrix`, `theorem circuit_evolve_basis_zero_of_groverMatrix`
  - `theorem idealUnitaryTrajectory_groverIterGates {n : ℕ} (target : Fin (2 ^ n)) (K : ℕ) : (idealUnitaryTrajectory (groverIterGates target K) (uniform_superposition : Ket (Fin (2 ^ n)))).vec = Grover.groverState target K`
  - `theorem idealUnitaryTrajectory_groverFullGates {n : ℕ} (target : Fin (2 ^ n)) (K : ℕ) : (idealUnitaryTrajectory (groverFullGates target K) (Ket.basis (0 : Fin (2 ^ n)))).vec = Grover.groverState target K`
  - `theorem groverState_bornProb {n : ℕ} (target : Fin (2 ^ n)) (K : ℕ) {ψ : Ket (Fin (2 ^ n))} (hψ : ψ.vec = Grover.groverState target K) : ‖ψ target‖ ^ 2 = Grover.p_succ K (2 ^ n)`

- [ ] **Step 1: Import `QuantumChannel` in `GroverCircuit.lean` and write failing `#check` assertions (RED)**

Import `IsotropicGroverProof.QuantumChannel` in `GroverCircuit.lean`, add `#check` assertions for `idealUnitaryTrajectory_groverIterGates`, `idealUnitaryTrajectory_groverFullGates`, and `groverState_bornProb`, and run `PATH="$HOME/.elan/bin:$PATH" lake build IsotropicGroverProof.GroverCircuit` to confirm RED missing-declaration failure.

- [ ] **Step 2: Simplify existing real-vector proofs and prove the noiseless Grover trajectory bridge (GREEN)**

1. Prove `targetBasisState n w = ketToReal (Ket.basis w)` and `uniformSuperposition n = ketToReal (uniform_superposition : Ket (Fin (2 ^ n)))` and use `norm_ketToReal` / `succProb_ketToReal_eq_born` + a shared orthonormal linear combination helper (`norm_smul_add_smul_of_ortho`) to compress `norm_uniformSuperposition`, `succProb_uniformSuperposition`, `norm_groverState2D`, and `norm_groverState2D_prob`.
2. Define `groverIterGates` and `groverFullGates`, prove their length lemmas (`2 * K` and `2 * K + 1`), and prove `idealUnitaryTrajectory_groverIterGates`, `idealUnitaryTrajectory_groverFullGates`, and `groverState_bornProb` by induction on `K` using `Grover.groverState_target_sum` and `Grover.p_succ_eq_sin_sq`.

- [ ] **Step 3: Run `lake build --wfail`**

Run: `PATH="$HOME/.elan/bin:$PATH" lake build --wfail`
Expected: Exit code 0, zero errors, zero warnings.

- [ ] **Step 4: Commit**

```bash
git add notes/issue-31-design.md notes/issue-31-plan.md IsotropicGroverProof/GroverCircuit.lean
git commit -m "feat: bridge QuantumComputation Grover state evolution to QuantumInfo kets and streamline GroverCircuit"
```

### Task 2: Prove End-to-End Noisy Grover Theorems Across Unitary Gate Lists and Syntactic `Circuit n`

**Files:**
- Modify: `IsotropicGroverProof/GroverCircuit.lean`

**Interfaces:**
- Consumes: `groverIterGates`, `groverFullGates`, `idealUnitaryTrajectory_groverIterGates`, `idealUnitaryTrajectory_groverFullGates`, `groverState_bornProb` from Task 1; `noisyTrajectory_eq_depolarizingChannel`, `noisyCircuit_bornProb_pure`, `noisyCircuit_trajectory_succProb_eq_measure` from `QuantumChannel.lean`.
- Produces:
  - `noncomputable def noisyUnitaryListChannel {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) : List 𝐔[Fin (2 ^ n)] → CPTPMap (Fin (2 ^ n)) (Fin (2 ^ n))`
  - `theorem noisyGrover_unitaryList_bornProb` & `theorem noisyGrover_unitaryList_succProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (us : List 𝐔[Fin (2 ^ n)]) (ψ₀ : Ket (Fin (2 ^ n))) (target : Fin (2 ^ n)) (K : ℕ) (hideal : ‖(idealUnitaryTrajectory us ψ₀) target‖ ^ 2 = Grover.p_succ K (2 ^ n)) : noisyTrajectoryExpectation n σ (us.map unitaryToRealIso) (ketToReal ψ₀) (fun Ψ => succProb n Ψ target) = σ ^ (2 * us.length) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * us.length)) / (2 ^ n : ℝ)`
  - `theorem noisyGrover_unitaryList_groverMatrix_bornProb` & `theorem noisyGrover_unitaryList_groverMatrix_succProb`
  - `theorem noisyGrover_iterGates_bornProb` & `theorem noisyGrover_iterGates_succProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (target : Fin (2 ^ n)) (K : ℕ) : noisyTrajectoryExpectation n σ ((groverIterGates target K).map unitaryToRealIso) (ketToReal (uniform_superposition : Ket (Fin (2 ^ n)))) (fun Ψ => succProb n Ψ target) = σ ^ (4 * K) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (4 * K)) / (2 ^ n : ℝ)`
  - `theorem noisyGrover_fullGates_bornProb` & `theorem noisyGrover_fullGates_succProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (target : Fin (2 ^ n)) (K : ℕ) : noisyTrajectoryExpectation n σ ((groverFullGates target K).map unitaryToRealIso) (ketToReal (Ket.basis (0 : Fin (2 ^ n)))) (fun Ψ => succProb n Ψ target) = σ ^ (2 * (2 * K + 1)) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * (2 * K + 1))) / (2 ^ n : ℝ)`
  - `theorem noisyGrover_circuit_bornProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (c : Circuit n) (ψ₀ : Ket (Fin (2 ^ n))) (target : Fin (2 ^ n)) (K : ℕ) (hideal : ‖(c.evolve ψ₀.vec) target‖ ^ 2 = Grover.p_succ K (2 ^ n)) : ((computationalPOVM n).measure (noisyCircuitChannel σ hσ c (MState.pure ψ₀)) target : ℝ) = σ ^ (2 * c.size) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * c.size)) / (2 ^ n : ℝ)`
  - `theorem noisyGrover_circuit_trajectory_succProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (c : Circuit n) (ψ₀ : Ket (Fin (2 ^ n))) (target : Fin (2 ^ n)) (K : ℕ) (hideal : ‖(c.evolve ψ₀.vec) target‖ ^ 2 = Grover.p_succ K (2 ^ n)) : noisyTrajectoryExpectation n σ ((circuitUnitaries c).map unitaryToRealIso) (ketToReal ψ₀) (fun Ψ => succProb n Ψ target) = σ ^ (2 * c.size) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * c.size)) / (2 ^ n : ℝ)`
  - `theorem noisyGrover_circuit_groverMatrix_bornProb` & `theorem noisyGrover_circuit_groverMatrix_trajectory_succProb`
  - Concrete computable `Circuit 1` (`Circuit.H (0 : Wire 1)`, `K = 0`, `c.size = 1`) and `Circuit 2` (`grover2QubitCircuit`, `K = 1`, `c.size = 14`, `Grover.p_succ 1 4 = 1`) witnesses demonstrating non-vacuous instantiation on primitive-gate syntax.

- [ ] **Step 1: Add failing `#check` assertions for the noisy Grover theorems and remove `quantumInfo_quantumComputation_smoke` (RED)**

Add `#check` lines for all five noisy Grover theorems in `GroverCircuit.lean`, remove `quantumInfo_quantumComputation_smoke`, and run `PATH="$HOME/.elan/bin:$PATH" lake build IsotropicGroverProof.GroverCircuit` to observe RED failure.

- [ ] **Step 2: Implement the five end-to-end noisy Grover theorems, concrete `Circuit 1` witness, and `#guard_msgs in #print axioms` guards (GREEN)**

Prove `noisyGrover_unitaryList_succProb` (from `noisyTrajectory_succProb` + `ketToReal_idealUnitaryTrajectory` + `succProb_ketToReal_eq_born`), deduce `noisyGrover_iterGates_succProb` (`2 * (2 * K) = 4 * K`) and `noisyGrover_fullGates_succProb`, prove `noisyGrover_circuit_bornProb` (from `noisyCircuit_bornProb_pure`) and `noisyGrover_circuit_trajectory_succProb` (from `noisyCircuit_trajectory_succProb_eq_measure`), add the concrete `Circuit.H (0 : Wire 1)` witness example, and pin `#guard_msgs in #print axioms` on `noisyGrover_iterGates_succProb`, `noisyGrover_fullGates_succProb`, `noisyGrover_circuit_bornProb`, and `isotropicGrover_groverState2D` confirming `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 3: Run full `lake build --wfail`**

Run: `PATH="$HOME/.elan/bin:$PATH" lake build --wfail`
Expected: Exit code 0, zero errors, zero warnings.

- [ ] **Step 4: Commit**

```bash
git add IsotropicGroverProof/GroverCircuit.lean
git commit -m "feat: prove end-to-end noisy Grover theorems for unitary lists and syntactic circuits"
```
