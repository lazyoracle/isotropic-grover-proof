# Issue #31 Design Document: Connect Grover's Algorithm from `formal-quantum-computation` to Noisy Isotropic Circuits

## Problem Context
`QuantumComputation.Algorithms.Grover` (from `google-deepmind/formal-quantum-computation`) already formalizes `Grover.oracleUnitary`, `Grover.diffuserUnitary`, `hadamardUnitary`, `Grover.groverMatrix`, `Grover.groverState`, `Grover.halfAngle`, `Grover.p_succ K (2^n) = sin²((2K + 1) arcsin(1 / √(2^n)))`, `Grover.groverState_target_sum`, and `Grover.grover_success_matrix_entry` with zero `sorry`s and zero custom axioms.

Meanwhile, `IsotropicGroverProof/QuantumChannel.lean` (from #30) connects pure-state isotropic sphere trajectories (`noisyTrajectoryExpectation`) and `QuantumInfo` channels (`depolarizingChannel`, `noisyCircuitChannel`) to `Ket`, `MState`, `computationalPOVM`, and `Circuit.size` for all $\sigma \in [0, 1]$ and $G \in \mathbb{N}$.

`IsotropicGroverProof/GroverCircuit.lean` currently proves only static real-vector specializations on `Set.Ioo 0 1` and `0 < G`, with ~150 lines of duplicated coordinate/norm boilerplate and a temporary dependency smoke lemma.

## Design & Architecture

### 1. Canonical Grover Unitary Sequences (`GroverCircuit.lean`)
Import `IsotropicGroverProof.QuantumChannel` into `GroverCircuit.lean` and connect `QuantumInfo` kets directly to `QuantumComputation.Algorithms.Grover`:
- Define `groverIterGates (target : Fin (2 ^ n)) : ℕ → List 𝐔[Fin (2 ^ n)]` (`0 => []`, `k + 1 => groverIterGates target k ++ [Grover.oracleUnitary target, Grover.diffuserUnitary]`), of length `2 * K`.
- Define `groverFullGates (n : ℕ) (target : Fin (2 ^ n)) (K : ℕ) : List 𝐔[Fin (2 ^ n)] := (hadamardUnitary : 𝐔[Fin (2 ^ n)]) :: groverIterGates target K`, of length `2 * K + 1`.
- Prove that evolving `uniform_superposition : Ket (Fin (2 ^ n))` along `groverIterGates target K`, and evolving `Ket.basis (0 : Fin (2 ^ n))` along `groverFullGates n target K`, both yield amplitude vector `Grover.groverState target K`, whose Born-rule measurement probability at `target` equals `Grover.p_succ K (2 ^ n) = Real.sin ((2 * (K : ℝ) + 1) * Real.arcsin (1 / √(2 ^ n))) ^ 2`.

### 2. End-to-End Noisy Grover Theorems (`σ ∈ [0, 1]`, `K, G : ℕ`)
1. **Canonical macro-gate noisy Grover theorems:**
   - `noisyGrover_iterGates_succProb`: Running `K` noisy Grover iterations (`groverIterGates target K`, $G = 2K$ unitary stages) from `uniform_superposition` under isotropic sphere noise gives expected `succProb` (and `computationalPOVM` Born probability):
     $$\sigma^{4K} \cdot \mathrm{Grover.p\_succ}\,K\,(2^n) + \frac{1 - \sigma^{4K}}{2^n}.$$
   - `noisyGrover_fullGates_succProb`: Including noisy Hadamard preparation from `Ket.basis 0` (`groverFullGates n target K`, $G = 2K + 1$) gives:
     $$\sigma^{2(2K + 1)} \cdot \mathrm{Grover.p\_succ}\,K\,(2^n) + \frac{1 - \sigma^{2(2K + 1)}}{2^n}.$$
2. **Arbitrary unitary gate decomposition (`List 𝐔[Fin (2 ^ n)]`):**
   - `noisyGrover_unitaryList_succProb`: For any gate list `us : List 𝐔[Fin (2 ^ n)]` of length `G = us.length` and initial ket `ψ₀` whose noiseless output satisfies `‖(idealUnitaryTrajectory us ψ₀) target‖ ^ 2 = Grover.p_succ K (2 ^ n)`, the noisy Markov trajectory expectation (and depolarizing `CPTPMap` Born probability) equals $\sigma^{2G} \cdot \mathrm{Grover.p\_succ}\,K\,(2^n) + (1 - \sigma^{2G}) / 2^n$.
3. **Syntactic primitive-gate `Circuit n` theorem (`G = c.size`):**
   - `noisyGrover_circuit_bornProb` & `noisyGrover_circuit_trajectory_succProb`: For any syntactic circuit `c : Circuit n` whose noiseless evolution from `ψ₀ : Ket (Fin (2 ^ n))` achieves target probability `‖(c.evolve ψ₀.vec) target‖ ^ 2 = Grover.p_succ K (2 ^ n)` (including `c.evolve (Ket.basis 0).vec = Grover.groverState target K`), both `((computationalPOVM n).measure (noisyCircuitChannel σ hσ c (MState.pure ψ₀)) target : ℝ)` and the microscopic pure-state sphere trajectory equal:
     $$\sigma^{2 \cdot c.\mathrm{size}} \cdot \mathrm{Grover.p\_succ}\,K\,(2^n) + \frac{1 - \sigma^{2 \cdot c.\mathrm{size}}}{2^n}.$$
   - Include a concrete 1-qubit (`n = 1`) syntactic `Circuit 1` example (`Circuit.H` preparation, `K = 0`, `c.size = 1`) verifying non-vacuous instantiation on `Circuit`.

### 3. Simplification & Deduplication of `GroverCircuit.lean`
- Express `targetBasisState` and `uniformSuperposition` properties via `ketToReal (Ket.basis w)` and `ketToReal uniform_superposition` (or keep existing definitions with compressed proofs via `ketToReal` / shared helpers) and deduplicate `norm_groverState2D` / `norm_groverState2D_prob` via a single orthonormal-combination lemma while preserving all existing public theorem signatures.
- Remove the temporary `quantumInfo_quantumComputation_smoke` lemma, replacing it with `#guard_msgs in #print axioms` guards on the real end-to-end noisy Grover theorems (`noisyGrover_iterGates_succProb`, `noisyGrover_circuit_bornProb`, `isotropicGrover_groverState2D`).
