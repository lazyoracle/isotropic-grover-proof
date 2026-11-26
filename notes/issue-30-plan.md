# Bridge Isotropic Sphere Errors to QuantumInfo CPTPMap & Circuit.size Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Eliminate all remaining "axioms by definition" by extending isotropic sphere moments to $\sigma \in [0, 1]$, proving the `Measure.bind` multi-gate pure-state Markov chain, and bridging to `QuantumInfo` (`Ket`, `MState`, `CPTPMap`, `POVM`) and `QuantumComputation` (`Circuit`, `Circuit.size`).

**Architecture:** Task 1 extends `poissonAngleMeasure` to `[0, 1]`, deletes `isotropicComposition := rfl`, and proves the general bilinear second-moment operator theorem on `E n`. Task 2 upgrades `Sequential.lean` with the `Measure.bind` noisy gate process over `List (E n ≃ₗᵢ[ℝ] E n)` for all `G : ℕ` and `σ ∈ Set.Icc 0 1` and connects `LimitingCases.lean`. Task 3 adds `IsotropicGroverProof/QuantumChannel.lean` establishing the `Ket`/`MState`/`POVM` Born-rule isomorphism, the emergence of `depolarizingChannel : CPTPMap`, unitary commutation, and syntactic `Circuit.size` noisy circuit evaluation.

**Tech Stack:** Lean 4 (`v4.35.0`), Mathlib (`Measure.bind`, `LinearIsometryEquiv`), Physlib `QuantumInfo` (`Ket`, `MState`, `CPTPMap`, `POVM`), `formal-quantum-computation` (`Circuit`, `Circuit.size`, `compProjObs`).

**Spec:** `notes/issue-30-design.md`

## Global Constraints

- **Worktree isolation:** Work strictly inside `/home/anurag/isotropic-grover-proof/.claude/worktrees/issue-30`. Never modify `/home/anurag/isotropic-grover-proof` directly.
- **Lean binary path:** Always include `$HOME/.elan/bin` on `PATH` when invoking `lean` or `lake`.
- **Zero non-standard axioms & zero `sorry`s:** Every declaration in `IsotropicGroverProof` must depend exclusively on a subset of `[propext, Classical.choice, Quot.sound]`, with 0 `sorry`s and 0 warnings (`lake build --wfail`). Never import `QuantumComputationSpecs` or the top-level `QuantumInfo` barrel.
- **Simplicity & no duplication:** Keep existing public theorems in `MainTheorem.lean`, `GroverCircuit.lean`, `LimitingCases.lean`, and `Sequential.lean` intact while removing dead stubs (`isotropicComposition := rfl`) and reusing the bilinear second-moment theorem across both `succProb` and `MState` proofs instead of duplicating sphere algebra.
- **Documentation directory:** Never create a top-level `docs/` directory.

## Review Focus

- Endpoint $\sigma = 0$ in `poissonMarginal d 0`: `poissonKernelDensity d 0 θ = sin θ ^ (d - 2)`; verify `denom_pos` holds for `0 ≤ σ ∧ σ < 1` (`Set.Ico 0 1`) and prove $\int_0^\pi \sin^{d-2}\theta \cos\theta = 0$ and $\int_0^\pi \sin^{d-2}\theta \cos^2\theta = \frac{1}{d} \int_0^\pi \sin^{d-2}\theta$ via 1D FTC for `2 ≤ d`.
- Endpoint $\sigma = 1$ and $G = 0$: `0 ^ 0 = 1` in Lean (`pow_zero`), so `σ ^ 0 = 1 ∈ Set.Icc 0 1` even when `σ = 0`, matching `poissonAngleMeasure d (σ ^ 0) = Measure.dirac 0` (noiseless empty gate sequence!).
- Measurability for `Measure.bind` (`integral_bind` / `bind_apply`): prove `AEMeasurable` (or `Measurable`) of `θ ↦ (perpSphereMeasure Ψ).map (isotropicError Ψ · θ)` or avoid measurability of measure-valued maps on `Ψ` by defining `sequentialNoisyMeasure` via `Measure` pushforward of an explicit product space (`Fin G → ℝ × ...`) OR proving `Measurable (perpSphereMeasure)` — **CRITICAL DESIGN NOTE:** `perpSphereMeasure Ψ` depends on `stdOrthonormalBasis ℝ ↥(V_perp Ψ)` (`Classical.choice`), which is NOT measurable in `Ψ`! To avoid any non-measurable kernel in `Ψ`, define each step via an **ambient** rotation / orthogonal projection or define `applyNoisyStep (n : ℕ) (σ : ℝ) (μ : Measure (E n)) : Measure (E n)`? Wait: `μ.bind κ` in Mathlib requires `AEMeasurable κ μ`! See Task 2 below for the clean measurable construction via `P_perp Ψ` on `ambientSphereMeasure n` OR inductively pushing forward product measures!
- Dependent-proof avoidance in complex density matrices: define `pureDensityMatrix (n : ℕ) (v : E n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ` on ALL `v : E n` without a `‖v‖ = 1` proof argument, and prove `pureDensityMatrix n (ketToReal ψ) = (MState.pure ψ).m` separately so Bochner integration over `E n` is completely non-dependent.
- `Circuit.eval` composition order in `QuantumComputation.Circuits.Basic`: `(Circuit.seq c₁ c₂).eval = c₂.eval * c₁.eval` (`c₁` runs first, then `c₂`), matching `noisyCircuitChannel σ hσ (.seq c₁ c₂) = noisyCircuitChannel σ hσ c₂ ∘ₘ noisyCircuitChannel σ hσ c₁` and `CPTPMap.ofUnitary (U₂ * U₁) = CPTPMap.ofUnitary U₂ ∘ₘ CPTPMap.ofUnitary U₁`! Verify matrix multiplication order `(U₂ * U₁) * ρ * (U₂ * U₁)ᴴ = U₂ * (U₁ * ρ * U₁ᴴ) * U₂ᴴ`!

---

### Task 1: Extend `poissonAngleMeasure` to `[0, 1]`, Remove `isotropicComposition` Stub, and Prove the Full Bilinear Second-Moment Identity

**Files:**
- Modify: `IsotropicGroverProof/IsotropicError.lean`
- Modify: `IsotropicGroverProof/Composition.lean`
- Modify: `IsotropicGroverProof/SecondMoment.lean`

**Interfaces:**
- Consumes: `poissonMarginal`, `isotropicError`, `perpSphereMeasure`, `P_perp`, `secondMoment_coeff`
- Produces:
  - `noncomputable def poissonAngleMeasure (d : ℕ) (σ : ℝ) : Measure ℝ := if σ = 1 then Measure.dirac 0 else poissonMarginal d σ`
  - `theorem poissonAngleMeasure_isProbMeasure (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (hd : 2 ≤ d) : IsProbabilityMeasure (poissonAngleMeasure d σ)`
  - `theorem poissonAngleMeasure_mean_cos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (hd : 2 ≤ d) : ∫ θ, cos θ ∂(poissonAngleMeasure d σ) = σ`
  - `theorem poissonAngleMeasure_cos_sq (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (hd : 2 ≤ d) : ∫ θ, (cos θ) ^ 2 ∂(poissonAngleMeasure d σ) = ((d - 1 : ℝ) * σ ^ 2 + 1) / d`
  - `theorem perpSphere_inner_mul_inner (Ψ : E n) (hΨ : ‖Ψ‖ = 1) (u v : E n) : ∫ e₂, ⟪e₂, u⟫_ℝ * ⟪e₂, v⟫_ℝ ∂(perpSphereMeasure Ψ) = (⟪u, v⟫_ℝ - ⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) / ((d n : ℝ) - 1)`
  - `theorem isotropicError_bilinear_secondMoment (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (Ψ : E n) (hΨ : ‖Ψ‖ = 1) (u v : E n) : ∫ θ, ∫ e₂, ⟪isotropicError Ψ e₂ θ, u⟫_ℝ * ⟪isotropicError Ψ e₂ θ, v⟫_ℝ ∂(perpSphereMeasure Ψ) ∂(poissonAngleMeasure (d n) σ) = σ ^ 2 * (⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) + (1 - σ ^ 2) / (d n : ℝ) * ⟪u, v⟫_ℝ`
  - `theorem isotropicError_succProb_oneStep (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (Ψ : E n) (hΨ : ‖Ψ‖ = 1) (w : Fin (2 ^ n)) : ∫ θ, ∫ e₂, succProb n (isotropicError Ψ e₂ θ) w ∂(perpSphereMeasure Ψ) ∂(poissonAngleMeasure (d n) σ) = σ ^ 2 * succProb n Ψ w + (1 - σ ^ 2) / (2 ^ n : ℝ)`

- [ ] **Step 1: Write failing `#check` assertions for the new `[0, 1]` and bilinear theorems (RED)**

Add `#check` lines for `poissonAngleMeasure_cos_sq` in `IsotropicError.lean` and `isotropicError_bilinear_secondMoment` / `isotropicError_succProb_oneStep` in `SecondMoment.lean`, remove the deprecated `isotropicComposition` stub in `Composition.lean`, and run `PATH="$HOME/.elan/bin:$PATH" lake build IsotropicGroverProof.SecondMoment` to confirm expected missing-declaration failure.

- [ ] **Step 2: Implement `poissonAngleMeasure` on `[0, 1]` and the bilinear second-moment theorem (GREEN)**

1. In `IsotropicError.lean`: generalize `denom_pos`, `poissonKernelDensity_nonneg`, `poissonKernelDensity_continuous`, `poissonNormConst_pos`, and `poissonMarginal_isProbMeasure` to `σ ∈ Set.Ico 0 1` (keeping `Set.Ioo 0 1` callers working via `Set.Ioo_subset_Ico_self`), prove the $\sigma = 0$ first and second moments of `poissonMarginal d 0` via 1D FTC on $\sin^{d-1}\theta / (d - 1)$ and $\sin^{d-1}\theta \cos\theta$, and define `poissonAngleMeasure` with `poissonAngleMeasure_isProbMeasure`, `poissonAngleMeasure_mean_cos`, and `poissonAngleMeasure_cos_sq` on `Set.Icc 0 1`.
2. In `Composition.lean`: delete the deprecated `isotropicComposition := rfl` stub and update module comments cleanly.
3. In `SecondMoment.lean`: prove `perpSphere_inner_mul_inner` from `secondMoment_coeff` + `P_perp_apply`, then expand `⟪isotropicError Ψ e₂ θ, u⟫_ℝ * ⟪isotropicError Ψ e₂ θ, v⟫_ℝ`, integrate over `e₂` (cross terms vanish by `integral_perp_inner_eq_zero`), and integrate over `θ` using `poissonAngleMeasure_cos_sq` to prove `isotropicError_bilinear_secondMoment` and `isotropicError_succProb_oneStep`.

- [ ] **Step 3: Run full `lake build --wfail` and check `#print axioms`**

Run: `PATH="$HOME/.elan/bin:$PATH" lake build --wfail`
Expected: Exit code 0, zero warnings, `#guard_msgs in #print axioms isotropicError_bilinear_secondMoment` prints `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 4: Commit**

```bash
git add notes/issue-30-design.md notes/issue-30-plan.md IsotropicGroverProof/IsotropicError.lean IsotropicGroverProof/Composition.lean IsotropicGroverProof/SecondMoment.lean
git commit -m "feat: extend Poisson angle moments to [0,1] and prove bilinear second-moment identity"
```

### Task 2: Formalize Multi-Gate Sequential Noisy Trajectory Over Interleaved Isometric Gates in `Sequential.lean` and Extend `LimitingCases.lean`

**Files:**
- Modify: `IsotropicGroverProof/Sequential.lean`
- Modify: `IsotropicGroverProof/LimitingCases.lean`

**Interfaces:**
- Consumes: `poissonAngleMeasure`, `perpSphereMeasure`, `isotropicError_bilinear_secondMoment`, `isotropicError_succProb_oneStep` from Task 1.
- Produces:
  - Inductive expected-value operator `noisyTrajectoryExpectation (n : ℕ) (σ : ℝ) : List (E n ≃ₗᵢ[ℝ] E n) → E n → (E n → ℝ) → ℝ`:
    - `[] => fun Φ₀ f => f Φ₀`
    - `U :: rest => fun Φ₀ f => ∫ θ, ∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ) f ∂(perpSphereMeasure (U Φ₀)) ∂(poissonAngleMeasure (d n) σ)`
    *(Note: Defining the multi-step Markov expectation directly via iterated nested integrals over `(poissonAngleMeasure, perpSphereMeasure)` completely avoids non-measurable `Classical.choice` basis selection in `Ψ ↦ perpSphereMeasure Ψ` while faithfully executing `Ψ_{k+1} = cos θ_{k+1} (U_{k+1} Ψ_k) + sin θ_{k+1} e_{2,k+1}` with `e_{2,k+1} ~ perpSphereMeasure (U_{k+1} Ψ_k)` at every gate step!)*
  - `def idealGateTrajectory (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) : E n := gates.foldl (fun v U => U v) Φ₀`
  - `theorem noisyTrajectory_bilinear (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1) (u v : E n) : noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => ⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) = σ ^ (2 * gates.length) * (⟪idealGateTrajectory gates Φ₀, u⟫_ℝ * ⟪idealGateTrajectory gates Φ₀, v⟫_ℝ) + (1 - σ ^ (2 * gates.length)) / (d n : ℝ) * ⟪u, v⟫_ℝ`
  - `theorem noisyTrajectory_fidelity_eq_sequentialFidelity (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1) : noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => ⟪Ψ, idealGateTrajectory gates Φ₀⟫_ℝ ^ 2) = sequentialFidelity (d n) σ gates.length`
  - `theorem noisyTrajectory_succProb (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1) (w : Fin (2 ^ n)) : noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => succProb n Ψ w) = σ ^ (2 * gates.length) * succProb n (idealGateTrajectory gates Φ₀) w + (1 - σ ^ (2 * gates.length)) / (2 ^ n : ℝ)`
  - Endpoint & continuity theorems on `Set.Icc 0 1` in `LimitingCases.lean`.

- [ ] **Step 1: Write failing `#check` tests for `noisyTrajectory_bilinear`, `noisyTrajectory_fidelity_eq_sequentialFidelity`, and `noisyTrajectory_succProb` (RED)**

Add `#check` assertions in `Sequential.lean` and run `PATH="$HOME/.elan/bin:$PATH" lake build IsotropicGroverProof.Sequential` to observe expected missing-declaration errors.

- [ ] **Step 2: Implement `noisyTrajectoryExpectation`, prove the `G`-gate inductive theorems in `Sequential.lean`, and connect `LimitingCases.lean` (GREEN)**

1. Import `IsotropicGroverProof.SecondMoment` in `Sequential.lean`.
2. Define `idealGateTrajectory` and `noisyTrajectoryExpectation` by recursion on `gates : List (E n ≃ₗᵢ[ℝ] E n)`.
3. Prove a helper `noisyTrajectory_congr_unitSphere` showing that if two functions `f₁, f₂ : E n → ℝ` agree on all unit vectors `{Ψ : E n | ‖Ψ‖ = 1}` (or more generally `noisyTrajectoryExpectation` only evaluates on unit vectors when `‖Φ₀‖ = 1`, using `perpSphereMeasure_norm_ae` + `isotropicError_norm` + `U.norm_map`!).
4. Prove `noisyTrajectory_bilinear` by induction on `gates`! Look how short the inductive step `U :: rest` is:
   - For a.e. `e₂` under `perpSphereMeasure (U Φ₀)` and every `θ`, `Ψ₁ := isotropicError (U Φ₀) e₂ θ` satisfies `‖Ψ₁‖ = 1`!
   - By the induction hypothesis on `rest` starting at `Ψ₁`, the inner `noisyTrajectoryExpectation` equals `σ ^ (2 * rest.length) * (⟪idealGateTrajectory rest Ψ₁, u⟫_ℝ * ⟪idealGateTrajectory rest Ψ₁, v⟫_ℝ) + (1 - σ ^ (2 * rest.length)) / d n * ⟪u, v⟫_ℝ`.
   - Since `idealGateTrajectory rest` is a composition of linear isometries `W : E n ≃ₗᵢ[ℝ] E n`, `⟪W Ψ₁, u⟫_ℝ = ⟪Ψ₁, W.symm u⟫_ℝ` and `⟪W.symm u, W.symm v⟫_ℝ = ⟪u, v⟫_ℝ`!
   - Applying `isotropicError_bilinear_secondMoment` to `(U Φ₀, W.symm u, W.symm v)` and simplifying `σ ^ 2 * σ ^ (2 * rest.length) = σ ^ (2 * (U :: rest).length)` closes the induction cleanly!
5. Deduce `noisyTrajectory_fidelity_eq_sequentialFidelity` (setting `u = v = idealGateTrajectory gates Φ₀`) and `noisyTrajectory_succProb` (summing `succProbIdx0` and `succProbIdx1`).
6. In `LimitingCases.lean`, add closed-interval `[0, 1]` evaluation (`σ = 1`, `σ = 0`, `G = 0`) and `ContinuousOn` corollaries for `noisyTrajectory_succProb`.

- [ ] **Step 3: Run `lake build --wfail` and verify `#guard_msgs in #print axioms`**

Run: `PATH="$HOME/.elan/bin:$PATH" lake build --wfail`
Expected: Exit code 0, zero warnings, `#print axioms noisyTrajectory_succProb` shows `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 4: Commit**

```bash
git add IsotropicGroverProof/Sequential.lean IsotropicGroverProof/LimitingCases.lean
git commit -m "feat: prove multi-gate Markov trajectory theorems over interleaved isometries"
```

### Task 3: Create `QuantumChannel.lean` Bridging Isotropic Sphere Errors to `QuantumInfo` `CPTPMap` and `QuantumComputation` `Circuit.size`

**Files:**
- Create: `IsotropicGroverProof/QuantumChannel.lean`
- Modify: `IsotropicGroverProof/Basic.lean`

**Interfaces:**
- Consumes: `isotropicError_bilinear_secondMoment` (`SecondMoment.lean`), `noisyTrajectoryExpectation` & `noisyTrajectory_bilinear` (`Sequential.lean`), `QuantumInfo` (`Ket`, `MState`, `𝐔[Fin (2^n)]`, `CPTPMap`, `POVM`), `QuantumComputation` (`Circuit`, `Circuit.size`, `Circuit.eval`, `compProjObs`).
- Produces:
  - `vecToReal` / `realToVec`, `ketToReal` / `realToKet`, `unitaryToRealIso : 𝐔[Fin (2 ^ n)] → (E n ≃ₗᵢ[ℝ] E n)`
  - `computationalPOVM (n : ℕ) : POVM (Fin (2 ^ n)) (Fin (2 ^ n))` and `succProb_ketToReal_eq_born` (`succProb n (ketToReal ψ) w = ‖ψ w‖ ^ 2`, `= ((MState.pure ψ).m w w).re`, `= (MState.pure ψ).exp_val (compProjObs w).1`, `= ((computationalPOVM n).measure (MState.pure ψ) w : ℝ)`)
  - `pureDensityMatrix (n : ℕ) (v : E n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ` with `pureDensityMatrix_ketToReal (ψ : Ket (Fin (2 ^ n))) : pureDensityMatrix n (ketToReal ψ) = (MState.pure ψ).m`
  - `depolarizingChannel (n : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) : CPTPMap (Fin (2 ^ n)) (Fin (2 ^ n))`
  - `isotropicOneStep_eq_depolarizingChannel` and `noisyTrajectory_eq_depolarizingChannel`: expectation of every `(x, y)` entry of `pureDensityMatrix` under one step (and under `us : List 𝐔[Fin (2 ^ n)]` via `us.map unitaryToRealIso`) equals `(depolarizingChannel n (σ ^ us.length) ... (MState.pure ψ_final)).m x y`!
  - `depolarizingChannel_comm_ofUnitary`, `depolarizingChannel_compose`, `noisyCircuitChannel`, `noisyCircuitChannel_eq`, and `noisyCircuit_bornProb`: for any `c : Circuit n`, `σ ∈ Set.Icc 0 1`, initial `ψ₀ : Ket (Fin (2 ^ n))`, and outcome `w : Fin (2 ^ n)`:
    `((computationalPOVM n).measure (noisyCircuitChannel σ hσ c (MState.pure ψ₀)) w : ℝ) = σ ^ (2 * c.size) * (CPTPMap.ofUnitary c.eval (MState.pure ψ₀)).exp_val (compProjObs w).1 + (1 - σ ^ (2 * c.size)) / (2 ^ n : ℝ)`.

- [ ] **Step 1: Create `IsotropicGroverProof/QuantumChannel.lean` stub, import in `Basic.lean`, and write failing `#check` assertions (RED)**

Create a minimal `QuantumChannel.lean` with `#check` assertions for the target definitions/theorems, add `import IsotropicGroverProof.QuantumChannel` to `IsotropicGroverProof/Basic.lean`, and run `PATH="$HOME/.elan/bin:$PATH" lake build IsotropicGroverProof.QuantumChannel` to verify RED failure.

- [ ] **Step 2: Implement the `Ket`/`MState`/`POVM` bridge, `depolarizingChannel` emergence, unitary commutation, and `Circuit.size` theorems (GREEN)**

1. Implement `vecToReal`, `realToVec`, norm identity `sum_norm_sq_realToVec`, `ketToReal`, `realToKet`, `unitaryToRealIso`, `computationalPOVM`, and Born-rule equivalences (`succProb_ketToReal_eq_born`).
2. Define `depolarizingChannel` directly via `MatrixMap` convex combination (`(σ ^ 2 : ℂ) • CPTPMap.id.map + (1 - σ ^ 2 : ℂ) • (CPTPMap.replacement MState.uniform).map`) so `(depolarizingChannel n σ hσ ρ).m` simplifies cleanly.
3. Prove `isotropicOneStep_eq_depolarizingChannel` and `noisyTrajectory_eq_depolarizingChannel` by splitting `(pureDensityMatrix n Ψ x y).re` and `.im` into linear combinations of `⟪Ψ, stdBasisVec ...⟫_ℝ * ⟪Ψ, stdBasisVec ...⟫_ℝ`, applying `noisyTrajectory_bilinear`, and observing that off-diagonal even/odd inner products `⟪stdBasisVec n (succProbIdx0 n x), stdBasisVec n (succProbIdx1 n y)⟫_ℝ = 0` vanish identically while `⟪idx0 x, idx0 y⟫ + ⟪idx1 x, idx1 y⟫ = if x = y then 2 else 0` (`2 / (2 * 2^n) = 1 / 2^n`, matching `(MState.uniform : MState (Fin (2 ^ n))).m x y`)!
4. Prove `depolarizingChannel_comm_ofUnitary`, `depolarizingChannel_compose`, `ofUnitary_mul`, `noisyCircuitChannel_eq`, and `noisyCircuit_bornProb` by structural induction on `c : Circuit n`, plus `#guard_msgs in #print axioms noisyCircuit_bornProb` confirming `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 3: Run full `lake build --wfail`**

Run: `PATH="$HOME/.elan/bin:$PATH" lake build --wfail`
Expected: Exit code 0, zero errors, zero warnings.

- [ ] **Step 4: Commit**

```bash
git add IsotropicGroverProof/QuantumChannel.lean IsotropicGroverProof/Basic.lean
git commit -m "feat: bridge isotropic errors to QuantumInfo CPTPMap depolarizing channel and Circuit.size"
```
