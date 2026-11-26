-- IsotropicGroverProof/QuantumChannel.lean
-- Bridge from isotropic sphere errors on E n to QuantumInfo CPTPMap depolarizing channels
-- and QuantumComputation Circuit.size.

import QuantumInfo.States.Pure.Braket
import QuantumInfo.States.Mixed.MState
import QuantumInfo.Channels.CPTP
import QuantumInfo.Measurements.POVM
import QuantumComputation.Circuits.Basic
import QuantumComputation.Circuits.ResourceCounting
import QuantumComputation.Primitives.Measure
import IsotropicGroverProof.Sequential

/-!
# Bridge to `QuantumInfo` Channels and `QuantumComputation` Circuits

Connects the real-sphere isotropic error model on `E n = EuclideanSpace ℝ (Fin (2 * 2^n))` to:
1. `Physlib`'s `QuantumInfo` pure/mixed states (`Ket`, `MState.pure`, `MState.uniform`),
   completely positive trace-preserving channels (`CPTPMap`), and `POVM` Born-rule measurements.
2. `formal-quantum-computation`'s syntactic circuits (`Circuit n`), whole-system unitary semantics
   (`Circuit.eval`), computational-basis observables (`compProjObs`), and primitive gate count
   (`Circuit.size`).

Main results:
- `succProb_ketToReal_eq_born`: equivalence between `succProb` on `E n`, squared ket amplitude,
  pure density-matrix diagonal, `MState.exp_val (compProjObs w).1`, and `POVM.measure`.
- `isotropicOneStep_eq_depolarizingChannel` and `noisyTrajectory_eq_depolarizingChannel`:
  averaging the rank-1 density matrix `pureDensityMatrix` over isotropic sphere errors yields
  `depolarizingChannel` (`ρ ↦ σ² ρ + (1 - σ²) MState.uniform`) entrywise.
- `depolarizingChannel_comm_ofUnitary`, `depolarizingChannel_compose`, `noisyCircuitChannel_eq`,
  `noisyCircuit_trajectory_eq_channel`, `noisyCircuit_trajectory_succProb_eq_measure`,
  `noisyCircuit_bornProb`, and `noisyCircuit_bornProb_pure`: gate-by-gate depolarizing noise
  across any `c : Circuit n` equates the microscopic real-sphere Markov trajectory of
  `circuitUnitaries c` with `noisyCircuitChannel σ hσ c` and composes into
  `depolarizingChannel n (σ ^ c.size) _ ∘ₘ CPTPMap.ofUnitary c.eval`, deriving the gate count
  `G = c.size` directly from circuit syntax.
-/

namespace IsotropicGrover

open MeasureTheory InnerProductSpace Real
open scoped Matrix ComplexOrder

/-! ## Interval arithmetic helpers on `[0, 1]` -/

lemma mul_mem_Icc_zero_one {σ₁ σ₂ : ℝ} (h₁ : σ₁ ∈ Set.Icc 0 1) (h₂ : σ₂ ∈ Set.Icc 0 1) :
    σ₁ * σ₂ ∈ Set.Icc 0 1 :=
  ⟨mul_nonneg h₁.1 h₂.1, by nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]⟩

lemma pow_mem_Icc_zero_one {σ : ℝ} (hσ : σ ∈ Set.Icc 0 1) (k : ℕ) :
    σ ^ k ∈ Set.Icc 0 1 :=
  ⟨pow_nonneg hσ.1 k, pow_le_one₀ hσ.1 hσ.2⟩

/-! ## Complex ↔ Real Hilbert space bridge -/

/-- Map a complex `n`-qubit amplitude vector `Fin (2 ^ n) → ℂ` into the real Euclidean space
    `E n = EuclideanSpace ℝ (Fin (2 * 2 ^ n))` by placing real parts at even indices `2x` and
    imaginary parts at odd indices `2x + 1`. -/
noncomputable def vecToReal {n : ℕ} (v : Fin (2 ^ n) → ℂ) : E n :=
  WithLp.toLp 2 fun i : Fin (d n) =>
    let x : Fin (2 ^ n) := ⟨i.val / 2, by have := i.isLt; simp only [d] at this; omega⟩
    if i.val % 2 = 0 then (v x).re else (v x).im

/-- Reconstruct a complex `n`-qubit amplitude vector `Fin (2 ^ n) → ℂ` from a real state vector
    `Φ : E n` via `x ↦ ⟨Φ (2x), Φ (2x + 1)⟩`. -/
noncomputable def realToVec {n : ℕ} (Φ : E n) (x : Fin (2 ^ n)) : ℂ :=
  ⟨Φ (succProbIdx0 n x), Φ (succProbIdx1 n x)⟩

@[simp]
lemma realToVec_re {n : ℕ} (Φ : E n) (x : Fin (2 ^ n)) :
    (realToVec Φ x).re = Φ (succProbIdx0 n x) := rfl

@[simp]
lemma realToVec_im {n : ℕ} (Φ : E n) (x : Fin (2 ^ n)) :
    (realToVec Φ x).im = Φ (succProbIdx1 n x) := rfl

@[simp]
lemma vecToReal_succProbIdx0 {n : ℕ} (v : Fin (2 ^ n) → ℂ) (x : Fin (2 ^ n)) :
    vecToReal v (succProbIdx0 n x) = (v x).re := by
  change (if (succProbIdx0 n x).val % 2 = 0 then
    (v ⟨(succProbIdx0 n x).val / 2, _⟩).re else
    (v ⟨(succProbIdx0 n x).val / 2, _⟩).im) = (v x).re
  have hx : (⟨(succProbIdx0 n x).val / 2,
      by have := (succProbIdx0 n x).isLt; simp only [d] at this; omega⟩ : Fin (2 ^ n)) = x := by
    ext; dsimp [succProbIdx0]; omega
  have hmod : (succProbIdx0 n x).val % 2 = 0 := by dsimp [succProbIdx0]; omega
  simp [hx, hmod]

@[simp]
lemma vecToReal_succProbIdx1 {n : ℕ} (v : Fin (2 ^ n) → ℂ) (x : Fin (2 ^ n)) :
    vecToReal v (succProbIdx1 n x) = (v x).im := by
  change (if (succProbIdx1 n x).val % 2 = 0 then
    (v ⟨(succProbIdx1 n x).val / 2, _⟩).re else
    (v ⟨(succProbIdx1 n x).val / 2, _⟩).im) = (v x).im
  have hx : (⟨(succProbIdx1 n x).val / 2,
      by have := (succProbIdx1 n x).isLt; simp only [d] at this; omega⟩ : Fin (2 ^ n)) = x := by
    ext; dsimp [succProbIdx1]; omega
  have hmod : (succProbIdx1 n x).val % 2 ≠ 0 := by dsimp [succProbIdx1]; omega
  simp [hx, hmod]

@[simp]
theorem realToVec_vecToReal {n : ℕ} (v : Fin (2 ^ n) → ℂ) :
    realToVec (vecToReal v) = v := by
  ext x : 1
  apply Complex.ext <;> simp

@[simp]
theorem vecToReal_realToVec {n : ℕ} (Φ : E n) :
    vecToReal (realToVec Φ) = Φ := by
  ext i
  change (let x : Fin (2 ^ n) := ⟨i.val / 2, by have := i.isLt; simp only [d] at this; omega⟩
    if i.val % 2 = 0 then (realToVec Φ x).re else (realToVec Φ x).im) = Φ.ofLp i
  dsimp only [realToVec_re, realToVec_im]
  by_cases hmod : i.val % 2 = 0
  · rw [ite_eq_left hmod]
    exact congrArg Φ.ofLp (Fin.ext (by dsimp [succProbIdx0]; omega))
  · rw [ite_eq_right hmod]
    exact congrArg Φ.ofLp (Fin.ext (by dsimp [succProbIdx1]; omega))

lemma realToVec_add {n : ℕ} (Φ₁ Φ₂ : E n) :
    realToVec (Φ₁ + Φ₂) = realToVec Φ₁ + realToVec Φ₂ := by
  ext x : 1
  apply Complex.ext <;> simp

lemma realToVec_smul {n : ℕ} (c : ℝ) (Φ : E n) :
    realToVec (c • Φ) = (c : ℂ) • realToVec Φ := by
  ext x : 1
  apply Complex.ext <;> simp

lemma vecToReal_add {n : ℕ} (v₁ v₂ : Fin (2 ^ n) → ℂ) :
    vecToReal (v₁ + v₂) = vecToReal v₁ + vecToReal v₂ := by
  rw [← vecToReal_realToVec (vecToReal v₁ + vecToReal v₂), realToVec_add,
      realToVec_vecToReal, realToVec_vecToReal]

lemma vecToReal_smul {n : ℕ} (c : ℝ) (v : Fin (2 ^ n) → ℂ) :
    vecToReal ((c : ℂ) • v) = c • vecToReal v := by
  rw [← vecToReal_realToVec (c • vecToReal v), realToVec_smul, realToVec_vecToReal]

lemma norm_sq_realToVec_eq_succProb {n : ℕ} (Φ : E n) (w : Fin (2 ^ n)) :
    ‖realToVec Φ w‖ ^ 2 = succProb n Φ w := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [realToVec_re, realToVec_im, succProb, inner_stdBasisVec_eq_apply, sq]

/-- Parseval identity across the complex/real state-vector bijection:
    `∑ x, ‖realToVec Φ x‖ ^ 2 = ‖Φ‖ ^ 2`. -/
theorem sum_norm_sq_realToVec {n : ℕ} (Φ : E n) :
    ∑ x : Fin (2 ^ n), ‖realToVec Φ x‖ ^ 2 = ‖Φ‖ ^ 2 := by
  simp_rw [norm_sq_realToVec_eq_succProb, sum_succProb_eq_norm_sq]

lemma norm_sq_vecToReal {n : ℕ} (v : Fin (2 ^ n) → ℂ) :
    ‖vecToReal v‖ ^ 2 = ∑ x : Fin (2 ^ n), ‖v x‖ ^ 2 := by
  rw [← sum_norm_sq_realToVec (vecToReal v), realToVec_vecToReal]

/-- Embed a normalized `QuantumInfo` ket `ψ : Ket (Fin (2 ^ n))` into the real unit sphere
    in `E n`. -/
noncomputable def ketToReal {n : ℕ} (ψ : Ket (Fin (2 ^ n))) : E n :=
  vecToReal ψ.vec

@[simp]
theorem norm_ketToReal {n : ℕ} (ψ : Ket (Fin (2 ^ n))) : ‖ketToReal ψ‖ = 1 := by
  have hsq : ‖ketToReal ψ‖ ^ 2 = 1 := by
    rw [ketToReal, norm_sq_vecToReal, ψ.normalized']
  nlinarith [norm_nonneg (ketToReal ψ)]

@[simp]
lemma realToVec_ketToReal {n : ℕ} (ψ : Ket (Fin (2 ^ n))) :
    realToVec (ketToReal ψ) = ψ.vec :=
  realToVec_vecToReal ψ.vec

/-- Reconstruct a normalized `Ket (Fin (2 ^ n))` from a unit vector `Φ : E n`. -/
noncomputable def realToKet {n : ℕ} (Φ : E n) (hΦ : ‖Φ‖ = 1) : Ket (Fin (2 ^ n)) where
  vec := realToVec Φ
  normalized' := by rw [sum_norm_sq_realToVec, hΦ, one_pow]

@[simp]
theorem realToKet_ketToReal {n : ℕ} (ψ : Ket (Fin (2 ^ n))) :
    realToKet (ketToReal ψ) (norm_ketToReal ψ) = ψ := by
  ext x
  exact congr_fun (realToVec_ketToReal ψ) x

@[simp]
theorem ketToReal_realToKet {n : ℕ} (Φ : E n) (hΦ : ‖Φ‖ = 1) :
    ketToReal (realToKet Φ hΦ) = Φ :=
  vecToReal_realToVec Φ

/-- Lift an `n`-qubit unitary matrix `U : 𝐔[Fin (2 ^ n)]` to a real linear isometry equivalence
    on `E n`. -/
noncomputable def unitaryToRealIso {n : ℕ} (U : 𝐔[Fin (2 ^ n)]) : E n ≃ₗᵢ[ℝ] E n where
  toFun Φ := vecToReal (U.val *ᵥ realToVec Φ)
  invFun Φ := vecToReal ((star U).val *ᵥ realToVec Φ)
  map_add' x y := by
    rw [realToVec_add, Matrix.mulVec_add, vecToReal_add]
  map_smul' c x := by
    simp only [RingHom.id_apply, realToVec_smul, Matrix.mulVec_smul, vecToReal_smul]
  left_inv Φ := by
    dsimp only
    have hU : (star U).val * U.val = 1 := U.2.1
    rw [realToVec_vecToReal, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec, vecToReal_realToVec]
  right_inv Φ := by
    dsimp only
    have hU : U.val * (star U).val = 1 := U.2.2
    rw [realToVec_vecToReal, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec, vecToReal_realToVec]
  norm_map' Φ := by
    change ‖vecToReal (U.val *ᵥ realToVec Φ)‖ = ‖Φ‖
    have hsq : ‖vecToReal (U.val *ᵥ realToVec Φ)‖ ^ 2 = ‖Φ‖ ^ 2 := by
      rw [norm_sq_vecToReal, ← sum_norm_sq_realToVec Φ]
      simp_rw [← Complex.normSq_eq_norm_sq]
      exact sum_normSq_unitary_mulVec U (realToVec Φ)
    nlinarith [norm_nonneg (vecToReal (U.val *ᵥ realToVec Φ)), norm_nonneg Φ,
      sq_nonneg (‖vecToReal (U.val *ᵥ realToVec Φ)‖ - ‖Φ‖)]

@[simp]
lemma unitaryToRealIso_one {n : ℕ} :
    unitaryToRealIso (1 : 𝐔[Fin (2 ^ n)]) = LinearIsometryEquiv.refl ℝ (E n) := by
  ext Φ i
  change (vecToReal ((1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) *ᵥ realToVec Φ)) i = Φ i
  rw [Matrix.one_mulVec, vecToReal_realToVec]

/-- Apply a unitary `U : 𝐔[Fin (2 ^ n)]` to a normalized `Ket (Fin (2 ^ n))`. -/
noncomputable def applyUnitaryKet {n : ℕ} (U : 𝐔[Fin (2 ^ n)]) (ψ : Ket (Fin (2 ^ n))) :
    Ket (Fin (2 ^ n)) where
  vec := U.val *ᵥ ψ.vec
  normalized' := by
    simp_rw [← Complex.normSq_eq_norm_sq, sum_normSq_unitary_mulVec, Complex.normSq_eq_norm_sq]
    exact ψ.normalized'

@[simp]
lemma ketToReal_applyUnitaryKet {n : ℕ} (U : 𝐔[Fin (2 ^ n)]) (ψ : Ket (Fin (2 ^ n))) :
    ketToReal (applyUnitaryKet U ψ) = unitaryToRealIso U (ketToReal ψ) := by
  simp [ketToReal, applyUnitaryKet, unitaryToRealIso]

@[simp]
lemma applyUnitaryKet_one {n : ℕ} (ψ : Ket (Fin (2 ^ n))) :
    applyUnitaryKet 1 ψ = ψ := by
  ext x
  exact congr_fun (Matrix.one_mulVec ψ.vec) x

@[simp]
lemma applyUnitaryKet_mul {n : ℕ} (U₂ U₁ : 𝐔[Fin (2 ^ n)]) (ψ : Ket (Fin (2 ^ n))) :
    applyUnitaryKet (U₂ * U₁) ψ = applyUnitaryKet U₂ (applyUnitaryKet U₁ ψ) := by
  ext x
  exact congr_fun (Matrix.mulVec_mulVec ψ.vec U₂.val U₁.val).symm x

@[simp]
lemma ofUnitary_apply_m {n : ℕ} (U : 𝐔[Fin (2 ^ n)]) (ρ : MState (Fin (2 ^ n))) :
    (CPTPMap.ofUnitary U ρ).m = U.val * ρ.m * U.valᴴ := rfl

lemma ofUnitary_pure {n : ℕ} (U : 𝐔[Fin (2 ^ n)]) (ψ : Ket (Fin (2 ^ n))) :
    CPTPMap.ofUnitary U (MState.pure ψ) = MState.pure (applyUnitaryKet U ψ) := by
  apply MState.ext_m
  have h : (MState.pure ψ).m = pureStateDensity ψ.vec := rfl
  have h' : (MState.pure (applyUnitaryKet U ψ)).m = pureStateDensity (U.val *ᵥ ψ.vec) := rfl
  rw [ofUnitary_apply_m, h, h', matrix_conj_pureStateDensity]

/-- Ideal noiseless ket after applying a list of `n`-qubit unitaries left-to-right. -/
noncomputable def idealUnitaryTrajectory {n : ℕ} (us : List 𝐔[Fin (2 ^ n)])
    (ψ₀ : Ket (Fin (2 ^ n))) : Ket (Fin (2 ^ n)) :=
  us.foldl (fun ψ U => applyUnitaryKet U ψ) ψ₀

@[simp]
lemma idealUnitaryTrajectory_nil {n : ℕ} (ψ₀ : Ket (Fin (2 ^ n))) :
    idealUnitaryTrajectory ([] : List 𝐔[Fin (2 ^ n)]) ψ₀ = ψ₀ := rfl

@[simp]
lemma idealUnitaryTrajectory_cons {n : ℕ} (U : 𝐔[Fin (2 ^ n)]) (rest : List 𝐔[Fin (2 ^ n)])
    (ψ₀ : Ket (Fin (2 ^ n))) :
    idealUnitaryTrajectory (U :: rest) ψ₀ =
    idealUnitaryTrajectory rest (applyUnitaryKet U ψ₀) := rfl

@[simp]
lemma idealUnitaryTrajectory_append {n : ℕ} (us₁ us₂ : List 𝐔[Fin (2 ^ n)])
    (ψ₀ : Ket (Fin (2 ^ n))) :
    idealUnitaryTrajectory (us₁ ++ us₂) ψ₀ =
    idealUnitaryTrajectory us₂ (idealUnitaryTrajectory us₁ ψ₀) :=
  List.foldl_append

@[simp]
lemma ketToReal_idealUnitaryTrajectory {n : ℕ} (us : List 𝐔[Fin (2 ^ n)])
    (ψ₀ : Ket (Fin (2 ^ n))) :
    ketToReal (idealUnitaryTrajectory us ψ₀) =
    idealGateTrajectory (us.map unitaryToRealIso) (ketToReal ψ₀) := by
  induction us generalizing ψ₀ with
  | nil => rfl
  | cons U rest ih =>
    simp only [idealUnitaryTrajectory, List.foldl_cons, List.map_cons, idealGateTrajectory_cons,
      ← ketToReal_applyUnitaryKet]
    exact ih (applyUnitaryKet U ψ₀)

/-! ## Computational-basis `POVM` and Born-rule equivalences -/

/-- The `n`-qubit computational-basis projective measurement packaged as a `QuantumInfo` `POVM`. -/
noncomputable def computationalPOVM (n : ℕ) : POVM (Fin (2 ^ n)) (Fin (2 ^ n)) where
  mats w := (compProjObs w).1
  nonneg w := (compProjObs w).2.1
  normalized := by
    apply HermitianMat.ext
    rw [HermitianMat.mat_finset_sum, HermitianMat.mat_one]
    have hmat : ∀ w : Fin (2 ^ n), ((compProjObs w).1).mat = compProj w := fun _ => rfl
    simp_rw [hmat]
    exact compProj_sum

lemma computationalPOVM_measure_eq_exp_val {n : ℕ} (ρ : MState (Fin (2 ^ n)))
    (w : Fin (2 ^ n)) :
    ((computationalPOVM n).measure ρ w : ℝ) = ρ.exp_val (compProjObs w).1 := by
  change ⟪(compProjObs w).1, ρ.M⟫_ℝ = ⟪ρ.M, (compProjObs w).1⟫_ℝ
  exact HermitianMat.inner_comm _ _

lemma exp_val_compProjObs_eq_re_diag {n : ℕ} (ρ : MState (Fin (2 ^ n))) (w : Fin (2 ^ n)) :
    ρ.exp_val (compProjObs w).1 = (ρ.m w w).re := by
  have htr : (ρ.M.mat * ((compProjObs w).1).mat).trace = ρ.m w w := by
    change (ρ.m * Matrix.single w w (1 : ℂ)).trace = ρ.m w w
    simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]
  rw [MState.exp_val, HermitianMat.inner_eq_re_trace, htr, RCLike.re_to_complex]

/-- Born-rule equivalence: `succProb` on the real unit vector `ketToReal ψ` coincides with
    the squared amplitude `‖ψ w‖ ^ 2`, the diagonal entry `((MState.pure ψ).m w w).re`,
    the observable expectation `(MState.pure ψ).exp_val (compProjObs w).1`, and the
    `computationalPOVM` outcome probability. -/
theorem succProb_ketToReal_eq_born {n : ℕ} (ψ : Ket (Fin (2 ^ n))) (w : Fin (2 ^ n)) :
    succProb n (ketToReal ψ) w = ‖ψ w‖ ^ 2 ∧
    succProb n (ketToReal ψ) w = ((MState.pure ψ).m w w).re ∧
    succProb n (ketToReal ψ) w = (MState.pure ψ).exp_val (compProjObs w).1 ∧
    succProb n (ketToReal ψ) w = ((computationalPOVM n).measure (MState.pure ψ) w : ℝ) := by
  have h1 : succProb n (ketToReal ψ) w = ‖ψ w‖ ^ 2 := by
    rw [← norm_sq_realToVec_eq_succProb, realToVec_ketToReal, Ket.apply]
  have h2 : ((MState.pure ψ).m w w).re = ‖ψ w‖ ^ 2 := by
    rw [MState.pure_apply, Complex.mul_conj, ← Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have h3 : (MState.pure ψ).exp_val (compProjObs w).1 = ((MState.pure ψ).m w w).re :=
    exp_val_compProjObs_eq_re_diag (MState.pure ψ) w
  have h4 : ((computationalPOVM n).measure (MState.pure ψ) w : ℝ) =
      (MState.pure ψ).exp_val (compProjObs w).1 :=
    computationalPOVM_measure_eq_exp_val (MState.pure ψ) w
  exact ⟨h1, h1.trans h2.symm, h1.trans (h3.trans h2).symm,
    h1.trans (h4.trans (h3.trans h2)).symm⟩

/-! ## Rank-1 density matrix on `E n` and the depolarizing `CPTPMap` -/

/-- Rank-1 complex matrix `|v⟩⟨v|` associated with any real vector `v : E n` without requiring
    a dependent unit-norm proof. -/
noncomputable def pureDensityMatrix (n : ℕ) (v : E n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun x y => realToVec v x * starRingEnd ℂ (realToVec v y)

@[simp]
lemma pureDensityMatrix_apply (n : ℕ) (v : E n) (x y : Fin (2 ^ n)) :
    pureDensityMatrix n v x y = realToVec v x * starRingEnd ℂ (realToVec v y) := rfl

/-- On embedded kets, `pureDensityMatrix` agrees identically with `(MState.pure ψ).m`. -/
theorem pureDensityMatrix_ketToReal {n : ℕ} (ψ : Ket (Fin (2 ^ n))) :
    pureDensityMatrix n (ketToReal ψ) = (MState.pure ψ).m := by
  ext x y
  simp [pureDensityMatrix, Ket.apply]

lemma uniform_m_apply (n : ℕ) (x y : Fin (2 ^ n)) :
    (MState.uniform (d := Fin (2 ^ n))).m x y =
    if x = y then ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) else 0 := by
  change Matrix.diagonal
    (fun z : Fin (2 ^ n) => ((ProbDistribution.uniform z : ℝ) : ℂ)) x y = _
  by_cases hxy : x = y
  · subst hxy
    simp [ProbDistribution.uniform_def]
  · simp [hxy]

lemma uniform_m_eq_smul_one (n : ℕ) :
    (MState.uniform (d := Fin (2 ^ n))).m =
    ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  ext x y
  rw [uniform_m_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- The `n`-qubit depolarizing channel `ρ ↦ σ² ρ + (1 - σ²) MState.uniform` on `σ ∈ [0, 1]`
    constructed as a `CPTPMap`. -/
noncomputable def depolarizingChannel (n : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) :
    CPTPMap (Fin (2 ^ n)) (Fin (2 ^ n)) where
  toLinearMap :=
    ((σ ^ 2 : ℝ) : ℂ) • (CPTPMap.id (dIn := Fin (2 ^ n))).map +
    ((1 - σ ^ 2 : ℝ) : ℂ) •
      (CPTPMap.replacement (dIn := Fin (2 ^ n)) (MState.uniform (d := Fin (2 ^ n)))).map
  cp := by
    have h1 : (0 : ℂ) ≤ ((σ ^ 2 : ℝ) : ℂ) := by
      simp [Complex.le_def, -Complex.ofReal_pow, sq_nonneg σ]
    have h2 : (0 : ℂ) ≤ ((1 - σ ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.le_def, Complex.zero_re, Complex.ofReal_re, Complex.zero_im,
        Complex.ofReal_im, and_true]
      nlinarith [hσ.1, hσ.2]
    exact ((CPTPMap.id (dIn := Fin (2 ^ n))).cp.smul h1).add
      ((CPTPMap.replacement (MState.uniform (d := Fin (2 ^ n)))).cp.smul h2)
  TP :=
    MatrixMap.IsTracePreserving.unit_linear
      (CPTPMap.id (dIn := Fin (2 ^ n))).TP
      (CPTPMap.replacement (MState.uniform (d := Fin (2 ^ n)))).TP
      (by push_cast; ring)

@[simp]
lemma depolarizingChannel_apply_m (n : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (ρ : MState (Fin (2 ^ n))) :
    (depolarizingChannel n σ hσ ρ).m =
    ((σ ^ 2 : ℝ) : ℂ) • ρ.m +
      ((1 - σ ^ 2 : ℝ) : ℂ) • (MState.uniform (d := Fin (2 ^ n))).m := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  dsimp only [depolarizingChannel, HPMap.map]
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      ← CPTPMap.mat_coe_eq_apply_mat, ← CPTPMap.mat_coe_eq_apply_mat,
      CPTPMap.id_MState, CPTPMap.replacement_apply]

@[simp]
lemma depolarizingChannel_one (n : ℕ) (h1 : (1 : ℝ) ∈ Set.Icc 0 1) :
    depolarizingChannel n 1 h1 = CPTPMap.id := by
  apply CPTPMap.funext
  intro ρ
  apply MState.ext_m
  simp [depolarizingChannel_apply_m]

/-! ## Emergence of `depolarizingChannel` from isotropic sphere errors -/

private lemma pureDensityMatrix_re_eq {n : ℕ} (Ψ : E n) (x y : Fin (2 ^ n)) :
    (pureDensityMatrix n Ψ x y).re =
    ⟪Ψ, stdBasisVec n (succProbIdx0 n x)⟫_ℝ * ⟪Ψ, stdBasisVec n (succProbIdx0 n y)⟫_ℝ +
    ⟪Ψ, stdBasisVec n (succProbIdx1 n x)⟫_ℝ * ⟪Ψ, stdBasisVec n (succProbIdx1 n y)⟫_ℝ := by
  simp only [pureDensityMatrix_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    realToVec_re, realToVec_im, inner_stdBasisVec_eq_apply]
  ring

private lemma pureDensityMatrix_im_eq {n : ℕ} (Ψ : E n) (x y : Fin (2 ^ n)) :
    (pureDensityMatrix n Ψ x y).im =
    ⟪Ψ, stdBasisVec n (succProbIdx1 n x)⟫_ℝ * ⟪Ψ, stdBasisVec n (succProbIdx0 n y)⟫_ℝ -
    ⟪Ψ, stdBasisVec n (succProbIdx0 n x)⟫_ℝ * ⟪Ψ, stdBasisVec n (succProbIdx1 n y)⟫_ℝ := by
  simp only [pureDensityMatrix_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    realToVec_re, realToVec_im, inner_stdBasisVec_eq_apply]
  ring

theorem noisyTrajectory_pureDensityMatrix_re {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1) (x y : Fin (2 ^ n)) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => (pureDensityMatrix n Ψ x y).re) =
    σ ^ (2 * gates.length) * (pureDensityMatrix n (idealGateTrajectory gates Φ₀) x y).re +
      (1 - σ ^ (2 * gates.length)) * (if x = y then 1 / (2 ^ n : ℝ) else 0) := by
  let e0x := stdBasisVec n (succProbIdx0 n x)
  let e1x := stdBasisVec n (succProbIdx1 n x)
  let e0y := stdBasisVec n (succProbIdx0 n y)
  let e1y := stdBasisVec n (succProbIdx1 n y)
  have hc0 : Continuous (fun Ψ : E n => ⟪Ψ, e0x⟫_ℝ * ⟪Ψ, e0y⟫_ℝ) :=
    (continuous_id.inner continuous_const).mul (continuous_id.inner continuous_const)
  have hc1 : Continuous (fun Ψ : E n => ⟪Ψ, e1x⟫_ℝ * ⟪Ψ, e1y⟫_ℝ) :=
    (continuous_id.inner continuous_const).mul (continuous_id.inner continuous_const)
  simp_rw [pureDensityMatrix_re_eq]
  rw [noisyTrajectoryExpectation_add σ hσ gates Φ₀ hΦ₀ hc0 hc1,
      noisyTrajectory_bilinear σ hσ gates Φ₀ hΦ₀ e0x e0y,
      noisyTrajectory_bilinear σ hσ gates Φ₀ hΦ₀ e1x e1y]
  have h0_iff : succProbIdx0 n x = succProbIdx0 n y ↔ x = y := ⟨succProbIdx0_inj, congrArg _⟩
  have h1_iff : succProbIdx1 n x = succProbIdx1 n y ↔ x = y := ⟨succProbIdx1_inj, congrArg _⟩
  have h00 : ⟪e0x, e0y⟫_ℝ = if x = y then 1 else 0 := by
    simp [e0x, e0y, inner_stdBasisVec, h0_iff]
  have h11 : ⟪e1x, e1y⟫_ℝ = if x = y then 1 else 0 := by
    simp [e1x, e1y, inner_stdBasisVec, h1_iff]
  have hd_eq : (d n : ℝ) = 2 * (2 ^ n : ℝ) := by simp only [d]; push_cast; ring
  have hN_ne : (2 ^ n : ℝ) ≠ 0 := by positivity
  rw [h00, h11, hd_eq]
  dsimp only [e0x, e1x, e0y, e1y]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte]
    field_simp [hN_ne]
    ring
  · simp only [hxy, ↓reduceIte, mul_zero, add_zero]
    ring

theorem noisyTrajectory_pureDensityMatrix_im {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1) (x y : Fin (2 ^ n)) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => (pureDensityMatrix n Ψ x y).im) =
    σ ^ (2 * gates.length) * (pureDensityMatrix n (idealGateTrajectory gates Φ₀) x y).im := by
  let e0x := stdBasisVec n (succProbIdx0 n x)
  let e1x := stdBasisVec n (succProbIdx1 n x)
  let e0y := stdBasisVec n (succProbIdx0 n y)
  let e1y := stdBasisVec n (succProbIdx1 n y)
  have hc10 : Continuous (fun Ψ : E n => ⟪Ψ, e1x⟫_ℝ * ⟪Ψ, e0y⟫_ℝ) :=
    (continuous_id.inner continuous_const).mul (continuous_id.inner continuous_const)
  have hc01 : Continuous (fun Ψ : E n => ⟪Ψ, e0x⟫_ℝ * ⟪Ψ, e1y⟫_ℝ) :=
    (continuous_id.inner continuous_const).mul (continuous_id.inner continuous_const)
  simp_rw [pureDensityMatrix_im_eq]
  rw [noisyTrajectoryExpectation_sub σ hσ gates Φ₀ hΦ₀ hc10 hc01,
      noisyTrajectory_bilinear σ hσ gates Φ₀ hΦ₀ e1x e0y,
      noisyTrajectory_bilinear σ hσ gates Φ₀ hΦ₀ e0x e1y]
  have h10 : ⟪e1x, e0y⟫_ℝ = 0 := by
    dsimp only [e1x, e0y]
    rw [inner_stdBasisVec, ite_eq_right (succProbIdx0_ne_succProbIdx1 y x).symm]
  have h01 : ⟪e0x, e1y⟫_ℝ = 0 := by
    dsimp only [e0x, e1y]
    rw [inner_stdBasisVec, ite_eq_right (succProbIdx0_ne_succProbIdx1 x y)]
  rw [h10, h01]
  dsimp only [e0x, e1x, e0y, e1y]
  ring

private lemma continuous_realToVec_apply {n : ℕ} (x : Fin (2 ^ n)) :
    Continuous (fun Φ : E n => realToVec Φ x) := by
  have heq : (fun Φ : E n => realToVec Φ x) =
      fun Φ => (Φ (succProbIdx0 n x) : ℂ) + (Φ (succProbIdx1 n x) : ℂ) * Complex.I := by
    ext Φ; exact (Complex.re_add_im (realToVec Φ x)).symm
  rw [heq]
  have h0 : Continuous (fun Φ : E n => Φ (succProbIdx0 n x)) :=
    PiLp.continuous_apply 2 _ (succProbIdx0 n x)
  have h1 : Continuous (fun Φ : E n => Φ (succProbIdx1 n x)) :=
    PiLp.continuous_apply 2 _ (succProbIdx1 n x)
  exact (Complex.continuous_ofReal.comp h0).add
    ((Complex.continuous_ofReal.comp h1).mul continuous_const)

private lemma continuous_pureDensityMatrix_apply {n : ℕ} (x y : Fin (2 ^ n)) :
    Continuous (fun Φ : E n => pureDensityMatrix n Φ x y) :=
  (continuous_realToVec_apply x).mul (continuous_star.comp (continuous_realToVec_apply y))

/-- Complex-valued expectation of `f : E n → ℂ` along the multi-gate pure-state Markov
    trajectory `Ψ_{k+1} = cos θ_{k+1} (U_{k+1} Ψ_k) + sin θ_{k+1} e_{2,k+1}`. -/
noncomputable def noisyTrajectoryExpectationℂ (n : ℕ) (σ : ℝ) :
    List (E n ≃ₗᵢ[ℝ] E n) → E n → (E n → ℂ) → ℂ
  | [] => fun Φ₀ f => f Φ₀
  | U :: rest => fun Φ₀ f =>
      ∫ θ, ∫ e₂, noisyTrajectoryExpectationℂ n σ rest (isotropicError (U Φ₀) e₂ θ) f
            ∂(perpSphereMeasure (U Φ₀)) ∂(poissonAngleMeasure (d n) σ)

@[simp]
lemma noisyTrajectoryExpectationℂ_nil (n : ℕ) (σ : ℝ) (Φ₀ : E n) (f : E n → ℂ) :
    noisyTrajectoryExpectationℂ n σ [] Φ₀ f = f Φ₀ := rfl

@[simp]
lemma noisyTrajectoryExpectationℂ_cons (n : ℕ) (σ : ℝ) (U : E n ≃ₗᵢ[ℝ] E n)
    (rest : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (f : E n → ℂ) :
    noisyTrajectoryExpectationℂ n σ (U :: rest) Φ₀ f =
    ∫ θ, ∫ e₂, noisyTrajectoryExpectationℂ n σ rest (isotropicError (U Φ₀) e₂ θ) f
          ∂(perpSphereMeasure (U Φ₀)) ∂(poissonAngleMeasure (d n) σ) := rfl

private lemma integral_mk_complex {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {r i : α → ℝ} (hr : Integrable r μ) (hi : Integrable i μ) :
    ∫ x, (⟨r x, i x⟩ : ℂ) ∂μ = ⟨∫ x, r x ∂μ, ∫ x, i x ∂μ⟩ := by
  have hint : Integrable (fun x => (⟨r x, i x⟩ : ℂ)) μ := Integrable.re_im_iff.mp ⟨hr, hi⟩
  exact Complex.ext (Complex.reCLM.integral_comp_comm hint).symm
    (Complex.imCLM.integral_comp_comm hint).symm

/-- Componentwise compatibility of `noisyTrajectoryExpectationℂ` with `noisyTrajectoryExpectation`
    for any observable `f : E n → ℂ` continuous on the unit sphere. -/
theorem noisyTrajectoryExpectationℂ_eq_re_im_of_continuousOn {n : ℕ} (σ : ℝ)
    (hσ : σ ∈ Set.Icc 0 1) (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1)
    {f : E n → ℂ} (hf : ContinuousOn f (unitSphere n)) :
    noisyTrajectoryExpectationℂ n σ gates Φ₀ f =
    ⟨noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => (f Ψ).re),
     noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => (f Ψ).im)⟩ := by
  induction gates generalizing Φ₀ with
  | nil => rfl
  | cons U rest ih =>
    simp only [noisyTrajectoryExpectationℂ_cons, noisyTrajectoryExpectation_cons]
    have hU : ‖U Φ₀‖ = 1 := by rw [U.norm_map]; exact hΦ₀
    have hfr := noisyTrajectoryExpectation_continuousOn_unitSphere σ hσ rest
      (Complex.continuous_re.comp_continuousOn hf)
    have hfi := noisyTrajectoryExpectation_continuousOn_unitSphere σ hσ rest
      (Complex.continuous_im.comp_continuousOn hf)
    have hinner : ∀ θ : ℝ,
        ∫ e₂, noisyTrajectoryExpectationℂ n σ rest (isotropicError (U Φ₀) e₂ θ) f
          ∂(perpSphereMeasure (U Φ₀)) =
        ⟨∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ)
            (fun Ψ => (f Ψ).re) ∂(perpSphereMeasure (U Φ₀)),
         ∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ)
            (fun Ψ => (f Ψ).im) ∂(perpSphereMeasure (U Φ₀))⟩ := by
      intro θ
      have hae : ∀ᵐ e₂ ∂(perpSphereMeasure (U Φ₀)),
          noisyTrajectoryExpectationℂ n σ rest (isotropicError (U Φ₀) e₂ θ) f =
          ⟨noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ)
              (fun Ψ => (f Ψ).re),
           noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ)
              (fun Ψ => (f Ψ).im)⟩ := by
        filter_upwards [ae_isotropicError_mem_sphere hU θ] with e₂ he₂
        exact ih (isotropicError (U Φ₀) e₂ θ) he₂
      rw [integral_congr_ae hae]
      exact integral_mk_complex
        (integrable_perpSphere_of_continuousOn hU θ hfr)
        (integrable_perpSphere_of_continuousOn hU θ hfi)
    simp_rw [hinner]
    exact integral_mk_complex
      (integrable_outer_integral_of_continuousOn σ hσ hU hfr)
      (integrable_outer_integral_of_continuousOn σ hσ hU hfi)

/-- Componentwise compatibility of `noisyTrajectoryExpectationℂ` with `noisyTrajectoryExpectation`
    for continuous `f : E n → ℂ`. -/
theorem noisyTrajectoryExpectationℂ_eq_re_im {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1)
    {f : E n → ℂ} (hf : Continuous f) :
    noisyTrajectoryExpectationℂ n σ gates Φ₀ f =
    ⟨noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => (f Ψ).re),
     noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => (f Ψ).im)⟩ :=
  noisyTrajectoryExpectationℂ_eq_re_im_of_continuousOn σ hσ gates Φ₀ hΦ₀ hf.continuousOn

/-- `noisyTrajectoryExpectationℂ` commutes with `.re` for continuous `f : E n → ℂ`. -/
theorem noisyTrajectoryExpectationℂ_re {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1)
    {f : E n → ℂ} (hf : Continuous f) :
    (noisyTrajectoryExpectationℂ n σ gates Φ₀ f).re =
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => (f Ψ).re) := by
  rw [noisyTrajectoryExpectationℂ_eq_re_im σ hσ gates Φ₀ hΦ₀ hf]

/-- `noisyTrajectoryExpectationℂ` commutes with `.im` for continuous `f : E n → ℂ`. -/
theorem noisyTrajectoryExpectationℂ_im {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1)
    {f : E n → ℂ} (hf : Continuous f) :
    (noisyTrajectoryExpectationℂ n σ gates Φ₀ f).im =
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => (f Ψ).im) := by
  rw [noisyTrajectoryExpectationℂ_eq_re_im σ hσ gates Φ₀ hΦ₀ hf]

/-- Compatibility between the `ℂ`-valued Bochner integral `noisyTrajectoryExpectationℂ` and
    componentwise `noisyTrajectoryExpectation` on `pureDensityMatrix` entries. -/
theorem noisyTrajectoryExpectationℂ_pureDensityMatrix_eq_re_im {n : ℕ} (σ : ℝ)
    (hσ : σ ∈ Set.Icc 0 1) (us : List 𝐔[Fin (2 ^ n)]) (ψ₀ : Ket (Fin (2 ^ n)))
    (x y : Fin (2 ^ n)) :
    noisyTrajectoryExpectationℂ n σ (us.map unitaryToRealIso) (ketToReal ψ₀)
      (fun Ψ => pureDensityMatrix n Ψ x y) =
    ⟨noisyTrajectoryExpectation n σ (us.map unitaryToRealIso) (ketToReal ψ₀)
        (fun Ψ => (pureDensityMatrix n Ψ x y).re),
     noisyTrajectoryExpectation n σ (us.map unitaryToRealIso) (ketToReal ψ₀)
        (fun Ψ => (pureDensityMatrix n Ψ x y).im)⟩ :=
  noisyTrajectoryExpectationℂ_eq_re_im σ hσ _ _ (norm_ketToReal ψ₀)
    (continuous_pureDensityMatrix_apply x y)

/-- **Multi-gate depolarizing channel emergence:** Averaging `pureDensityMatrix` along the
    interleaved unitary/isotropic-error Markov trajectory for `us : List 𝐔[Fin (2 ^ n)]`
    yields
    `(depolarizingChannel n (σ ^ us.length) _ (MState.pure (idealUnitaryTrajectory us ψ₀))).m`
    entrywise. -/
theorem noisyTrajectory_eq_depolarizingChannel {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (us : List 𝐔[Fin (2 ^ n)]) (ψ₀ : Ket (Fin (2 ^ n))) (x y : Fin (2 ^ n)) :
    noisyTrajectoryExpectationℂ n σ (us.map unitaryToRealIso) (ketToReal ψ₀)
      (fun Ψ => pureDensityMatrix n Ψ x y) =
    (depolarizingChannel n (σ ^ us.length) (pow_mem_Icc_zero_one hσ us.length)
      (MState.pure (idealUnitaryTrajectory us ψ₀))).m x y := by
  rw [noisyTrajectoryExpectationℂ_pureDensityMatrix_eq_re_im σ hσ,
      noisyTrajectory_pureDensityMatrix_re σ hσ _ _ (norm_ketToReal ψ₀),
      noisyTrajectory_pureDensityMatrix_im σ hσ _ _ (norm_ketToReal ψ₀)]
  simp only [List.length_map, ← ketToReal_idealUnitaryTrajectory, pureDensityMatrix_ketToReal,
    depolarizingChannel_apply_m, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    uniform_m_apply, ← pow_mul, mul_comm us.length 2]
  apply Complex.ext <;> (by_cases hxy : x = y <;> simp [hxy, -Complex.ofReal_pow])

/-- **Single-step depolarizing channel emergence:** Averaging the rank-1 density matrix
    `pureDensityMatrix` over one isotropic sphere error step on `ketToReal ψ` yields
    `(depolarizingChannel n σ hσ (MState.pure ψ)).m` entrywise. -/
theorem isotropicOneStep_eq_depolarizingChannel {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (ψ : Ket (Fin (2 ^ n))) (x y : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, pureDensityMatrix n (isotropicError (ketToReal ψ) e₂ θ) x y
          ∂(perpSphereMeasure (ketToReal ψ)) ∂(poissonAngleMeasure (d n) σ) =
    (depolarizingChannel n σ hσ (MState.pure ψ)).m x y := by
  simpa [idealUnitaryTrajectory] using
    noisyTrajectory_eq_depolarizingChannel σ hσ [1] ψ x y

/-! ## Channel algebra and syntactic `Circuit.size` theorems -/

theorem ofUnitary_one (n : ℕ) :
    CPTPMap.ofUnitary (1 : 𝐔[Fin (2 ^ n)]) = CPTPMap.id := by
  apply CPTPMap.funext
  intro ρ
  apply MState.ext_m
  rw [ofUnitary_apply_m, CPTPMap.id_MState]
  change (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) * ρ.m *
    (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)ᴴ = ρ.m
  simp

theorem ofUnitary_mul {n : ℕ} (U₂ U₁ : 𝐔[Fin (2 ^ n)]) :
    CPTPMap.ofUnitary (U₂ * U₁) = CPTPMap.ofUnitary U₂ ∘ₘ CPTPMap.ofUnitary U₁ := by
  apply CPTPMap.funext
  intro ρ
  apply MState.ext_m
  rw [CPTPMap.compose_eq, ofUnitary_apply_m, ofUnitary_apply_m, ofUnitary_apply_m]
  change (U₂.val * U₁.val) * ρ.m * (U₂.val * U₁.val)ᴴ =
    U₂.val * (U₁.val * ρ.m * U₁.valᴴ) * U₂.valᴴ
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma ofUnitary_uniform {n : ℕ} (U : 𝐔[Fin (2 ^ n)]) :
    CPTPMap.ofUnitary U (MState.uniform (d := Fin (2 ^ n))) = MState.uniform := by
  apply MState.ext_m
  have hu : U.val * U.valᴴ = 1 := U.2.2
  rw [ofUnitary_apply_m, uniform_m_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hu]

/-- The depolarizing channel commutes with every unitary channel `CPTPMap.ofUnitary U`. -/
theorem depolarizingChannel_comm_ofUnitary (n : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (U : 𝐔[Fin (2 ^ n)]) :
    depolarizingChannel n σ hσ ∘ₘ CPTPMap.ofUnitary U =
    CPTPMap.ofUnitary U ∘ₘ depolarizingChannel n σ hσ := by
  apply CPTPMap.funext
  intro ρ
  apply MState.ext_m
  have hunif : U.val * (MState.uniform (d := Fin (2 ^ n))).m * U.valᴴ =
      (MState.uniform (d := Fin (2 ^ n))).m := by
    rw [← ofUnitary_apply_m, ofUnitary_uniform]
  rw [CPTPMap.compose_eq, CPTPMap.compose_eq, depolarizingChannel_apply_m, ofUnitary_apply_m,
      ofUnitary_apply_m, depolarizingChannel_apply_m, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hunif]

/-- Sequential composition of depolarizing channels multiplies their fidelity parameters:
    `D(σ₁) ∘ₘ D(σ₂) = D(σ₁ * σ₂)`. -/
theorem depolarizingChannel_compose (n : ℕ) (σ₁ : ℝ) (hσ₁ : σ₁ ∈ Set.Icc 0 1)
    (σ₂ : ℝ) (hσ₂ : σ₂ ∈ Set.Icc 0 1) :
    depolarizingChannel n σ₁ hσ₁ ∘ₘ depolarizingChannel n σ₂ hσ₂ =
    depolarizingChannel n (σ₁ * σ₂) (mul_mem_Icc_zero_one hσ₁ hσ₂) := by
  apply CPTPMap.funext
  intro ρ
  apply MState.ext_m
  ext x y
  simp only [CPTPMap.compose_eq, depolarizingChannel_apply_m, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  push_cast
  ring

/-- Left-to-right list of whole-system primitive gate unitaries executed by a syntactic
    circuit `c : Circuit n`. -/
noncomputable def circuitUnitaries {n : ℕ} : Circuit n → List 𝐔[Fin (2 ^ n)]
  | .identity => []
  | .gate g r => [r.embedUnitary g.eval]
  | .seq c₁ c₂ => circuitUnitaries c₁ ++ circuitUnitaries c₂

@[simp]
lemma circuitUnitaries_identity {n : ℕ} :
    circuitUnitaries (.identity : Circuit n) = [] := rfl

@[simp]
lemma circuitUnitaries_gate {n k : ℕ} (g : PrimitiveGate k) (r : QRegister k n) :
    circuitUnitaries (.gate g r : Circuit n) = [r.embedUnitary g.eval] := rfl

@[simp]
lemma circuitUnitaries_seq {n : ℕ} (c₁ c₂ : Circuit n) :
    circuitUnitaries (.seq c₁ c₂) = circuitUnitaries c₁ ++ circuitUnitaries c₂ := rfl

@[simp]
lemma length_circuitUnitaries {n : ℕ} (c : Circuit n) :
    (circuitUnitaries c).length = c.size := by
  induction c with
  | identity => rfl
  | gate _ _ => rfl
  | seq _ _ ih₁ ih₂ => simp [ih₁, ih₂]

@[simp]
theorem idealUnitaryTrajectory_circuitUnitaries {n : ℕ} (c : Circuit n)
    (ψ₀ : Ket (Fin (2 ^ n))) :
    idealUnitaryTrajectory (circuitUnitaries c) ψ₀ = applyUnitaryKet c.eval ψ₀ := by
  induction c generalizing ψ₀ with
  | identity => simp
  | gate _ _ => rfl
  | seq c₁ c₂ ih₁ ih₂ =>
    simp [ih₁, ih₂]

/-- Noisy quantum channel associated with a syntactic circuit `c : Circuit n`, applying
    `depolarizingChannel n σ hσ` after every primitive gate `.gate g r` while `.identity` is
    noiseless. -/
noncomputable def noisyCircuitChannel {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) :
    Circuit n → CPTPMap (Fin (2 ^ n)) (Fin (2 ^ n))
  | .identity => CPTPMap.id
  | .gate g r => depolarizingChannel n σ hσ ∘ₘ CPTPMap.ofUnitary (r.embedUnitary g.eval)
  | .seq c₁ c₂ => noisyCircuitChannel σ hσ c₂ ∘ₘ noisyCircuitChannel σ hσ c₁

@[simp]
lemma noisyCircuitChannel_identity {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) :
    noisyCircuitChannel (n := n) σ hσ .identity = CPTPMap.id := rfl

@[simp]
lemma noisyCircuitChannel_gate {n k : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (g : PrimitiveGate k) (r : QRegister k n) :
    noisyCircuitChannel σ hσ (.gate g r) =
    depolarizingChannel n σ hσ ∘ₘ CPTPMap.ofUnitary (r.embedUnitary g.eval) := rfl

@[simp]
lemma noisyCircuitChannel_seq {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (c₁ c₂ : Circuit n) :
    noisyCircuitChannel σ hσ (.seq c₁ c₂) =
    noisyCircuitChannel σ hσ c₂ ∘ₘ noisyCircuitChannel σ hσ c₁ := rfl

/-- **Syntactic `Circuit.size` channel theorem:** For any circuit `c : Circuit n`, executing `c`
    with per-gate depolarizing parameter `σ ∈ [0, 1]` equals ideal unitary evolution `c.eval`
    followed by a single depolarizing channel with parameter `σ ^ c.size`. -/
theorem noisyCircuitChannel_eq {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (c : Circuit n) :
    noisyCircuitChannel σ hσ c =
    depolarizingChannel n (σ ^ c.size) (pow_mem_Icc_zero_one hσ c.size) ∘ₘ
      CPTPMap.ofUnitary c.eval := by
  induction c with
  | identity => simp [ofUnitary_one]
  | gate g r => simp
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [noisyCircuitChannel_seq, ih₁, ih₂, Circuit.size_seq, Circuit.eval_seq]
    rw [CPTPMap.compose_assoc,
        ← CPTPMap.compose_assoc (CPTPMap.ofUnitary c₂.eval),
        ← depolarizingChannel_comm_ofUnitary,
        CPTPMap.compose_assoc (depolarizingChannel n (σ ^ c₁.size) _),
        ← CPTPMap.compose_assoc (depolarizingChannel n (σ ^ c₂.size) _),
        depolarizingChannel_compose,
        ← ofUnitary_mul]
    congr 2
    rw [← pow_add, add_comm]

/-- **End-to-end density-matrix bridge for syntactic circuits:** Averaging `pureDensityMatrix`
    along the microscopic pure-state Markov trajectory of `circuitUnitaries c` yields the exact
    output density matrix of `noisyCircuitChannel σ hσ c (MState.pure ψ₀)` entrywise. -/
theorem noisyCircuit_trajectory_eq_channel {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (c : Circuit n) (ψ₀ : Ket (Fin (2 ^ n))) (x y : Fin (2 ^ n)) :
    noisyTrajectoryExpectationℂ n σ ((circuitUnitaries c).map unitaryToRealIso) (ketToReal ψ₀)
      (fun Ψ => pureDensityMatrix n Ψ x y) =
    (noisyCircuitChannel σ hσ c (MState.pure ψ₀)).m x y := by
  rw [noisyTrajectory_eq_depolarizingChannel σ hσ, length_circuitUnitaries,
      idealUnitaryTrajectory_circuitUnitaries, ← ofUnitary_pure,
      ← CPTPMap.compose_eq, ← noisyCircuitChannel_eq]

/-- **End-to-end measurement-probability bridge for syntactic circuits:** Expected `succProb`
    along the microscopic pure-state Markov trajectory of `circuitUnitaries c` coincides with
    the `computationalPOVM` Born-rule probability of
    `noisyCircuitChannel σ hσ c (MState.pure ψ₀)`. -/
theorem noisyCircuit_trajectory_succProb_eq_measure {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (c : Circuit n) (ψ₀ : Ket (Fin (2 ^ n))) (w : Fin (2 ^ n)) :
    noisyTrajectoryExpectation n σ ((circuitUnitaries c).map unitaryToRealIso) (ketToReal ψ₀)
      (fun Ψ => succProb n Ψ w) =
    ((computationalPOVM n).measure (noisyCircuitChannel σ hσ c (MState.pure ψ₀)) w : ℝ) := by
  have hdiag : (fun Ψ : E n => succProb n Ψ w) =
      (fun Ψ => (pureDensityMatrix n Ψ w w).re) := by
    ext Ψ
    rw [pureDensityMatrix_re_eq]
    simp [succProb, sq]
  rw [hdiag, ← noisyTrajectoryExpectationℂ_re σ hσ _ _ (norm_ketToReal ψ₀)
        (continuous_pureDensityMatrix_apply w w),
      noisyCircuit_trajectory_eq_channel σ hσ c ψ₀ w w,
      computationalPOVM_measure_eq_exp_val, exp_val_compProjObs_eq_re_diag]

/-- **Born-rule probability under noisy circuit execution:** Measuring outcome `w : Fin (2 ^ n)`
    with `computationalPOVM n` after running `noisyCircuitChannel σ hσ c` on any mixed state
    `ρ₀ : MState (Fin (2 ^ n))` yields
    `σ ^ (2 * c.size) * (CPTPMap.ofUnitary c.eval ρ₀).exp_val (compProjObs w).1 +
      (1 - σ ^ (2 * c.size)) / 2^n`, where the gate count `c.size` is computed directly from
    the circuit syntax. -/
theorem noisyCircuit_bornProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (c : Circuit n)
    (ρ₀ : MState (Fin (2 ^ n))) (w : Fin (2 ^ n)) :
    ((computationalPOVM n).measure (noisyCircuitChannel σ hσ c ρ₀) w : ℝ) =
    σ ^ (2 * c.size) * (CPTPMap.ofUnitary c.eval ρ₀).exp_val (compProjObs w).1 +
      (1 - σ ^ (2 * c.size)) / (2 ^ n : ℝ) := by
  rw [noisyCircuitChannel_eq, CPTPMap.compose_eq, computationalPOVM_measure_eq_exp_val,
      exp_val_compProjObs_eq_re_diag, exp_val_compProjObs_eq_re_diag,
      depolarizingChannel_apply_m, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      uniform_m_apply, ite_eq_left rfl]
  simp only [smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, ← pow_mul, mul_comm c.size 2]
  ring

/-- Pure-state specialization of `noisyCircuit_bornProb`: for an initial ket `ψ₀`, the ideal
    expectation simplifies directly to the squared evolved amplitude `‖(c.evolve ψ₀.vec) w‖ ^ 2`. -/
theorem noisyCircuit_bornProb_pure {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) (c : Circuit n)
    (ψ₀ : Ket (Fin (2 ^ n))) (w : Fin (2 ^ n)) :
    ((computationalPOVM n).measure (noisyCircuitChannel σ hσ c (MState.pure ψ₀)) w : ℝ) =
    σ ^ (2 * c.size) * ‖(c.evolve ψ₀.vec) w‖ ^ 2 +
      (1 - σ ^ (2 * c.size)) / (2 ^ n : ℝ) := by
  have hideal :
      (CPTPMap.ofUnitary c.eval (MState.pure ψ₀)).exp_val (compProjObs w).1 =
      ‖(c.evolve ψ₀.vec) w‖ ^ 2 := by
    have hborn := succProb_ketToReal_eq_born (applyUnitaryKet c.eval ψ₀) w
    rw [ofUnitary_pure, ← hborn.2.2.1, hborn.1]
    rfl
  rw [noisyCircuit_bornProb, hideal]

/-! ## Verification checks -/

#check @vecToReal
#check @realToVec
#check @sum_norm_sq_realToVec
#check @ketToReal
#check @realToKet
#check @unitaryToRealIso
#check @computationalPOVM
#check @succProb_ketToReal_eq_born
#check @pureDensityMatrix
#check @pureDensityMatrix_ketToReal
#check @depolarizingChannel
#check @isotropicOneStep_eq_depolarizingChannel
#check @noisyTrajectory_eq_depolarizingChannel
#check @depolarizingChannel_comm_ofUnitary
#check @depolarizingChannel_compose
#check @ofUnitary_mul
#check @circuitUnitaries
#check @noisyCircuitChannel
#check @noisyCircuitChannel_eq
#check @noisyCircuit_trajectory_eq_channel
#check @noisyCircuit_trajectory_succProb_eq_measure
#check @noisyCircuit_bornProb
#check @noisyCircuit_bornProb_pure

/--
info: 'IsotropicGrover.succProb_ketToReal_eq_born' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms succProb_ketToReal_eq_born

/--
info: 'IsotropicGrover.isotropicOneStep_eq_depolarizingChannel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isotropicOneStep_eq_depolarizingChannel

/--
info: 'IsotropicGrover.noisyTrajectory_eq_depolarizingChannel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyTrajectory_eq_depolarizingChannel

/--
info: 'IsotropicGrover.noisyCircuitChannel_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyCircuitChannel_eq

/--
info: 'IsotropicGrover.noisyCircuit_trajectory_eq_channel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyCircuit_trajectory_eq_channel

/--
info: 'IsotropicGrover.noisyCircuit_trajectory_succProb_eq_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyCircuit_trajectory_succProb_eq_measure

/--
info: 'IsotropicGrover.noisyCircuit_bornProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyCircuit_bornProb

/--
info: 'IsotropicGrover.noisyCircuit_bornProb_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyCircuit_bornProb_pure

end IsotropicGrover
