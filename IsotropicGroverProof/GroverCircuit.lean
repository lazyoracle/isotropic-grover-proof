-- IsotropicGroverProof/GroverCircuit.lean
-- M9: Grover circuit state vectors, specialization of isotropicGrover_main,
--     and bridge to QuantumComputation.Algorithms.Grover.
--
-- Formalizes:
-- 1. The target basis state |w⟩, its ketToReal equivalence, and its success probability (1).
-- 2. The non-target orthogonal superposition |w^⟂⟩ and its orthogonality to |w⟩.
-- 3. The uniform superposition state |s⟩, its ketToReal equivalence, ‖|s⟩‖ = 1, succProb = 1/2^n,
--    and invariance under isotropic noise.
-- 4. The 2D Grover search plane spanned by |w⟩ and |w^⟂⟩, parameterized by angle α
--    or ideal success probability p_ideal ∈ [0, 1].
-- 5. Canonical Grover unitary sequences (`groverIterGates`, `groverFullGates`) and their
--    noiseless evolution to `Grover.groverState` and Born-rule probability `Grover.p_succ`.

import QuantumInfo.States.Pure.Braket
import QuantumInfo.States.Mixed.MState
import QuantumInfo.Channels.CPTP
import QuantumInfo.Measurements.POVM
import QuantumComputation.Algorithms.Grover.Operators
import QuantumComputation.Algorithms.Grover.Amplitude
import QuantumComputation.Circuits.ResourceCounting
import IsotropicGroverProof.MainTheorem
import IsotropicGroverProof.QuantumChannel

/-!
# Grover Circuit State Specializations and `QuantumComputation.Algorithms.Grover` Bridge

Specializes `isotropicGrover_main` to the target basis state, uniform superposition,
and 2D Grover search plane, and bridges `QuantumInfo` ket trajectories across
`Grover.oracleUnitary`, `Grover.diffuserUnitary`, and `hadamardUnitary` to
`Grover.groverState` and `Grover.p_succ`.
-/

namespace IsotropicGrover

open Real MeasureTheory
open scoped Matrix

/-! ## Shared real/complex vector and orthonormal linear-combination helpers -/

private lemma realToVec_stdBasisVec_idx0 (n : ℕ) (w x : Fin (2 ^ n)) :
    realToVec (stdBasisVec n (succProbIdx0 n w)) x = if w = x then 1 else 0 := by
  have hiff : succProbIdx0 n x = succProbIdx0 n w ↔ w = x :=
    ⟨fun h => (succProbIdx0_inj h).symm, fun h => congrArg _ h.symm⟩
  have hne : ∀ a b, succProbIdx1 n a ≠ succProbIdx0 n b :=
    fun a b h => succProbIdx0_ne_succProbIdx1 b a h.symm
  by_cases hwx : w = x <;> apply Complex.ext <;>
    simp [stdBasisVec_apply, hiff, hne, hwx]

private lemma realToVec_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → E n) (x : Fin (2 ^ n)) :
    realToVec (∑ i ∈ s, f i) x = ∑ i ∈ s, realToVec (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply Complex.ext <;> simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, realToVec_add, Pi.add_apply, ih, Finset.sum_insert ha]

/-- Norm of a linear combination `a • u + b • v` of orthonormal vectors `u, v : E n`
    when `a ^ 2 + b ^ 2 = 1`. -/
lemma norm_smul_add_smul_of_ortho {n : ℕ} {u v : E n} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℝ) u v = 0) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    ‖a • u + b • v‖ = 1 := by
  have hsq : ‖a • u + b • v‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
        hu, hv, huv, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one,
        sq_abs, sq_abs]
    linarith
  nlinarith [norm_nonneg (a • u + b • v)]

/-! ## Target basis state -/

/-- The target basis state vector |w⟩ in ℝ^d with amplitude 1 at real index 2w
    and 0 on all other indices. -/
noncomputable def targetBasisState (n : ℕ) (w : Fin (2 ^ n)) : E n :=
  stdBasisVec n (succProbIdx0 n w)

/-- `targetBasisState n w` is the real embedding `ketToReal (Ket.basis w)`. -/
lemma targetBasisState_eq_ketToReal (n : ℕ) (w : Fin (2 ^ n)) :
    targetBasisState n w = ketToReal (Ket.basis w) := by
  rw [← vecToReal_realToVec (targetBasisState n w), ketToReal]
  congr 1
  ext x
  rw [targetBasisState, realToVec_stdBasisVec_idx0]
  simp [Ket.basis]

/-- The target basis state is a unit vector: ‖|w⟩‖ = 1. -/
lemma norm_targetBasisState (n : ℕ) (w : Fin (2 ^ n)) :
    ‖targetBasisState n w‖ = 1 := by
  rw [targetBasisState_eq_ketToReal]
  exact norm_ketToReal (Ket.basis w)

/-- Inner product of |w⟩ with real component 2w is 1. -/
lemma inner_targetBasisState_idx0 (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetBasisState n w) (stdBasisVec n (succProbIdx0 n w)) = 1 := by
  unfold targetBasisState
  rw [inner_stdBasisVec]
  simp

/-- Inner product of |w⟩ with imaginary component 2w+1 is 0. -/
lemma inner_targetBasisState_idx1 (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetBasisState n w) (stdBasisVec n (succProbIdx1 n w)) = 0 := by
  unfold targetBasisState
  rw [inner_stdBasisVec]
  simp [succProbIdx0_ne_succProbIdx1]

/-- The ideal success probability of measuring outcome w on |w⟩ is 1. -/
lemma succProb_targetBasisState (n : ℕ) (w : Fin (2 ^ n)) :
    succProb n (targetBasisState n w) w = 1 := by
  rw [targetBasisState_eq_ketToReal, (succProb_ketToReal_eq_born (Ket.basis w) w).1]
  simp [Ket.apply, Ket.basis]

/-! ## Orthogonal non-target state -/

/-- The normalized uniform superposition over all non-target states:
    |w^⟂⟩ = (1 / √(2^n - 1)) ∑_{x ≠ w} |x⟩. -/
noncomputable def targetPerpState (n : ℕ) (w : Fin (2 ^ n)) : E n :=
  (1 / Real.sqrt ((2 ^ n : ℝ) - 1)) •
    ∑ x : Fin (2 ^ n), (if x = w then (0 : ℝ) else 1) • stdBasisVec n (succProbIdx0 n x)

private lemma realToVec_targetPerpState (n : ℕ) (w y : Fin (2 ^ n)) :
    realToVec (targetPerpState n w) y =
    if y = w then 0 else ((1 / Real.sqrt ((2 ^ n : ℝ) - 1) : ℝ) : ℂ) := by
  unfold targetPerpState
  rw [realToVec_smul, Pi.smul_apply, realToVec_sum]
  simp_rw [realToVec_smul, Pi.smul_apply, realToVec_stdBasisVec_idx0, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hy : y = w <;> simp [hy]

lemma inner_targetPerpState_idx0 (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetPerpState n w) (stdBasisVec n (succProbIdx0 n w)) = 0 := by
  rw [inner_stdBasisVec_eq_apply, ← realToVec_re, realToVec_targetPerpState]
  simp

lemma inner_targetPerpState_idx1 (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetPerpState n w) (stdBasisVec n (succProbIdx1 n w)) = 0 := by
  rw [inner_stdBasisVec_eq_apply, ← realToVec_im, realToVec_targetPerpState]
  simp

/-- The target state |w⟩ and the non-target state |w^⟂⟩ are orthogonal. -/
lemma inner_targetBasisState_targetPerpState (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetBasisState n w) (targetPerpState n w) = 0 := by
  rw [real_inner_comm]
  exact inner_targetPerpState_idx0 n w

/-- Success probability of measuring outcome w on |w^⟂⟩ is 0. -/
lemma succProb_targetPerpState (n : ℕ) (w : Fin (2 ^ n)) :
    succProb n (targetPerpState n w) w = 0 := by
  simp [succProb, inner_targetPerpState_idx0, inner_targetPerpState_idx1]

/-- The non-target state |w^⟂⟩ is a unit vector when 1 < 2^n (i.e., n ≥ 1). -/
lemma norm_targetPerpState (n : ℕ) (w : Fin (2 ^ n)) (hn : 1 < 2 ^ n) :
    ‖targetPerpState n w‖ = 1 := by
  have h1 : (1 : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hn
  have hsq : ‖targetPerpState n w‖ ^ 2 = 1 := by
    rw [← sum_norm_sq_realToVec]
    simp_rw [realToVec_targetPerpState]
    have hterm : ∀ y : Fin (2 ^ n),
        ‖if y = w then (0 : ℂ) else ((1 / Real.sqrt ((2 ^ n : ℝ) - 1) : ℝ) : ℂ)‖ ^ 2 =
        if y = w then 0 else 1 / ((2 ^ n : ℝ) - 1) := by
      intro y
      by_cases hy : y = w
      · simp [hy]
      · simp only [hy, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div_pow,
          Real.sq_sqrt (by linarith : 0 ≤ (2 ^ n : ℝ) - 1)]
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun y : Fin (2 ^ n) => ¬y = w)).card = 2 ^ n - 1 := by
      rw [show Finset.univ.filter (fun y : Fin (2 ^ n) => ¬y = w) = Finset.univ \ {w} by ext; simp,
          Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr (Finset.mem_univ w))]
      simp
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ 2 ^ n)]
    push_cast
    exact mul_one_div_cancel (by linarith)
  nlinarith [norm_nonneg (targetPerpState n w)]

/-! ## Uniform superposition state -/

/-- The uniform superposition state vector |s⟩ = (1 / √(2^n)) ∑_x |x⟩ in ℝ^d,
    with amplitude 1 / √(2^n) on each even index 2x and 0 on 2x+1. -/
noncomputable def uniformSuperposition (n : ℕ) : E n :=
  (1 / Real.sqrt (2 ^ n)) • ∑ x : Fin (2 ^ n), stdBasisVec n (succProbIdx0 n x)

lemma uniform_superposition_vec {n : ℕ} (x : Fin (2 ^ n)) :
    (uniform_superposition : Ket (Fin (2 ^ n))).vec x = ((1 / Real.sqrt (2 ^ n) : ℝ) : ℂ) := by
  simp [uniform_superposition, Ket.normalize]

/-- `uniformSuperposition n` is the real embedding `ketToReal uniform_superposition`. -/
lemma uniformSuperposition_eq_ketToReal (n : ℕ) :
    uniformSuperposition n = ketToReal (uniform_superposition : Ket (Fin (2 ^ n))) := by
  rw [← vecToReal_realToVec (uniformSuperposition n), ketToReal]
  congr 1
  ext y
  rw [uniformSuperposition, realToVec_smul, Pi.smul_apply, realToVec_sum, uniform_superposition_vec]
  simp_rw [realToVec_stdBasisVec_idx0]
  simp

/-- The success probability of measuring any outcome w on the uniform superposition is 1 / 2^n. -/
lemma succProb_uniformSuperposition (n : ℕ) (w : Fin (2 ^ n)) :
    succProb n (uniformSuperposition n) w = 1 / (2 ^ n : ℝ) := by
  rw [uniformSuperposition_eq_ketToReal,
      (succProb_ketToReal_eq_born (uniform_superposition : Ket (Fin (2 ^ n))) w).1,
      Ket.apply, uniform_superposition_vec, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      one_div_pow, Real.sq_sqrt (by positivity)]

/-- The uniform superposition state is a unit vector: ‖|s⟩‖ = 1. -/
lemma norm_uniformSuperposition (n : ℕ) :
    ‖uniformSuperposition n‖ = 1 := by
  rw [uniformSuperposition_eq_ketToReal]
  exact norm_ketToReal (uniform_superposition : Ket (Fin (2 ^ n)))

/-- For the uniform superposition |s⟩ (prior to Grover iterations), the expected success
    probability under isotropic noise is identically 1 / 2^n for ANY gate count G and parameter σ.
    This establishes the baseline: without Grover rotations, isotropic noise leaves the success
    probability unchanged at the random guessing floor. -/
theorem isotropicGrover_uniformSuperposition (n : ℕ) (G : ℕ) (hG : 0 < G)
    (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (w : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, succProb n (isotropicError (uniformSuperposition n) e₂ θ) w
          ∂(perpSphereMeasure (uniformSuperposition n))
      ∂(composedMeasure (d n) G σ) =
    1 / (2 ^ n : ℝ) := by
  rw [isotropicGrover_main G hG σ hσ (uniformSuperposition n) (norm_uniformSuperposition n) w,
      succProb_uniformSuperposition]
  ring

/-! ## Grover state in the 2D search plane -/

private lemma succProb_smul_target_add_perp (n : ℕ) (w : Fin (2 ^ n)) (a b : ℝ) :
    succProb n (a • targetBasisState n w + b • targetPerpState n w) w = a ^ 2 := by
  unfold succProb
  simp_rw [inner_add_left, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial,
    inner_targetBasisState_idx0, inner_targetBasisState_idx1,
    inner_targetPerpState_idx0, inner_targetPerpState_idx1]
  ring

/-- A general state in the 2D Grover search plane spanned by |w⟩ and |w^⟂⟩,
    parameterized by angle α: |ψ(α)⟩ = sin(α)|w⟩ + cos(α)|w^⟂⟩. -/
noncomputable def groverState2D (n : ℕ) (w : Fin (2 ^ n)) (α : ℝ) : E n :=
  Real.sin α • targetBasisState n w + Real.cos α • targetPerpState n w

/-- Any Grover state |ψ(α)⟩ in the 2D search plane is a unit vector when 1 < 2^n. -/
lemma norm_groverState2D (n : ℕ) (w : Fin (2 ^ n)) (α : ℝ) (hn : 1 < 2 ^ n) :
    ‖groverState2D n w α‖ = 1 :=
  norm_smul_add_smul_of_ortho (norm_targetBasisState n w) (norm_targetPerpState n w hn)
    (inner_targetBasisState_targetPerpState n w) (Real.sin_sq_add_cos_sq α)

/-- The ideal success probability of measuring outcome w on |ψ(α)⟩ is sin²(α). -/
lemma succProb_groverState2D (n : ℕ) (w : Fin (2 ^ n)) (α : ℝ) :
    succProb n (groverState2D n w α) w = Real.sin α ^ 2 :=
  succProb_smul_target_add_perp n w (Real.sin α) (Real.cos α)

/-- The expected success probability of any state in the 2D Grover search plane under
    isotropic noise is σ^(2G) * sin²(α) + (1 - σ^(2G)) / 2^n. -/
theorem isotropicGrover_groverState2D (n : ℕ) (G : ℕ) (hG : 0 < G) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (w : Fin (2 ^ n)) (α : ℝ) (hn : 1 < 2 ^ n) :
    ∫ θ, ∫ e₂, succProb n (isotropicError (groverState2D n w α) e₂ θ) w
          ∂(perpSphereMeasure (groverState2D n w α))
      ∂(composedMeasure (d n) G σ) =
    σ ^ (2 * G) * Real.sin α ^ 2 + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) := by
  rw [isotropicGrover_main G hG σ hσ (groverState2D n w α) (norm_groverState2D n w α hn) w,
      succProb_groverState2D]

/-! ## Grover state parameterized directly by ideal success probability p_ideal -/

/-- A Grover state in the 2D search plane with specified ideal success probability p_ideal ∈ [0, 1]:
    |ψ(p_ideal)⟩ = √p_ideal |w⟩ + √(1 - p_ideal) |w^⟂⟩. -/
noncomputable def groverState2D_prob (n : ℕ) (w : Fin (2 ^ n)) (p_ideal : ℝ) : E n :=
  Real.sqrt p_ideal • targetBasisState n w + Real.sqrt (1 - p_ideal) • targetPerpState n w

/-- The state |ψ(p_ideal)⟩ is a unit vector for any p_ideal ∈ [0, 1] when 1 < 2^n. -/
lemma norm_groverState2D_prob (n : ℕ) (w : Fin (2 ^ n)) (p_ideal : ℝ)
    (hp : p_ideal ∈ Set.Icc (0 : ℝ) 1) (hn : 1 < 2 ^ n) :
    ‖groverState2D_prob n w p_ideal‖ = 1 :=
  norm_smul_add_smul_of_ortho (norm_targetBasisState n w) (norm_targetPerpState n w hn)
    (inner_targetBasisState_targetPerpState n w) (by
      rw [Real.sq_sqrt hp.1, Real.sq_sqrt (sub_nonneg.mpr hp.2)]; ring)

/-- The ideal success probability of measuring outcome w on |ψ(p_ideal)⟩ is exactly p_ideal. -/
lemma succProb_groverState2D_prob (n : ℕ) (w : Fin (2 ^ n)) (p_ideal : ℝ) (hp : 0 ≤ p_ideal) :
    succProb n (groverState2D_prob n w p_ideal) w = p_ideal := by
  rw [groverState2D_prob, succProb_smul_target_add_perp, Real.sq_sqrt hp]

/-- The expected success probability of |ψ(p_ideal)⟩ under isotropic noise is exactly
    σ^(2G) * p_ideal + (1 - σ^(2G)) / 2^n. -/
theorem isotropicGrover_groverState2D_prob (n : ℕ) (G : ℕ) (hG : 0 < G)
    (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (w : Fin (2 ^ n)) (p_ideal : ℝ)
    (hp : p_ideal ∈ Set.Icc (0 : ℝ) 1) (hn : 1 < 2 ^ n) :
    ∫ θ, ∫ e₂, succProb n (isotropicError (groverState2D_prob n w p_ideal) e₂ θ) w
          ∂(perpSphereMeasure (groverState2D_prob n w p_ideal))
      ∂(composedMeasure (d n) G σ) =
    σ ^ (2 * G) * p_ideal + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) := by
  rw [isotropicGrover_main G hG σ hσ (groverState2D_prob n w p_ideal)
        (norm_groverState2D_prob n w p_ideal hp hn) w,
      succProb_groverState2D_prob n w p_ideal hp.1]

/-! ## Ideal Grover output state -/

/-- For the ideal Grover output state (where p_ideal = 1, e.g. at the target state |w⟩),
    the expected success probability under isotropic noise simplifies to
    σ^(2G) + (1 - σ^(2G)) / 2^n. -/
theorem isotropicGrover_targetBasisState (n : ℕ) (G : ℕ) (hG : 0 < G)
    (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (w : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, succProb n (isotropicError (targetBasisState n w) e₂ θ) w
          ∂(perpSphereMeasure (targetBasisState n w))
      ∂(composedMeasure (d n) G σ) =
    σ ^ (2 * G) + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) := by
  rw [isotropicGrover_main G hG σ hσ (targetBasisState n w) (norm_targetBasisState n w) w,
      succProb_targetBasisState]
  ring

/-! ## Canonical Grover unitary sequences and noiseless state-evolution bridge -/

/-- Left-to-right list of `2 * K` macro unitaries for `K` Grover iterations: each iteration
    applies the phase oracle `Grover.oracleUnitary target` followed by `Grover.diffuserUnitary`. -/
noncomputable def groverIterGates {n : ℕ} (target : Fin (2 ^ n)) : ℕ → List 𝐔[Fin (2 ^ n)]
  | 0 => []
  | k + 1 => groverIterGates target k ++ [Grover.oracleUnitary target, Grover.diffuserUnitary]

@[simp]
lemma groverIterGates_zero {n : ℕ} (target : Fin (2 ^ n)) :
    groverIterGates target 0 = [] := rfl

@[simp]
lemma groverIterGates_succ {n : ℕ} (target : Fin (2 ^ n)) (k : ℕ) :
    groverIterGates target (k + 1) =
    groverIterGates target k ++ [Grover.oracleUnitary target, Grover.diffuserUnitary] := rfl

/-- Left-to-right list of `2 * K + 1` macro unitaries for Hadamard preparation followed by
    `K` Grover iterations. -/
noncomputable def groverFullGates (n : ℕ) (target : Fin (2 ^ n)) (K : ℕ) : List 𝐔[Fin (2 ^ n)] :=
  (hadamardUnitary : 𝐔[Fin (2 ^ n)]) :: groverIterGates target K

@[simp]
lemma length_groverIterGates {n : ℕ} (target : Fin (2 ^ n)) (K : ℕ) :
    (groverIterGates target K).length = 2 * K := by
  induction K with
  | zero => rfl
  | succ k ih =>
    simp [groverIterGates, ih]
    omega

@[simp]
lemma length_groverFullGates (n : ℕ) (target : Fin (2 ^ n)) (K : ℕ) :
    (groverFullGates n target K).length = 2 * K + 1 := by
  simp [groverFullGates]

/-- Applying `hadamardUnitary` to `Ket.basis 0` prepares `uniform_superposition`. -/
lemma applyUnitaryKet_hadamardUnitary_basis_zero (n : ℕ) :
    applyUnitaryKet (hadamardUnitary : 𝐔[Fin (2 ^ n)]) (Ket.basis (0 : Fin (2 ^ n))) =
    (uniform_superposition : Ket (Fin (2 ^ n))) := by
  ext i
  rw [Ket.apply, Ket.apply, uniform_superposition_vec]
  change (hadamardMatrix n *ᵥ (Ket.basis (0 : Fin (2 ^ n))).vec) i = _
  simp [Matrix.mulVec, dotProduct, Ket.basis]

/-- Evolving `uniform_superposition` along `groverIterGates target K` produces the exact
    amplitude vector `Grover.groverState target K` from `QuantumComputation.Algorithms.Grover`. -/
theorem idealUnitaryTrajectory_groverIterGates {n : ℕ} (target : Fin (2 ^ n)) (K : ℕ) :
    (idealUnitaryTrajectory (groverIterGates target K)
      (uniform_superposition : Ket (Fin (2 ^ n)))).vec =
    Grover.groverState target K := by
  induction K with
  | zero =>
    ext x
    simp [uniform_superposition_vec, Grover.groverState]
  | succ k ih =>
    simp only [groverIterGates_succ, idealUnitaryTrajectory_append, idealUnitaryTrajectory_cons,
      idealUnitaryTrajectory_nil]
    change Grover.diffuserMatrix *ᵥ (Grover.oracleMatrix target *ᵥ
      (idealUnitaryTrajectory (groverIterGates target k)
        (uniform_superposition : Ket (Fin (2 ^ n)))).vec) =
      Grover.groverState target (k + 1)
    rw [ih, Grover.groverState]

/-- Evolving `Ket.basis 0` along `groverFullGates n target K` (Hadamard preparation followed by
    `K` Grover iterations) produces `Grover.groverState target K`. -/
theorem idealUnitaryTrajectory_groverFullGates (n : ℕ) (target : Fin (2 ^ n)) (K : ℕ) :
    (idealUnitaryTrajectory (groverFullGates n target K) (Ket.basis (0 : Fin (2 ^ n)))).vec =
    Grover.groverState target K := by
  rw [groverFullGates, idealUnitaryTrajectory_cons, applyUnitaryKet_hadamardUnitary_basis_zero]
  exact idealUnitaryTrajectory_groverIterGates target K

/-- Any normalized ket `ψ` whose amplitude vector equals `Grover.groverState target K` has
    Born-rule measurement probability `‖ψ target‖ ^ 2 = Grover.p_succ K (2 ^ n)`. -/
theorem groverState_bornProb {n : ℕ} (target : Fin (2 ^ n)) (K : ℕ) {ψ : Ket (Fin (2 ^ n))}
    (hψ : ψ.vec = Grover.groverState target K) :
    ‖ψ target‖ ^ 2 = Grover.p_succ K (2 ^ n) := by
  rw [Ket.apply, hψ, (Grover.groverState_target_sum target K).1,
      Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Grover.p_succ_eq_sin_sq, Nat.cast_pow, Nat.cast_ofNat, ← Grover.halfAngle]

/-! ## Dependency smoke check & verification checks -/

/-- Smoke check that `Physlib`'s `QuantumInfo` (`Ket`, `MState.pure`, `MState.uniform`,
`CPTPMap.id`, `POVM.measureDiscard_apply`) and `formal-quantum-computation`'s
`QuantumComputation` (`Grover.diffuserUnitary`, `Grover.oracleUnitary`,
`Grover.grover_success_matrix_entry`, `Grover.p_succ_eq_sin_sq`, `Circuit.size`) are
available and carry zero `sorryAx` or custom axioms. -/
lemma quantumInfo_quantumComputation_smoke (n K : ℕ) (target : Fin (2 ^ n))
    (ψ : Ket (Fin 2)) (Λ : POVM (Fin 2) (Fin 2)) :
    (MState.pure ψ).M.trace = 1 ∧
    ((CPTPMap.id (dIn := Fin 2)) (MState.uniform (d := Fin 2))).M.trace = 1 ∧
    Λ.measureDiscard (MState.uniform (d := Fin 2)) =
      MState.ofClassical (Λ.measure (MState.uniform (d := Fin 2))) ∧
    Grover.diffuserUnitary (n := n) ≠ Grover.oracleUnitary target ∧
    ((Grover.groverMatrix target K)ᴴ * compProj target *
      Grover.groverMatrix target K) 0 0 = (Grover.p_succ K (2 ^ n) : ℂ) ∧
    Grover.p_succ K (2 ^ n) =
      Real.sin ((2 * (K : ℝ) + 1) * Real.arcsin (1 / √((2 ^ n : ℕ) : ℝ))) ^ 2 ∧
    (Circuit.identity : Circuit n).size = 0 :=
  ⟨(MState.pure ψ).tr,
   ((CPTPMap.id (dIn := Fin 2)) (MState.uniform (d := Fin 2))).tr,
   Λ.measureDiscard_apply (MState.uniform (d := Fin 2)),
   Grover.diffuserUnitary_ne_oracleUnitary target,
   Grover.grover_success_matrix_entry target K,
   Grover.p_succ_eq_sin_sq K (2 ^ n),
   rfl⟩

#check @targetBasisState_eq_ketToReal
#check @uniformSuperposition_eq_ketToReal
#check @groverIterGates
#check @groverFullGates
#check @length_groverIterGates
#check @length_groverFullGates
#check @idealUnitaryTrajectory_groverIterGates
#check @idealUnitaryTrajectory_groverFullGates
#check @groverState_bornProb

/-- info: 'IsotropicGrover.quantumInfo_quantumComputation_smoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quantumInfo_quantumComputation_smoke

/--
info: 'IsotropicGrover.isotropicGrover_groverState2D' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isotropicGrover_groverState2D

/--
info: 'IsotropicGrover.idealUnitaryTrajectory_groverIterGates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms idealUnitaryTrajectory_groverIterGates

/--
info: 'IsotropicGrover.idealUnitaryTrajectory_groverFullGates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms idealUnitaryTrajectory_groverFullGates

/--
info: 'IsotropicGrover.groverState_bornProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms groverState_bornProb

end IsotropicGrover
