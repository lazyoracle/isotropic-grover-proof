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
-- 6. End-to-end noisy Grover success-probability theorems across arbitrary unitary gate lists
--    (`List 𝐔[Fin (2 ^ n)]`), canonical Grover sequences, and syntactic `Circuit n` (`c.size`),
--    with concrete 1-qubit (`K = 0`) and 2-qubit (`K = 1`) primitive-gate circuit witnesses.

import QuantumComputation.Algorithms.Grover.Amplitude
import IsotropicGroverProof.MainTheorem
import IsotropicGroverProof.QuantumChannel

/-!
# Grover Circuit State Specializations and `QuantumComputation.Algorithms.Grover` Bridge

Specializes `isotropicGrover_main` to the target basis state, uniform superposition,
and 2D Grover search plane, bridges `QuantumInfo` ket trajectories across
`Grover.oracleUnitary`, `Grover.diffuserUnitary`, and `hadamardUnitary` to
`Grover.groverState` and `Grover.p_succ`, and proves end-to-end noisy Grover
success-probability theorems across arbitrary unitary gate lists (`List 𝐔[Fin (2 ^ n)]`),
canonical Grover sequences (`groverIterGates`, `groverFullGates`), and syntactic
`Circuit n` (`c.size`) for all `σ ∈ [0, 1]` and `K : ℕ`.
-/

namespace IsotropicGrover

open Real MeasureTheory
open scoped Matrix Circuit.Notation

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

/-! ## End-to-end noisy Grover theorems -/

/-- **Noisy Grover theorem for arbitrary unitary gate lists:** For any gate sequence
    `us : List 𝐔[Fin (2 ^ n)]` and initial ket `ψ₀` whose noiseless evolution achieves
    `‖(idealUnitaryTrajectory us ψ₀) target‖ ^ 2 = Grover.p_succ K (2 ^ n)`, the expected
    measurement probability along the interleaved isotropic sphere trajectory equals
    `σ ^ (2 * us.length) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * us.length)) / 2 ^ n`
    for all `σ ∈ [0, 1]`. -/
theorem noisyGrover_unitaryList_succProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (us : List 𝐔[Fin (2 ^ n)]) (ψ₀ : Ket (Fin (2 ^ n))) (target : Fin (2 ^ n)) (K : ℕ)
    (hideal : ‖(idealUnitaryTrajectory us ψ₀) target‖ ^ 2 = Grover.p_succ K (2 ^ n)) :
    noisyTrajectoryExpectation n σ (us.map unitaryToRealIso) (ketToReal ψ₀)
      (fun Ψ => succProb n Ψ target) =
    σ ^ (2 * us.length) * Grover.p_succ K (2 ^ n) +
      (1 - σ ^ (2 * us.length)) / (2 ^ n : ℝ) := by
  rw [noisyTrajectory_succProb σ hσ (us.map unitaryToRealIso) (ketToReal ψ₀) (norm_ketToReal ψ₀),
      List.length_map, ← ketToReal_idealUnitaryTrajectory,
      (succProb_ketToReal_eq_born (idealUnitaryTrajectory us ψ₀) target).1, hideal]

/-- **Noisy Grover theorem for `K` macro iterations (`G = 2 * K`):** Running
    `groverIterGates target K` from `uniform_superposition` under per-stage isotropic sphere noise
    with parameter `σ ∈ [0, 1]` yields expected success probability
    `σ ^ (4 * K) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (4 * K)) / 2 ^ n`. -/
theorem noisyGrover_iterGates_succProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (target : Fin (2 ^ n)) (K : ℕ) :
    noisyTrajectoryExpectation n σ ((groverIterGates target K).map unitaryToRealIso)
      (ketToReal (uniform_superposition : Ket (Fin (2 ^ n))))
      (fun Ψ => succProb n Ψ target) =
    σ ^ (4 * K) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (4 * K)) / (2 ^ n : ℝ) := by
  rw [noisyGrover_unitaryList_succProb σ hσ (groverIterGates target K)
        (uniform_superposition : Ket (Fin (2 ^ n))) target K
        (groverState_bornProb target K (idealUnitaryTrajectory_groverIterGates target K)),
      length_groverIterGates, show 2 * (2 * K) = 4 * K by omega]

/-- **Noisy Grover theorem with noisy Hadamard preparation (`G = 2 * K + 1`):** Running
    `groverFullGates n target K` from `Ket.basis 0` under per-stage isotropic sphere noise with
    parameter `σ ∈ [0, 1]` yields expected success probability
    `σ ^ (2 * (2 * K + 1)) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * (2 * K + 1))) / 2 ^ n`. -/
theorem noisyGrover_fullGates_succProb (n : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (target : Fin (2 ^ n)) (K : ℕ) :
    noisyTrajectoryExpectation n σ ((groverFullGates n target K).map unitaryToRealIso)
      (ketToReal (Ket.basis (0 : Fin (2 ^ n))))
      (fun Ψ => succProb n Ψ target) =
    σ ^ (2 * (2 * K + 1)) * Grover.p_succ K (2 ^ n) +
      (1 - σ ^ (2 * (2 * K + 1))) / (2 ^ n : ℝ) := by
  rw [noisyGrover_unitaryList_succProb σ hσ (groverFullGates n target K)
        (Ket.basis (0 : Fin (2 ^ n))) target K
        (groverState_bornProb target K (idealUnitaryTrajectory_groverFullGates n target K)),
      length_groverFullGates]

/-- **Noisy Grover Born-rule theorem for syntactic `Circuit n`:** For any primitive-gate circuit
    `c : Circuit n` and initial ket `ψ₀` whose noiseless evolution achieves
    `‖(c.evolve ψ₀.vec) target‖ ^ 2 = Grover.p_succ K (2 ^ n)`, measuring `target` with
    `computationalPOVM n` after executing `noisyCircuitChannel σ hσ c` yields
    `σ ^ (2 * c.size) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * c.size)) / 2 ^ n`,
    where `c.size` counts primitive gates directly from circuit syntax. -/
theorem noisyGrover_circuit_bornProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (c : Circuit n) (ψ₀ : Ket (Fin (2 ^ n))) (target : Fin (2 ^ n)) (K : ℕ)
    (hideal : ‖(c.evolve ψ₀.vec) target‖ ^ 2 = Grover.p_succ K (2 ^ n)) :
    ((computationalPOVM n).measure (noisyCircuitChannel σ hσ c (MState.pure ψ₀)) target : ℝ) =
    σ ^ (2 * c.size) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * c.size)) / (2 ^ n : ℝ) := by
  rw [noisyCircuit_bornProb_pure σ hσ c ψ₀ target, hideal]

/-- **Noisy Grover trajectory theorem for syntactic `Circuit n`:** Expected `succProb` along the
    microscopic pure-state isotropic sphere trajectory of `circuitUnitaries c` equals
    `σ ^ (2 * c.size) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * c.size)) / 2 ^ n`. -/
theorem noisyGrover_circuit_trajectory_succProb {n : ℕ} (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (c : Circuit n) (ψ₀ : Ket (Fin (2 ^ n))) (target : Fin (2 ^ n)) (K : ℕ)
    (hideal : ‖(c.evolve ψ₀.vec) target‖ ^ 2 = Grover.p_succ K (2 ^ n)) :
    noisyTrajectoryExpectation n σ ((circuitUnitaries c).map unitaryToRealIso) (ketToReal ψ₀)
      (fun Ψ => succProb n Ψ target) =
    σ ^ (2 * c.size) * Grover.p_succ K (2 ^ n) + (1 - σ ^ (2 * c.size)) / (2 ^ n : ℝ) := by
  rw [noisyCircuit_trajectory_succProb_eq_measure σ hσ c ψ₀ target,
      noisyGrover_circuit_bornProb σ hσ c ψ₀ target K hideal]

/-! ## Concrete syntactic `Circuit` witnesses -/

@[simp]
private lemma uzpow_neg_one (b : ZMod 2) :
    ((-1 : ℤˣ) ^ b : ℤˣ) = if b = 0 then 1 else -1 := by
  fin_cases b <;> decide

private lemma qubitH_eq_hadamardUnitary : Qubit.H = (hadamardUnitary : 𝐔[Fin (2 ^ 1)]) := by
  apply Subtype.ext
  ext i j
  simp only [hadamardUnitary_coe, hadamardMatrix_apply, walshMatrix_apply,
    walshChar_apply_apply, dotProduct, Fin.sum_univ_one]
  repeat rw [basisBits_eq_div_mod]
  fin_cases i <;> fin_cases j <;> simp [Qubit.H, Real.sqrt_inv]

private lemma circuit_H_eval {n : ℕ} (q : Wire n) :
    (Circuit.H q).eval = hadamardAt n q := by
  simp [Circuit.H, PrimitiveGate.eval, qubitH_eq_hadamardUnitary, hadamardAt]

private lemma circuit_Z_eval_val {n : ℕ} (q : Wire n) :
    (Circuit.Z q).eval.1 =
      Matrix.diagonal (fun i : Fin (2 ^ n) => if basisBits n i q = 0 then (1 : ℂ) else -1) := by
  have hZ : Qubit.Z.1 = Matrix.diagonal ![(1 : ℂ), -1] := by
    ext a b; fin_cases a <;> fin_cases b <;> rfl
  have hext : ∀ b : ZMod 2,
      ((basisBits 1).symm (fun _ => b) : Fin 2) = if b = 0 then 0 else 1 := by decide
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval, hZ,
      QRegister.embedMatrix_diagonal]
  congr 1; ext i
  simp only [QRegister.extractIndex, QRegister.singleton_apply, hext]
  split_ifs <;> rfl

/-- Evolving `Ket.basis 0` through the 1-qubit primitive Hadamard circuit `Circuit.H (0 : Wire 1)`
    yields `Grover.groverState target 0`. -/
lemma circuit_hadamard1_evolve_basis_zero (target : Fin (2 ^ 1)) :
    (Circuit.H (0 : Wire 1)).evolve (Ket.basis (0 : Fin (2 ^ 1))).vec =
    Grover.groverState target 0 := by
  rw [Circuit.evolve, circuit_H_eval]
  simpa [hadamardAt, groverFullGates, idealUnitaryTrajectory, applyUnitaryKet] using
    idealUnitaryTrajectory_groverFullGates 1 target 0

/-- The 1-qubit Hadamard circuit `Circuit.H (0 : Wire 1)` achieves ideal Born probability
    `Grover.p_succ 0 2` on every target `target : Fin (2 ^ 1)`. -/
lemma circuit_hadamard1_bornProb (target : Fin (2 ^ 1)) :
    ‖((Circuit.H (0 : Wire 1)).evolve (Ket.basis (0 : Fin (2 ^ 1))).vec) target‖ ^ 2 =
    Grover.p_succ 0 (2 ^ 1) :=
  groverState_bornProb target 0 (ψ := applyUnitaryKet (Circuit.H (0 : Wire 1)).eval (Ket.basis 0))
    (circuit_hadamard1_evolve_basis_zero target)

/-- At `K = 0` on `n = 1` qubit (`d = 2`), `Grover.p_succ 0 2 = 1 / 2`. -/
lemma p_succ_zero_two : Grover.p_succ 0 2 = 1 / 2 := by
  have h := groverState_bornProb (0 : Fin (2 ^ 1)) 0
    (idealUnitaryTrajectory_groverFullGates 1 (0 : Fin (2 ^ 1)) 0)
  rw [Ket.apply, idealUnitaryTrajectory_groverFullGates] at h
  simpa [Grover.groverState, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    one_div_pow] using h.symm

/-- **Concrete `Circuit 1` witness (`K = 0`, `c.size = 1`):** Instantiates
    `noisyGrover_circuit_bornProb` on `Circuit.H (0 : Wire 1)` (`(Circuit.H 0).size = 1`),
    yielding both `σ ^ 2 * Grover.p_succ 0 2 + (1 - σ ^ 2) / 2` and the simplified value `1 / 2`. -/
theorem noisyGrover_circuit_hadamard1_bornProb (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (target : Fin (2 ^ 1)) :
    ((computationalPOVM 1).measure
      (noisyCircuitChannel σ hσ (Circuit.H (0 : Wire 1))
        (MState.pure (Ket.basis (0 : Fin (2 ^ 1))))) target : ℝ) =
      σ ^ 2 * Grover.p_succ 0 2 + (1 - σ ^ 2) / 2 ∧
    ((computationalPOVM 1).measure
      (noisyCircuitChannel σ hσ (Circuit.H (0 : Wire 1))
        (MState.pure (Ket.basis (0 : Fin (2 ^ 1))))) target : ℝ) = 1 / 2 := by
  have hmain : ((computationalPOVM 1).measure
      (noisyCircuitChannel σ hσ (Circuit.H (0 : Wire 1))
        (MState.pure (Ket.basis (0 : Fin (2 ^ 1))))) target : ℝ) =
      σ ^ 2 * Grover.p_succ 0 2 + (1 - σ ^ 2) / 2 := by
    simpa [Circuit.size] using noisyGrover_circuit_bornProb σ hσ (Circuit.H (0 : Wire 1))
      (Ket.basis (0 : Fin (2 ^ 1))) target 0 (circuit_hadamard1_bornProb target)
  exact ⟨hmain, by rw [hmain, p_succ_zero_two]; ring⟩

/-- Concrete 2-qubit (`n = 2`), 1-iteration (`K = 1`) syntactic Grover circuit for marked state
    `3 : Fin (2 ^ 2)` (`|11⟩`), built exclusively from primitive `H`, `Z`, and `CNOT` gates
    (`size = 14`). -/
noncomputable def grover2QubitCircuit : Circuit 2 :=
  let cz : Circuit 2 := Circuit.H 1 ;;ᶜ Circuit.CNOT 0 1 (by decide) ;;ᶜ Circuit.H 1
  let prep : Circuit 2 := Circuit.H 0 ;;ᶜ Circuit.H 1
  let diffuser : Circuit 2 := prep ;;ᶜ Circuit.Z 0 ;;ᶜ Circuit.Z 1 ;;ᶜ cz ;;ᶜ prep
  prep ;;ᶜ cz ;;ᶜ diffuser

@[simp]
lemma size_grover2QubitCircuit : grover2QubitCircuit.size = 14 := rfl

private noncomputable def layerH2 : Circuit 2 :=
  Circuit.H 0 ;;ᶜ Circuit.H 1

private noncomputable def oracle2Circuit : Circuit 2 :=
  Circuit.H 1 ;;ᶜ Circuit.CNOT 0 1 (by decide) ;;ᶜ Circuit.H 1

private noncomputable def diffuser2Circuit : Circuit 2 :=
  layerH2 ;;ᶜ Circuit.Z 0 ;;ᶜ Circuit.Z 1 ;;ᶜ oracle2Circuit ;;ᶜ layerH2

private lemma sqrt_four_eq_two : √(4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by positivity)]

private lemma sum_fin_two_pow_two (f : Fin (2 ^ 2) → ℂ) :
    ∑ x, f x = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

private lemma layerH2_eval :
    layerH2.eval = (hadamardUnitary : 𝐔[Fin (2 ^ 2)]) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  apply Subtype.ext
  rw [layerH2, Circuit.eval_seq, circuit_H_eval, circuit_H_eval]
  change (hadamardAt 2 1).1 * (hadamardAt 2 0).1 = hadamardMatrix 2
  ext i j
  simp only [Matrix.mul_apply, sum_fin_two_pow_two, hadamardAt_apply, Fin.forall_fin_two,
    hadamardMatrix_apply, walshMatrix_apply, walshChar_apply_apply, dotProduct, Fin.sum_univ_two]
  repeat rw [basisBits_eq_div_mod]
  fin_cases i <;> fin_cases j <;> simp [h11]

private lemma oracle2Circuit_eval :
    oracle2Circuit.eval = Grover.oracleUnitary (3 : Fin (2 ^ 2)) := by
  have ha1 : (2 : ℂ)⁻¹ + 2⁻¹ = 1 := by norm_num
  have ha2 : -(2 : ℂ)⁻¹ + -2⁻¹ = -1 := by norm_num
  apply Subtype.ext
  rw [oracle2Circuit, Circuit.eval_seq, Circuit.eval_seq, circuit_H_eval,
      Circuit.CNOT, Circuit.eval_gate, QRegister.pair_zero_one_eq_whole,
      QRegister.whole_embedUnitary]
  change ((hadamardAt 2 1).1 * (Equiv.swap (1 : Fin (2 ^ 2)) 3).permMatrix ℂ) *
    (hadamardAt 2 1).1 = Grover.oracleMatrix 3
  ext i j
  simp only [Matrix.mul_apply, sum_fin_two_pow_two, hadamardAt_apply, Fin.forall_fin_two]
  repeat rw [basisBits_eq_div_mod]
  fin_cases i <;> fin_cases j <;>
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.swap_apply_def,
      Grover.oracleMatrix, ha1, ha2]

private lemma diffuser2_eval :
    diffuser2Circuit.eval = (Grover.diffuserUnitary : 𝐔[Fin (2 ^ 2)]) := by
  apply Subtype.ext
  have hrefl : Grover.oracleMatrix (3 : Fin (2 ^ 2)) *
      (Circuit.Z (1 : Wire 2)).eval.1 * (Circuit.Z (0 : Wire 2)).eval.1 =
      (2 : ℂ) • Matrix.single (0 : Fin (2 ^ 2)) (0 : Fin (2 ^ 2)) 1 - 1 := by
    rw [circuit_Z_eval_val, circuit_Z_eval_val, Grover.oracleMatrix,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.single_apply, Matrix.one_apply]
    repeat rw [basisBits_eq_div_mod]
    fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]
  have hseq : diffuser2Circuit.eval.1 =
      hadamardMatrix 2 *
        ((Grover.oracleMatrix (3 : Fin (2 ^ 2)) *
          (Circuit.Z (1 : Wire 2)).eval.1 * (Circuit.Z (0 : Wire 2)).eval.1) *
        hadamardMatrix 2) := by
    simp [diffuser2Circuit, Circuit.eval_seq, layerH2_eval, oracle2Circuit_eval, Matrix.mul_assoc]
  change diffuser2Circuit.eval.1 = Grover.diffuserMatrix
  rw [hseq, hrefl, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hadamardMatrix_mul_self,
      Matrix.smul_mul, Matrix.mul_smul]
  ext i j
  have hsingle : (hadamardMatrix 2 *
      (Matrix.single (0 : Fin (2 ^ 2)) (0 : Fin (2 ^ 2)) (1 : ℂ) * hadamardMatrix 2)) i j =
      hadamardMatrix 2 i 0 * hadamardMatrix 2 0 j := by
    simp only [Matrix.mul_apply, Matrix.single_apply, sum_fin_two_pow_two]
    norm_num
  rw [Grover.diffuserMatrix, Matrix.sub_apply, Matrix.smul_apply, hsingle,
      hadamardMatrix_apply_zero, hadamardMatrix_zero_apply]
  simp only [Matrix.sub_apply, Matrix.of_apply, smul_eq_mul]
  norm_num [sqrt_four_eq_two]

/-- Evolving `Ket.basis 0` through `grover2QubitCircuit` produces `Grover.groverState 3 1`. -/
theorem grover2QubitCircuit_evolve_basis_zero :
    grover2QubitCircuit.evolve (Ket.basis (0 : Fin (2 ^ 2))).vec =
    Grover.groverState (3 : Fin (2 ^ 2)) 1 := by
  have heval : grover2QubitCircuit.eval =
      Grover.diffuserUnitary * (Grover.oracleUnitary (3 : Fin (2 ^ 2)) * hadamardUnitary) := by
    change (layerH2 ;;ᶜ oracle2Circuit ;;ᶜ diffuser2Circuit).eval = _
    rw [Circuit.eval_seq, Circuit.eval_seq, layerH2_eval, oracle2Circuit_eval, diffuser2_eval,
        mul_assoc]
  simpa [Circuit.evolve, heval, groverFullGates, groverIterGates, idealUnitaryTrajectory,
    applyUnitaryKet, Matrix.mulVec_mulVec] using
    idealUnitaryTrajectory_groverFullGates 2 (3 : Fin (2 ^ 2)) 1

/-- At `K = 1` on `n = 2` qubits (`d = 4`), Grover's algorithm succeeds with certainty:
    `Grover.p_succ 1 4 = 1`. -/
lemma p_succ_one_four : Grover.p_succ 1 4 = 1 := by
  have h := groverState_bornProb (3 : Fin (2 ^ 2)) 1
    (idealUnitaryTrajectory_groverFullGates 2 (3 : Fin (2 ^ 2)) 1)
  have hval : Grover.groverState (3 : Fin (2 ^ 2)) 1 (3 : Fin (2 ^ 2)) = 1 := by
    rw [Grover.groverState, Grover.diffuserMatrix_mulVec, Grover.sum_oracleMatrix_mulVec,
        Grover.oracleMatrix_mulVec, ite_eq_left rfl]
    simp only [Grover.groverState, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num [sqrt_four_eq_two]
  rw [Ket.apply, idealUnitaryTrajectory_groverFullGates, hval] at h
  simpa using h.symm

/-- **Concrete `Circuit 2` witness (`K = 1`, `c.size = 14`, `Grover.p_succ 1 4 = 1`):**
    Instantiating `noisyGrover_circuit_bornProb` on the 14-gate primitive Grover circuit
    `grover2QubitCircuit` yields exact noisy Born probability `σ ^ 28 + (1 - σ ^ 28) / 4`. -/
theorem noisyGrover_circuit_grover2_bornProb (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) :
    ((computationalPOVM 2).measure
      (noisyCircuitChannel σ hσ grover2QubitCircuit
        (MState.pure (Ket.basis (0 : Fin (2 ^ 2))))) (3 : Fin (2 ^ 2)) : ℝ) =
    σ ^ 28 + (1 - σ ^ 28) / 4 := by
  have hideal : ‖(grover2QubitCircuit.evolve (Ket.basis (0 : Fin (2 ^ 2))).vec)
      (3 : Fin (2 ^ 2))‖ ^ 2 = Grover.p_succ 1 (2 ^ 2) :=
    groverState_bornProb (3 : Fin (2 ^ 2)) 1
      (ψ := applyUnitaryKet grover2QubitCircuit.eval (Ket.basis 0))
      grover2QubitCircuit_evolve_basis_zero
  rw [noisyGrover_circuit_bornProb σ hσ grover2QubitCircuit
        (Ket.basis (0 : Fin (2 ^ 2))) (3 : Fin (2 ^ 2)) 1 hideal,
      size_grover2QubitCircuit, show Grover.p_succ 1 (2 ^ 2) = 1 from p_succ_one_four]
  norm_num

/-! ## Verification checks -/

#check @targetBasisState_eq_ketToReal
#check @uniformSuperposition_eq_ketToReal
#check @groverIterGates
#check @groverFullGates
#check @length_groverIterGates
#check @length_groverFullGates
#check @idealUnitaryTrajectory_groverIterGates
#check @idealUnitaryTrajectory_groverFullGates
#check @groverState_bornProb
#check @noisyGrover_unitaryList_succProb
#check @noisyGrover_iterGates_succProb
#check @noisyGrover_fullGates_succProb
#check @noisyGrover_circuit_bornProb
#check @noisyGrover_circuit_trajectory_succProb
#check @noisyGrover_circuit_hadamard1_bornProb
#check @noisyGrover_circuit_grover2_bornProb

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

/--
info: 'IsotropicGrover.noisyGrover_unitaryList_succProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyGrover_unitaryList_succProb

/--
info: 'IsotropicGrover.noisyGrover_iterGates_succProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyGrover_iterGates_succProb

/--
info: 'IsotropicGrover.noisyGrover_fullGates_succProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyGrover_fullGates_succProb

/--
info: 'IsotropicGrover.noisyGrover_circuit_bornProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyGrover_circuit_bornProb

/--
info: 'IsotropicGrover.noisyGrover_circuit_trajectory_succProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyGrover_circuit_trajectory_succProb

/--
info: 'IsotropicGrover.noisyGrover_circuit_hadamard1_bornProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyGrover_circuit_hadamard1_bornProb

/--
info: 'IsotropicGrover.noisyGrover_circuit_grover2_bornProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyGrover_circuit_grover2_bornProb

end IsotropicGrover
