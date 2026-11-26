-- IsotropicGroverProof/Defs.lean
-- Core state-space definitions: ambient real Euclidean space E n = ℝ^{2·2^n},
-- unit sphere, standard basis vectors, shared dimension lemmas, and computational-basis
-- measurement probability succProb with Parseval normalization.

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Core Definitions for the Isotropic Grover Proof

Ambient Euclidean space, unit sphere, standard basis vectors, and the success-probability
formula for Grover's algorithm.
-/

namespace IsotropicGrover

/-! ## Dimension setup -/

/-- The real dimension of the state space: d = 2 * 2^n = 2^{n+1}. -/
abbrev d (n : ℕ) : ℕ := 2 * 2 ^ n

lemma two_le_d (n : ℕ) : 2 ≤ d n := by
  simp only [d]; have := @Nat.one_le_two_pow n; omega

lemma one_lt_d (n : ℕ) : 1 < d n := by
  have := two_le_d n; omega

lemma cast_d (n : ℕ) : (d n : ℝ) = 2 * (2 ^ n : ℝ) := by
  simp only [d]; push_cast; ring

lemma cast_d_ne_zero (n : ℕ) : (d n : ℝ) ≠ 0 := by
  positivity

lemma cast_d_sub_one_pos (n : ℕ) : 0 < (d n : ℝ) - 1 := by
  have : (1 : ℝ) < (d n : ℝ) := Nat.one_lt_cast.mpr (one_lt_d n)
  linarith

lemma cast_d_sub_one_ne_zero (n : ℕ) : (d n : ℝ) - 1 ≠ 0 :=
  (cast_d_sub_one_pos n).ne'

/-- The ambient Euclidean space ℝ^d. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin (d n))

/-- The unit sphere S^{d-1} ⊂ ℝ^d. -/
abbrev unitSphere (n : ℕ) := Metric.sphere (0 : E n) 1

/-! ## Standard basis vectors -/

/-- The i-th standard basis vector in ℝ^d. -/
noncomputable def stdBasisVec (n : ℕ) (i : Fin (d n)) : E n :=
  EuclideanSpace.single i 1

@[simp]
lemma stdBasisVec_apply (n : ℕ) (i j : Fin (d n)) :
    stdBasisVec n i j = if j = i then 1 else 0 := by
  simp [stdBasisVec, PiLp.single_apply]

lemma stdBasisVec_norm (n : ℕ) (i : Fin (d n)) : ‖stdBasisVec n i‖ = 1 := by
  simp [stdBasisVec, PiLp.norm_single]

lemma inner_stdBasisVec (n : ℕ) (i j : Fin (d n)) :
    inner (𝕜 := ℝ) (stdBasisVec n i) (stdBasisVec n j) = if i = j then 1 else 0 :=
  (orthonormal_iff_ite (𝕜 := ℝ)).mp
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (d n))) i j

lemma inner_stdBasisVec_eq_apply {n : ℕ} (v : E n) (i : Fin (d n)) :
    inner (𝕜 := ℝ) v (stdBasisVec n i) = v i := by
  simp [stdBasisVec, ← EuclideanSpace.basisFun_apply]

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

/-! ## Index bounds for the success probability -/

private lemma succProb_idx0_lt (n : ℕ) (w : Fin (2 ^ n)) : 2 * w.val < d n :=
  Nat.mul_lt_mul_of_pos_left w.isLt (by norm_num)

private lemma succProb_idx1_lt (n : ℕ) (w : Fin (2 ^ n)) : 2 * w.val + 1 < d n := by
  have := Nat.mul_lt_mul_of_pos_left w.isLt (by norm_num : 0 < 2)
  simpa [d] using Nat.lt_of_succ_le (by omega)

/-! ## Success probability -/

/-- The real-component indices for outcome w:
    the real part (index 2w) and imaginary part (index 2w+1) of amplitude w. -/
noncomputable def succProbIdx0 (n : ℕ) (w : Fin (2 ^ n)) : Fin (d n) :=
  ⟨2 * w.val, succProb_idx0_lt n w⟩

noncomputable def succProbIdx1 (n : ℕ) (w : Fin (2 ^ n)) : Fin (d n) :=
  ⟨2 * w.val + 1, succProb_idx1_lt n w⟩

lemma succProbIdx0_inj {n : ℕ} {x y : Fin (2 ^ n)}
    (h : succProbIdx0 n x = succProbIdx0 n y) : x = y := by
  ext; have := congrArg Fin.val h; dsimp [succProbIdx0] at this; omega

lemma succProbIdx1_inj {n : ℕ} {x y : Fin (2 ^ n)}
    (h : succProbIdx1 n x = succProbIdx1 n y) : x = y := by
  ext; have := congrArg Fin.val h; dsimp [succProbIdx1] at this; omega

lemma succProbIdx0_ne_succProbIdx1 {n : ℕ} (x y : Fin (2 ^ n)) :
    succProbIdx0 n x ≠ succProbIdx1 n y := by
  intro h; have := congrArg Fin.val h; dsimp [succProbIdx0, succProbIdx1] at this; omega

/-- The success probability of measuring outcome w given real state vector v.
    In the real representation, p = |a_w|² = α_{2w}² + α_{2w+1}², where
    α_{2w} and α_{2w+1} are the real and imaginary parts of amplitude w. -/
noncomputable def succProb (n : ℕ) (v : E n) (w : Fin (2 ^ n)) : ℝ :=
  inner (𝕜 := ℝ) v (stdBasisVec n (succProbIdx0 n w)) ^ 2 +
  inner (𝕜 := ℝ) v (stdBasisVec n (succProbIdx1 n w)) ^ 2

lemma succProb_nonneg (n : ℕ) (v : E n) (w : Fin (2 ^ n)) : 0 ≤ succProb n v w :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Parseval: the success probabilities sum to the squared norm of v. -/
lemma sum_succProb_eq_norm_sq (n : ℕ) (v : E n) :
    ∑ w : Fin (2 ^ n), succProb n v w = ‖v‖ ^ 2 := by
  simp only [succProb, inner_stdBasisVec_eq_apply]
  -- Parseval: ‖v‖^2 = ∑ i : Fin (d n), (v i)^2
  rw [EuclideanSpace.real_norm_sq_eq]
  -- Reindex RHS via bijection (w,k) ↦ w*2+k : Fin (2^n) × Fin 2 ≃ Fin (d n)
  have hd : 2 ^ n * 2 = d n := by simp [d, mul_comm]
  -- Transform RHS: ∑ i : Fin (d n) → ∑ w, ∑ k : Fin 2 → w*2+0 and w*2+1
  conv_rhs =>
    rw [← Equiv.sum_comp (finProdFinEquiv.trans (finCongr hd)) (fun i => v.ofLp i ^ 2)]
    rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two]
  -- Now both sides are ∑ w, f(succProbIdx0 n w) + f(succProbIdx1 n w)
  -- Match indices: (w, 0) ↦ succProbIdx0 n w and (w, 1) ↦ succProbIdx1 n w
  congr 1; ext w; congr 1
  all_goals {
    -- goal: v.ofLp A ^ 2 = v.ofLp B ^ 2; remove ^2, then prove A = B via Fin.ext
    congr 1
    exact congr_arg v.ofLp (Fin.ext (by
      simp [finProdFinEquiv, succProbIdx0, succProbIdx1]; try omega))
  }

/-! ## TDD spot-checks -/

example : d 0 = 2 := by norm_num [d]
example : d 1 = 4 := by norm_num [d]
example : d 2 = 8 := by norm_num [d]
example : d 3 = 16 := by norm_num [d]

/--
info: 'IsotropicGrover.sum_succProb_eq_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sum_succProb_eq_norm_sq

end IsotropicGrover
