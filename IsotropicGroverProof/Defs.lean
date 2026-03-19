-- IsotropicGroverProof/Defs.lean
-- M1: Core types — ambient Euclidean space, unit sphere, standard basis vectors,
--     and the success-probability formula for Grover's algorithm.
--
-- SORRY BUDGET: 0 (this file should compile without any sorry)

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

namespace IsotropicGrover

/-! ## Dimension setup -/

/-- The real dimension of the state space: d = 2 * 2^n = 2^{n+1}. -/
abbrev d (n : ℕ) : ℕ := 2 * 2 ^ n

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
  simp [stdBasisVec, EuclideanSpace.single_apply]

lemma stdBasisVec_norm (n : ℕ) (i : Fin (d n)) : ‖stdBasisVec n i‖ = 1 := by
  simp [stdBasisVec, EuclideanSpace.norm_single]

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
  -- Reduce inner products to components: inner ℝ v (single i 1) = v i
  -- using the @[simp] lemma inner_basisFun_real + basisFun_apply
  have hi : ∀ (i : Fin (d n)), inner (𝕜 := ℝ) v (stdBasisVec n i) = v i := fun i => by
    simp [stdBasisVec, ← EuclideanSpace.basisFun_apply]
  simp only [succProb, hi]
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

end IsotropicGrover
