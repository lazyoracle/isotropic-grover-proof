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

/-! ## TDD spot-checks -/

example : d 0 = 2 := by norm_num [d]
example : d 1 = 4 := by norm_num [d]
example : d 2 = 8 := by norm_num [d]
example : d 3 = 16 := by norm_num [d]

end IsotropicGrover
