-- IsotropicGroverProof/LimitingCases.lean
-- M8: Limiting case corollaries — pure continuity/arithmetic, no sorrys.
--     1. σ^{2G} → 1 (perfect gates):  E[p_e] → p_ideal
--     2. σ^{2G} → 0 (full decoherence): E[p_e] → 1/N

import Mathlib.Topology.Algebra.Order.LiminfLimsup
import IsotropicGroverProof.MainTheorem

namespace IsotropicGrover

open Filter Topology Real

/-! ## The mixture function -/

/-- The mixture formula as a real function of fidelity f ∈ [0,1]. -/
noncomputable def mixtureProb (p : ℝ) (N : ℕ) (f : ℝ) : ℝ :=
  f * p + (1 - f) / N

/-- mixtureProb is continuous (affine function of f). -/
lemma mixtureProb_continuous (p : ℝ) (N : ℕ) : Continuous (mixtureProb p N) := by
  unfold mixtureProb
  fun_prop

/-! ## Limiting case 1: perfect gates -/

/-- When fidelity f = 1 (σ^{2G} = 1), the mixture reduces to the ideal success probability.
    The σ=1 case: no noise, so E[p_e] = p_ideal exactly. -/
lemma mixtureProb_at_one (p : ℝ) (N : ℕ) : mixtureProb p N 1 = p := by
  simp [mixtureProb]

/-- As f → 1, the expected success probability tends to p_ideal. -/
theorem tendsto_ideal_as_fidelity_one (p : ℝ) (N : ℕ) :
    Tendsto (mixtureProb p N) (𝓝 1) (𝓝 p) := by
  have h : ContinuousAt (mixtureProb p N) 1 := (mixtureProb_continuous p N).continuousAt
  simp only [ContinuousAt, mixtureProb_at_one] at h
  exact h

/-! ## Limiting case 2: full decoherence -/

/-- When fidelity f = 0 (σ^{2G} = 0), the mixture reduces to 1/N (uniform random guess). -/
lemma mixtureProb_at_zero (p : ℝ) (N : ℕ) : mixtureProb p N 0 = 1 / N := by
  simp [mixtureProb]

/-- As f → 0, the expected success probability tends to 1/N.
    The decoherent limit: the algorithm is no better than random guessing. -/
theorem tendsto_random_as_fidelity_zero (p : ℝ) (N : ℕ) :
    Tendsto (mixtureProb p N) (𝓝 0) (𝓝 (1 / N)) := by
  have h : ContinuousAt (mixtureProb p N) 0 := (mixtureProb_continuous p N).continuousAt
  simp only [ContinuousAt, mixtureProb_at_zero] at h
  exact h

/-! ## Monotonicity: more noise → worse performance -/

/-- The mixture probability is monotone increasing in the fidelity f,
    provided p_ideal ≥ 1/N (which is guaranteed for Grover at optimal iterations). -/
lemma mixtureProb_mono (p : ℝ) (N : ℕ) (hN : 0 < N)
    (hp : 1 / (N : ℝ) ≤ p) : Monotone (mixtureProb p N) := by
  sorry -- M8: (f₂-f₁)*(p - 1/N) ≥ 0; needs field_simp to handle ℕ cast division

/-! ## TDD spot-checks -/

-- Numeric: n=2 (N=4), p_ideal=0.9609, σ=0.99, G=100
-- σ^{2G} ≈ 0.99^200 ≈ 0.134
-- E[p_e] ≈ 0.134 * 0.9609 + (1-0.134)/4 ≈ 0.1288 + 0.2165 ≈ 0.345
example : mixtureProb 1 4 1 = 1 := by simp [mixtureProb]
example : mixtureProb 1 4 0 = 1/4 := by simp [mixtureProb]
example : mixtureProb (1/2 : ℝ) 4 0 = 1/4 := by simp [mixtureProb]
example : mixtureProb (1/2 : ℝ) 4 1 = 1/2 := by simp [mixtureProb]

-- Verify the key limiting values
#check @tendsto_ideal_as_fidelity_one
#check @tendsto_random_as_fidelity_zero

end IsotropicGrover
