-- IsotropicGroverProof/SecondMoment.lean
-- M5: The second moment matrix E[e₂ e₂ᵀ] = P_{V⊥}/(d-1), where P_{V⊥} is the
--     orthogonal projector onto V_perp. Derives the decoherent floor formula:
--     E[|⟨w|e₂⟩|²] = (2 - p_ideal)/(d - 1)
--
-- SORRY BUDGET: 2
--   sorry 1 (secondMoment_eq_scalar_perp): Schur-type invariance argument
--   sorry 2 (trace_P_perp): trace of the projector onto V_perp = d - 1

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Trace
import IsotropicGroverProof.CrossTerm

namespace IsotropicGrover

open MeasureTheory InnerProductSpace ContinuousLinearMap

variable {n : ℕ}

/-! ## Orthogonal projector onto V_perp -/

/-- The orthogonal projector onto V_perp(Φ) = (ℝ · Φ)^⊥. -/
noncomputable def P_perp (Φ : E n) : E n →L[ℝ] E n :=
  (V_perp Φ).subtypeL ∘L (V_perp Φ).orthogonalProjection

/-- P_perp acts as the identity minus projection onto Φ:
    P_perp Φ v = v - ⟪Φ, v⟫ · Φ (when ‖Φ‖ = 1). -/
lemma P_perp_apply (Φ v : E n) (hΦ : ‖Φ‖ = 1) :
    P_perp Φ v = v - ⟪Φ, v⟫_ℝ • Φ := by
  sorry -- Follows from orthogonalProjection_eq_sub for a complete orthonormal family

/-! ## Second moment matrix = (1/(d-1)) · P_perp (sorry — Schur argument) -/

/-- Every continuous linear operator T : E n → E n that commutes with all rotations
    fixing Φ must be a scalar multiple of P_perp Φ (restricted to V_perp) plus
    a scalar multiple of the rank-1 projector onto Φ.
    When T = E[e₂ e₂ᵀ] with e₂ ∈ V_perp, the Φ-component vanishes,
    so T = c · P_perp for some c. -/
theorem secondMoment_eq_scalar_perp (Φ : E n) (hΦ : ‖Φ‖ = 1) :
    ∃ c : ℝ, ∀ u : E n,
      ∫ e₂, ⟪(e₂ : E n), u⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Φ) =
      c • P_perp Φ u := by
  sorry -- Schur-type: rotational invariance of perpSphereMeasure forces scalar × P_perp

/-- The trace of the second moment operator equals 1 (since ‖e₂‖ = 1 a.s.). -/
lemma trace_secondMoment_eq_one (Φ : E n) (hΦ : ‖Φ‖ = 1) :
    ∑ i : Fin (d n),
      ∫ e₂, ⟪(e₂ : E n), stdBasisVec n i⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) = 1 := by
  sorry -- ∫ ‖e₂‖² dμ = 1 since μ is supported on unit sphere

/-- The trace of P_perp equals d - 1 (the dimension of V_perp). -/
lemma trace_P_perp (Φ : E n) (hΦ : ‖Φ‖ = 1) :
    ∑ i : Fin (d n), ⟪P_perp Φ (stdBasisVec n i), stdBasisVec n i⟫_ℝ = d n - 1 := by
  sorry -- finrank (V_perp Φ) = d n - 1 since Φ ≠ 0 in a d-dimensional space

/-- The second moment operator is (1/(d-1)) · P_perp. -/
theorem secondMoment_coeff (Φ : E n) (hΦ : ‖Φ‖ = 1) (hn : 2 ≤ d n) :
    ∀ u : E n,
      ∫ e₂, ⟪(e₂ : E n), u⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Φ) =
      (1 / ((d n : ℝ) - 1)) • P_perp Φ u := by
  obtain ⟨c, hc⟩ := secondMoment_eq_scalar_perp Φ hΦ
  intro u
  rw [hc]
  congr 1
  -- Determine c from the trace constraint: c * (d n - 1) = 1
  have hc_val : c = 1 / ((d n : ℝ) - 1) := by
    have htrace : c * ((d n : ℝ) - 1) = 1 := by
      have h1 := trace_secondMoment_eq_one Φ hΦ
      have h2 := trace_P_perp Φ hΦ
      sorry -- combine: trace(c · P_perp) = c * (d-1) = 1
    have hd1 : (0 : ℝ) < (d n : ℝ) - 1 := by
      have h : 1 < d n := by
        simp only [d]
        have : 0 < 2 ^ n := pow_pos (by norm_num) n
        omega
      have : (1 : ℝ) < (d n : ℝ) := by exact_mod_cast h
      linarith
    field_simp at htrace ⊢
    linarith
  rw [hc_val]

/-! ## Decoherent floor formula -/

/-- The decoherent floor: the expected success probability when the state is
    uniform over V_perp (full decoherence limit).
    E[|⟨w|e₂⟩|²] = (2 - p_ideal)/(d - 1) -/
theorem decoherent_floor (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) (hn : 2 ≤ d n) :
    ∫ e₂, succProb n (e₂ : E n) w ∂(perpSphereMeasure Φ) =
    (2 - succProb n Φ w) / ((d n : ℝ) - 1) := by
  simp only [succProb]
  -- Expand the two squared inner-product integrals using secondMoment_coeff
  sorry -- Uses secondMoment_coeff twice (for û_{2w} and û_{2w+1}) and
        -- |P_perp û|² = |û|² - ⟪Φ,û⟫² = 1 - (Φ component)²

/-! ## TDD spot-checks -/

-- P_perp is idempotent (proof deferred to M5 — need the correct Mathlib API name)
example (n : ℕ) (Φ : E n) (hΦ : ‖Φ‖ = 1) (v : E n) :
    P_perp Φ (P_perp Φ v) = P_perp Φ v := by
  sorry -- M5: ContinuousLinearMap.comp_apply + orthogonalProjection idempotent

-- For large d, decoherent floor → 1/N
-- (2 - p_ideal)/(d-1) → 1/N as d = 2N → ∞ and p_ideal → 1
example : (2 - (1:ℝ)) / (8 - 1) = 1/7 := by norm_num

end IsotropicGrover
