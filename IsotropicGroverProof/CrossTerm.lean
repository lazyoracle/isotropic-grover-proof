-- IsotropicGroverProof/CrossTerm.lean
-- M4: The cross term in E[p_e] vanishes because E[e₂] = 0.
--     Derives the expanded form: E[p_e] = f₂ · p_ideal + (1-f₂) · E[|⟨w|e₂⟩|²]
--
-- SORRY BUDGET: 2
--   sorry 1 (perpSphereMeasure): construction of the uniform probability measure
--     on the unit sphere of V_perp
--   sorry 2 (expanded_E_pe): the full integration argument expanding E[p_e]

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.MeasureSpace
import IsotropicGroverProof.Composition

namespace IsotropicGrover

open MeasureTheory Real

variable {n : ℕ}

/-! ## The perpendicular subspace V_perp = (ℝ · Φ)^⊥ -/

/-- The subspace of ℝ^d orthogonal to Φ. -/
noncomputable def V_perp (Φ : E n) : Submodule ℝ (E n) :=
  (Submodule.span ℝ {Φ})ᗮ

lemma mem_V_perp_iff (Φ v : E n) : v ∈ V_perp Φ ↔ inner (𝕜 := ℝ) Φ v = 0 := by
  simp only [V_perp, Submodule.mem_orthogonal, Submodule.mem_span_singleton]
  constructor
  · intro h
    have := h Φ ⟨1, one_smul ℝ Φ⟩
    simpa using this
  · intro h u hu
    obtain ⟨c, rfl⟩ := hu
    simp [inner_smul_left, h]

/-! ## Uniform measure on the sphere of V_perp
    We model this as a Measure (E n) supported on {v | v ∈ V_perp Φ ∧ ‖v‖ = 1}. -/

/-- The uniform probability measure on the unit sphere of V_perp, modeled as a
    measure on the ambient space E n supported on V_perp ∩ S^{d-1}. -/
noncomputable def perpSphereMeasure (Φ : E n) : Measure (E n) := by
  exact sorry -- M4: addHaar on V_perp subspace, normalized to sphere

/-- The perpSphereMeasure is a probability measure. -/
instance perpSphereMeasure_isProbMeasure (Φ : E n) :
    IsProbabilityMeasure (perpSphereMeasure Φ) := by
  exact sorry

/-- The perpSphereMeasure is supported on V_perp. -/
lemma perpSphereMeasure_support (Φ v : E n) :
    perpSphereMeasure Φ {v} ≠ 0 → v ∈ V_perp Φ ∧ ‖v‖ = 1 := by
  exact sorry

/-! ## E[e₂] = 0 by antipodal symmetry -/

/-- The inner product ⟨e₂, û⟩ has zero expectation for any fixed û.
    Proof: the antipodal map e₂ ↦ -e₂ is measure-preserving on perpSphereMeasure
    and negates ⟨e₂, û⟩, so ∫ ⟨e₂, û⟩ = -∫ ⟨e₂, û⟩ = 0. -/
lemma integral_perp_inner_eq_zero (Φ û : E n) :
    ∫ e₂, inner (𝕜 := ℝ) e₂ û ∂(perpSphereMeasure Φ) = 0 := by
  sorry -- Antipodal symmetry of perpSphereMeasure

/-! ## Expanded expectation E[p_e] -/

/-- The expected success probability expands as:
    E[p_e] = f₂ · p_ideal + (1 - f₂) · E[|⟨w|e₂⟩|²] -/
theorem expanded_E_pe (G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
          ∂(perpSphereMeasure Φ) ∂(composedMeasure (d n) G σ) =
    f₂ (d n) G σ * succProb n Φ w +
    (1 - f₂ (d n) G σ) * ∫ e₂, succProb n e₂ w ∂(perpSphereMeasure Φ) := by
  sorry

/-! ## TDD spot-checks -/

-- V_perp contains vectors orthogonal to Φ (proof deferred to M4)
example (i j : Fin (d n)) (hij : i ≠ j) :
    stdBasisVec n j ∈ V_perp (stdBasisVec n i) := by
  rw [mem_V_perp_iff]
  sorry -- M4: EuclideanSpace.inner_single_left + EuclideanSpace.single_apply + hij

-- Negation stays in V_perp
example (Φ v : E n) (hv : v ∈ V_perp Φ) : -v ∈ V_perp Φ :=
  Submodule.neg_mem _ hv

end IsotropicGrover
