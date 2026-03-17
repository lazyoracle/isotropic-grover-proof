-- IsotropicGroverProof/CrossTerm.lean
-- M4: The cross term in E[p_e] vanishes because E[e₂] = 0.
--     Derives the expanded form: E[p_e] = f₂ · p_ideal + (1-f₂) · E[|⟨w|e₂⟩|²]
--
-- SORRY BUDGET: 6
--   sorry 1 (perpSphereMeasure): construction of the uniform probability measure
--     on the unit sphere of V_perp (needs sphere measure API)
--   sorry 2 (perpSphereMeasure_isProbMeasure): normalization
--   sorry 3 (perpSphereMeasure_support): support characterization
--   sorry 4 (perpSphereMeasure_neg_invariant): antipodal symmetry of sphere measure
--   sorry 5 (inner_integrable): |⟨e₂,y⟩| ≤ ‖y‖ on sphere → finite integral
--   sorry 6 (succProb_integrable): continuity + compact support

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Prod
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

/-- V_perp is a closed subspace. -/
lemma V_perp_isClosed (Φ : E n) : IsClosed (V_perp Φ : Set (E n)) :=
  Submodule.isClosed_orthogonal _

/-- Negation maps V_perp to itself. -/
lemma neg_mem_V_perp (Φ v : E n) (hv : v ∈ V_perp Φ) : -v ∈ V_perp Φ :=
  (V_perp Φ).neg_mem hv

/-- Inner product with a negated vector. -/
lemma inner_neg_V_perp (û v : E n) :
    inner (𝕜 := ℝ) (-v) û = -inner (𝕜 := ℝ) v û :=
  inner_neg_left v û

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

/-- The perpSphereMeasure is invariant under negation (antipodal symmetry). -/
lemma perpSphereMeasure_neg_invariant (Φ : E n) :
    Measure.map Neg.neg (perpSphereMeasure Φ) = perpSphereMeasure Φ := by
  exact sorry -- antipodal invariance of the uniform sphere measure

/-! ## Integrability of inner products over perpSphereMeasure -/

/-- Inner product ⟨e₂, y⟩ is integrable over perpSphereMeasure.
    Proof sketch: |⟨e₂, y⟩| ≤ ‖y‖ on the unit sphere (Cauchy–Schwarz),
    and perpSphereMeasure is a finite measure. -/
lemma inner_integrable (Φ y : E n) :
    Integrable (fun e₂ => inner (𝕜 := ℝ) e₂ y) (perpSphereMeasure Φ) := by
  sorry -- Blocked: needs |⟨e₂, y⟩| ≤ ‖y‖ on sphere and finite measure

/-- succProb n e₂ w is integrable over perpSphereMeasure.
    Proof sketch: succProb is continuous (sum of squares of inner products),
    and perpSphereMeasure is supported on the compact unit sphere. -/
lemma succProb_integrable (Φ : E n) (w : Fin (2 ^ n)) :
    Integrable (fun e₂ => succProb n e₂ w) (perpSphereMeasure Φ) := by
  sorry -- Blocked: needs continuity of succProb + compact support

/-! ## Algebraic expansion of succProb(isotropicError Φ e₂ θ) -/

/-- Expand succProb(cosθ·Φ + sinθ·e₂, w) into three terms via bilinearity. -/
lemma succProb_isotropicError_expand (Φ e₂ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    succProb n (isotropicError Φ e₂ θ) w =
    cos θ ^ 2 * succProb n Φ w +
    2 * cos θ * sin θ * (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
                         inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
                         inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
                         inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w))) +
    sin θ ^ 2 * succProb n e₂ w := by
  simp only [succProb, isotropicError, inner_add_left, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-! ## E[e₂] = 0 by antipodal symmetry -/

/-- The inner product ⟨e₂, û⟩ has zero expectation for any fixed û.
    Proof: the antipodal map e₂ ↦ -e₂ is measure-preserving on perpSphereMeasure
    and negates ⟨e₂, û⟩, so ∫ ⟨e₂, û⟩ = -∫ ⟨e₂, û⟩ = 0. -/
lemma integral_perp_inner_eq_zero (Φ û : E n) :
    ∫ e₂, inner (𝕜 := ℝ) e₂ û ∂(perpSphereMeasure Φ) = 0 := by
  have hmeas : MeasurePreserving Neg.neg (perpSphereMeasure Φ) (perpSphereMeasure Φ) :=
    ⟨measurable_neg, perpSphereMeasure_neg_invariant Φ⟩
  have heq : ∫ e₂, inner (𝕜 := ℝ) e₂ û ∂(perpSphereMeasure Φ) =
             -(∫ e₂, inner (𝕜 := ℝ) e₂ û ∂(perpSphereMeasure Φ)) := by
    conv_lhs => rw [← hmeas.integral_comp measurableEmbedding_neg
                       (fun e₂ => inner (𝕜 := ℝ) e₂ û)]
    simp_rw [inner_neg_left, integral_neg]
  linarith

/-- The cross term (a linear function of e₂) integrates to zero. -/
lemma integral_cross_term_eq_zero (Φ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    ∫ e₂, 2 * cos θ * sin θ *
          (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
           inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
           inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
           inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))
    ∂(perpSphereMeasure Φ) = 0 := by
  have key0 := integral_perp_inner_eq_zero Φ (stdBasisVec n (succProbIdx0 n w))
  have key1 := integral_perp_inner_eq_zero Φ (stdBasisVec n (succProbIdx1 n w))
  have hsimp : (fun e₂ : E n => 2 * cos θ * sin θ *
          (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
           inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
           inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
           inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))) =
       (fun e₂ => 2 * cos θ * sin θ * inner ℝ Φ (stdBasisVec n (succProbIdx0 n w)) *
           inner ℝ e₂ (stdBasisVec n (succProbIdx0 n w)) +
         2 * cos θ * sin θ * inner ℝ Φ (stdBasisVec n (succProbIdx1 n w)) *
           inner ℝ e₂ (stdBasisVec n (succProbIdx1 n w))) := by ext; ring
  rw [hsimp, integral_add ((inner_integrable Φ _).const_mul _) ((inner_integrable Φ _).const_mul _),
      integral_const_mul, integral_const_mul, key0, key1, mul_zero, mul_zero, add_zero]

/-- The cross term function is integrable. -/
lemma cross_integrable (Φ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    Integrable (fun e₂ : E n => 2 * cos θ * sin θ *
      (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
       inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))) (perpSphereMeasure Φ) := by
  have : (fun e₂ : E n => 2 * cos θ * sin θ *
      (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
       inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))) = fun e₂ =>
    (2 * cos θ * sin θ * inner ℝ Φ (stdBasisVec n (succProbIdx0 n w))) *
      inner ℝ e₂ (stdBasisVec n (succProbIdx0 n w)) +
    (2 * cos θ * sin θ * inner ℝ Φ (stdBasisVec n (succProbIdx1 n w))) *
      inner ℝ e₂ (stdBasisVec n (succProbIdx1 n w)) := by ext; ring
  rw [this]
  exact ((inner_integrable Φ _).const_mul _).add ((inner_integrable Φ _).const_mul _)

/-! ## Inner integral over e₂ -/

/-- After integrating over e₂, the cross term vanishes:
    ∫ e₂, succProb(cosθ·Φ + sinθ·e₂, w) = cos²θ · p_Φ + sin²θ · ∫ e₂, p_{e₂} -/
lemma integral_e₂_succProb (Φ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    ∫ e₂, succProb n (isotropicError Φ e₂ θ) w ∂(perpSphereMeasure Φ) =
    cos θ ^ 2 * succProb n Φ w +
    sin θ ^ 2 * ∫ e₂, succProb n e₂ w ∂(perpSphereMeasure Φ) := by
  have hf1 : Integrable (fun _ : E n => cos θ ^ 2 * succProb n Φ w) (perpSphereMeasure Φ) :=
    integrable_const _
  have hf2 := cross_integrable Φ θ w
  have hf3 : Integrable (fun e₂ => sin θ ^ 2 * succProb n e₂ w) (perpSphereMeasure Φ) :=
    (succProb_integrable Φ w).const_mul _
  -- Explicit beta-reduced type for hf1+hf2, so rw [integral_add hf12 hf3] can match
  have hf12 : Integrable (fun e₂ : E n => cos θ ^ 2 * succProb n Φ w +
      2 * cos θ * sin θ * (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
        inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
        inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
        inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)))) (perpSphereMeasure Φ) :=
    hf1.add hf2
  -- Rewrite integrand pointwise (under the binder) using the algebraic expansion
  simp_rw [succProb_isotropicError_expand Φ _ θ w]
  -- step1: ∫(A + cross) = A (cross integrates to 0, constant has measure 1)
  have step1 : ∫ e₂ : E n, cos θ ^ 2 * succProb n Φ w +
      2 * cos θ * sin θ * (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
       inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
       inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w))) ∂perpSphereMeasure Φ =
      cos θ ^ 2 * succProb n Φ w := by
    rw [integral_add hf1 hf2, integral_const, integral_cross_term_eq_zero]
    simp -- closes ENNReal.toReal 1 • A + 0 = A via IsProbabilityMeasure
  rw [integral_add hf12 hf3, step1, integral_const_mul]

/-! ## Expanded expectation E[p_e] -/

/-- The expected success probability expands as:
    E[p_e] = f₂ · p_ideal + (1 - f₂) · E[|⟨w|e₂⟩|²]
    Proof sketch:
    1. Expand succProb via succProb_isotropicError_expand
    2. Integrate over e₂ using integral_e₂_succProb (cross term = 0)
    3. Integrate over θ: ∫cos²θ dθ = f₂, ∫sin²θ dθ = 1 - f₂ (from isProbMeasure + f₂ def)
    4. Collect terms -/
theorem expanded_E_pe (G : ℕ) (hG : 0 < G) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
          ∂(perpSphereMeasure Φ) ∂(composedMeasure (d n) G σ) =
    f₂ (d n) G σ * succProb n Φ w +
    (1 - f₂ (d n) G σ) * ∫ e₂, succProb n e₂ w ∂(perpSphereMeasure Φ) := by
  have hd : 2 ≤ d n := by simp only [d]; have := @Nat.one_le_two_pow n; omega
  haveI : IsProbabilityMeasure (composedMeasure (d n) G σ) :=
    composedMeasure_isProbMeasure (d n) G σ hσ hG hd
  simp_rw [integral_e₂_succProb Φ _ w]
  -- Goal: ∫ θ, (cos²θ · p + sin²θ · q) ∂μ = f₂·p + (1-f₂)·q
  -- where f₂ = ∫ cos²θ ∂μ definitionally
  set μ := composedMeasure (d n) G σ
  have hcos_int : Integrable (fun θ => cos θ ^ 2) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact (continuous_cos.pow 2).measurable.aestronglyMeasurable
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hsin_int : Integrable (fun θ => sin θ ^ 2) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact (continuous_sin.pow 2).measurable.aestronglyMeasurable
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  have hf₂_def : f₂ (d n) G σ = ∫ θ, cos θ ^ 2 ∂μ := rfl
  have hsin_f₂ : ∫ θ, sin θ ^ 2 ∂μ = 1 - f₂ (d n) G σ := by
    have hsum : ∫ θ, (cos θ ^ 2 + sin θ ^ 2) ∂μ = 1 := by
      simp_rw [Real.cos_sq_add_sin_sq]
      simp
    rw [integral_add hcos_int hsin_int] at hsum
    linarith [hf₂_def]
  -- Rewrite integrand and do the integration
  have hfun : (fun θ => cos θ ^ 2 * succProb n Φ w +
      sin θ ^ 2 * ∫ e₂, succProb n e₂ w ∂(perpSphereMeasure Φ)) =
      fun θ => succProb n Φ w * cos θ ^ 2 +
               (∫ e₂, succProb n e₂ w ∂(perpSphereMeasure Φ)) * sin θ ^ 2 := by
    ext θ; ring
  rw [hfun]
  rw [integral_add (hcos_int.const_mul _) (hsin_int.const_mul _)]
  rw [show (∫ a, succProb n Φ w * cos a ^ 2 ∂μ) = succProb n Φ w * ∫ a, cos a ^ 2 ∂μ from
        integral_const_mul _ _,
      show (∫ a, (∫ e₂, succProb n e₂ w ∂perpSphereMeasure Φ) * sin a ^ 2 ∂μ) =
        (∫ e₂, succProb n e₂ w ∂perpSphereMeasure Φ) * ∫ a, sin a ^ 2 ∂μ from
        integral_const_mul _ _]
  rw [hsin_f₂, ← hf₂_def]
  ring

/-! ## TDD spot-checks -/

-- V_perp contains vectors orthogonal to Φ
example (i j : Fin (d n)) (hij : i ≠ j) :
    stdBasisVec n j ∈ V_perp (stdBasisVec n i) := by
  rw [mem_V_perp_iff]
  have h := (orthonormal_iff_ite (𝕜 := ℝ)).mp
              (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (d n)))
  have key : inner (𝕜 := ℝ) (stdBasisVec n i) (stdBasisVec n j) = if i = j then 1 else 0 := by
    simp only [stdBasisVec]
    exact h i j
  rw [key, if_neg hij]

-- Negation stays in V_perp
example (Φ v : E n) (hv : v ∈ V_perp Φ) : -v ∈ V_perp Φ :=
  Submodule.neg_mem _ hv

-- The algebraic expansion holds pointwise
example (Φ e₂ : E n) (θ : ℝ) (w : Fin (2 ^ n)) :
    succProb n (isotropicError Φ e₂ θ) w =
    cos θ ^ 2 * succProb n Φ w +
    2 * cos θ * sin θ * (inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx0 n w)) *
                         inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) +
                         inner (𝕜 := ℝ) Φ (stdBasisVec n (succProbIdx1 n w)) *
                         inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w))) +
    sin θ ^ 2 * succProb n e₂ w :=
  succProb_isotropicError_expand Φ e₂ θ w

end IsotropicGrover
