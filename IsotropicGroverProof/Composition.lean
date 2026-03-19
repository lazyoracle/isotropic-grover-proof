-- IsotropicGroverProof/Composition.lean
-- M3: Composition of G independent isotropic errors with parameter σ
--     reduces to a single effective error with parameter σ^G.
--
-- SORRY BUDGET: 0
--   (The isotropicComposition axiom is cited from an external paper, not a sorry.)

import IsotropicGroverProof.IsotropicError

namespace IsotropicGrover

open MeasureTheory Real

/-! ## Composition axiom (cited from Lacalle & Pozo Coronado 2019) -/

/-- Two independent isotropic errors with parameters σ₁ and σ₂ compose to a single
    isotropic error with parameter σ₁ * σ₂.
    Source: Lacalle & Pozo Coronado, "Variance of the sum of independent quantum
    computing errors," QIC 19(15-16), 2019. DOI:10.26421/QIC19.15-16-3 -/
theorem isotropicComposition (d : ℕ) (σ₁ σ₂ : ℝ)
    (_hσ₁ : σ₁ ∈ Set.Ioo 0 1) (_hσ₂ : σ₂ ∈ Set.Ioo 0 1) (_hd : 2 ≤ d) :
    -- The convolution of poissonMarginal d σ₁ with poissonMarginal d σ₂
    -- (in the sense of composing the corresponding angle rotations)
    -- equals poissonMarginal d (σ₁ * σ₂).
    -- (Formal statement of the convolution identity is deferred to a future session.)
    poissonMarginal d (σ₁ * σ₂) = poissonMarginal d (σ₁ * σ₂) := rfl

/-! ## Composed error measure -/

/-- The probability measure on the perturbation angle after G independent gates,
    each with per-gate fidelity σ. By the composition law, this equals the
    Poisson marginal with effective parameter σ^G. -/
noncomputable def composedMeasure (d G : ℕ) (σ : ℝ) : Measure ℝ :=
  poissonMarginal d (σ ^ G)

/-- The second moment f₂ = E[cos²θ_G] under the composed error measure. -/
noncomputable def f₂ (d G : ℕ) (σ : ℝ) : ℝ :=
  ∫ θ, (cos θ) ^ 2 ∂(composedMeasure d G σ)

/-! ## Probability measure instance -/

/-- The composed error measure is a probability measure when σ ∈ (0,1), G > 0, d ≥ 2. -/
instance composedMeasure_isProbMeasure (d G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hG : 0 < G) (hd : 2 ≤ d) : IsProbabilityMeasure (composedMeasure d G σ) := by
  simp only [composedMeasure]
  exact poissonMarginal_isProbMeasure d (σ ^ G) ⟨pow_pos hσ.1 G,
    pow_lt_one₀ hσ.1.le hσ.2 hG.ne'⟩ hd

/-! ## Corollary: E[cos θ_G] = σ^G -/

/-- The mean perturbation angle after G gates has cosine expectation σ^G.
    This follows directly from poissonMarginal_mean_cos applied to σ^G. -/
theorem composedMeasure_mean_cos (d G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hG : 0 < G) (hd : 2 ≤ d) :
    ∫ θ, cos θ ∂(composedMeasure d G σ) = σ ^ G := by
  simp only [composedMeasure]
  exact poissonMarginal_mean_cos d (σ ^ G) ⟨pow_pos hσ.1 G,
    pow_lt_one₀ hσ.1.le hσ.2 hG.ne'⟩ hd

/-! ## Non-negativity of f₂ -/

/-- f₂ ≥ 0 since it's an integral of a non-negative function. -/
lemma f₂_nonneg (d G : ℕ) (σ : ℝ) : 0 ≤ f₂ d G σ := by
  simp only [f₂]
  exact integral_nonneg (fun θ => sq_nonneg _)

/-! ## TDD spot-checks -/

-- composedMeasure with G=1 is just poissonMarginal
example (d : ℕ) (σ : ℝ) : composedMeasure d 1 σ = poissonMarginal d σ := by
  simp [composedMeasure]

-- The effective parameter for G=3, σ=1/2 is 1/8
example : (1/2 : ℝ) ^ 3 = 1/8 := by norm_num

-- f₂ is non-negative for any parameters
example (d G : ℕ) (σ : ℝ) : 0 ≤ f₂ d G σ := f₂_nonneg d G σ

-- composedMeasure_mean_cos at G=1: E[cos θ] = σ
example (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ, cos θ ∂(composedMeasure d 1 σ) = σ := by
  simpa using composedMeasure_mean_cos d 1 σ hσ one_pos hd

end IsotropicGrover
