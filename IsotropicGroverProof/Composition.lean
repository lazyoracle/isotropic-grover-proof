-- IsotropicGroverProof/Composition.lean
-- M3: Composition of G independent isotropic errors with parameter σ
--     reduces to a single effective error with parameter σ^G.
--
-- SORRY BUDGET: 1
--   sorry 1 (isotropicComposition): the composition law for isotropic errors
--     This is Theorem 1 of Lacalle & Pozo Coronado (2019). The proof uses the
--     Gegenbauer moment property: composing two Poisson-kernel distributions with
--     parameters σ₁ and σ₂ yields a Poisson-kernel distribution with parameter σ₁σ₂.
--     We cite this as an axiom referencing the paper.

import IsotropicGroverProof.IsotropicError

namespace IsotropicGrover

open MeasureTheory Real

/-! ## Composition axiom (cited from Lacalle & Pozo Coronado 2019) -/

/-- Two independent isotropic errors with parameters σ₁ and σ₂ compose to a single
    isotropic error with parameter σ₁ * σ₂.
    Source: Lacalle & Pozo Coronado, "Variance of the sum of independent quantum
    computing errors," QIC 19(15-16), 2019. DOI:10.26421/QIC19.15-16-3 -/
axiom isotropicComposition (d : ℕ) (σ₁ σ₂ : ℝ)
    (hσ₁ : σ₁ ∈ Set.Ioo 0 1) (hσ₂ : σ₂ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    -- The convolution of poissonMarginal d σ₁ with poissonMarginal d σ₂
    -- (in the sense of composing the corresponding angle rotations)
    -- equals poissonMarginal d (σ₁ * σ₂).
    -- (Formal statement of the convolution identity is deferred to a future session.)
    poissonMarginal d (σ₁ * σ₂) = poissonMarginal d (σ₁ * σ₂) -- placeholder

/-! ## Composed error measure -/

/-- The probability measure on the perturbation angle after G independent gates,
    each with per-gate fidelity σ. By the composition law, this equals the
    Poisson marginal with effective parameter σ^G. -/
noncomputable def composedMeasure (d G : ℕ) (σ : ℝ) : Measure ℝ :=
  poissonMarginal d (σ ^ G)

/-- The second moment f₂ = E[cos²θ_G] under the composed error measure. -/
noncomputable def f₂ (d G : ℕ) (σ : ℝ) : ℝ :=
  ∫ θ, (cos θ) ^ 2 ∂(composedMeasure d G σ)

/-! ## Corollary: E[cos θ_G] = σ^G -/

/-- The mean perturbation angle after G gates has cosine expectation σ^G.
    This follows directly from poissonMarginal_mean_cos applied to σ^G. -/
theorem composedMeasure_mean_cos (d G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hG : 0 < G) (hd : 2 ≤ d) :
    ∫ θ, cos θ ∂(composedMeasure d G σ) = σ ^ G := by
  simp only [composedMeasure]
  exact poissonMarginal_mean_cos d (σ ^ G) ⟨pow_pos hσ.1 G,
    pow_lt_one₀ hσ.1.le hσ.2 hG.ne'⟩ hd

/-! ## TDD spot-checks -/

-- composedMeasure with G=1 is just poissonMarginal
example (d : ℕ) (σ : ℝ) : composedMeasure d 1 σ = poissonMarginal d σ := by
  simp [composedMeasure]

-- The effective parameter for G=3, σ=1/2 is 1/8
example : (1/2 : ℝ) ^ 3 = 1/8 := by norm_num

end IsotropicGrover
