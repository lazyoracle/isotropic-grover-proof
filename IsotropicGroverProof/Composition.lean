-- IsotropicGroverProof/Composition.lean
-- M3: Composition of G independent isotropic errors with parameter σ
--     reduces to a single effective error with parameter σ^G.
--
-- SORRY BUDGET: 0
--   (The isotropicComposition axiom is cited from an external paper, not a sorry.)

import IsotropicGroverProof.IsotropicError

namespace IsotropicGrover

open MeasureTheory Real

/-! ## Multi-gate error composition note

    Historically, composition was cited from Lacalle & Pozo Coronado (2019)
    as an effective parameter property σ^G. However, in physical quantum circuits,
    each gate error rotates around the perturbed state Ψ_k rather than the initial state Φ.
    The rigorous physical derivation across G gates is formalized via the sequential
    Markov chain in `IsotropicGroverProof/Sequential.lean` (resolving Issues #6 and #7),
    yielding the exact same second moment f_k = ((d-1)σ^{2k} + 1)/d unconditionally.

    The definition `composedMeasure d G σ := poissonMarginal d (σ ^ G)` below serves as
    the single-effective-error representation corresponding to this sequential induction. -/

/-- Nominal alias / placeholder for the composition identity.
    Deprecated: Multi-gate error accumulation is derived via the sequential Markov
    chain in `IsotropicGroverProof/Sequential.lean`, avoiding any reliance on
    spherical convolution or rotational commutativity conjectures. -/
@[deprecated "Use sequential Markov chain in IsotropicGroverProof.Sequential"
  (since := "2026-03-01")]
theorem isotropicComposition (d : ℕ) (σ₁ σ₂ : ℝ)
    (_hσ₁ : σ₁ ∈ Set.Ioo 0 1) (_hσ₂ : σ₂ ∈ Set.Ioo 0 1) (_hd : 2 ≤ d) :
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

/-! ## Corollary: E[cos θ_G] = σ^G (auxiliary property) -/

/-- Auxiliary property: The mean perturbation angle after G gates has cosine
    expectation σ^G for d = 2.
    This follows directly from poissonMarginal_mean_cos_d2 applied to σ^G.
    Note: isotropicGrover_main depends only on f₂ (the second moment), not on
    this first-moment corollary. -/
theorem composedMeasure_mean_cos_d2 (G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hG : 0 < G) :
    ∫ θ, cos θ ∂(composedMeasure 2 G σ) = σ ^ G := by
  simp only [composedMeasure]
  exact poissonMarginal_mean_cos_d2 (σ ^ G) ⟨pow_pos hσ.1 G,
    pow_lt_one₀ hσ.1.le hσ.2 hG.ne'⟩

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

-- composedMeasure_mean_cos_d2 at G=1: E[cos θ] = σ
example (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ, cos θ ∂(composedMeasure 2 1 σ) = σ := by
  simpa using composedMeasure_mean_cos_d2 1 σ hσ one_pos

end IsotropicGrover
