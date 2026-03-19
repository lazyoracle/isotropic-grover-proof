-- IsotropicGroverProof/IsotropicError.lean
-- M2: The isotropic error model — Poisson kernel marginal density g(θ;σ),
--     the error state Ψ = cos θ · Φ + sin θ · e₂, and the key property E[cos θ] = σ.
--
-- SORRY BUDGET: 1  (was 2; sorry 1 proved below)
--   sorry 1 (poissonMarginal_isProbMeasure): PROVED — normalization via interval integral positivity
--   sorry 2 (poissonMarginal_mean_cos): E[cos θ] = σ — blocked on M6 moment theorem

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import IsotropicGroverProof.Defs

namespace IsotropicGrover

open MeasureTheory Real Set

variable {n : ℕ}

/-! ## Poisson kernel marginal density -/

/-- The unnormalized Poisson kernel marginal density for the isotropic error model.
    g(θ; σ) ∝ (1 - σ²) · sin^{d-2}(θ) / (1 + σ² - 2σ cos θ)^{d/2}
    (Lacalle & Pozo Coronado 2019, equation for the isotropic normal distribution.) -/
noncomputable def poissonKernelDensity (d : ℕ) (σ θ : ℝ) : ℝ :=
  (1 - σ ^ 2) * sin θ ^ (d - 2) /
  (1 + σ ^ 2 - 2 * σ * cos θ) ^ ((d : ℝ) / 2)

/-- Normalization constant: the integral of the unnormalized Poisson kernel over [0, π]. -/
noncomputable def poissonNormConst (d : ℕ) (σ : ℝ) : ℝ :=
  ∫ θ in Set.Icc 0 Real.pi, poissonKernelDensity d σ θ

/-- The Poisson kernel marginal probability measure on [0, π].
    This is the distribution of the perturbation angle θ in a single isotropic error.
    The density is poissonKernelDensity / poissonNormConst, restricted to [0, π]. -/
noncomputable def poissonMarginal (d : ℕ) (σ : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 Real.pi)).withDensity
    (fun θ => ENNReal.ofReal (poissonKernelDensity d σ θ / poissonNormConst d σ))

/-! ## Private helpers for the probability measure proof -/

private lemma denom_pos (σ θ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    0 < 1 + σ ^ 2 - 2 * σ * cos θ := by
  have hcos : cos θ ≤ 1 := Real.cos_le_one θ
  nlinarith [sq_nonneg (σ - cos θ), sq_nonneg (1 - σ), hσ.1, hσ.2]

private lemma poissonKernelDensity_nonneg (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) (_hd : 2 ≤ d) :
    0 ≤ poissonKernelDensity d σ θ := by
  simp only [poissonKernelDensity]
  apply div_nonneg
  · apply mul_nonneg
    · nlinarith [hσ.1, hσ.2, mul_pos hσ.1 hσ.1]
    · exact pow_nonneg (Real.sin_nonneg_of_mem_Icc hθ) _
  · exact Real.rpow_nonneg (by linarith [denom_pos σ θ hσ]) _

private lemma poissonKernelDensity_continuousOn (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ContinuousOn (poissonKernelDensity d σ) (Set.Icc 0 Real.pi) := by
  unfold poissonKernelDensity
  apply ContinuousOn.div
  · exact continuousOn_const.mul (Real.continuous_sin.continuousOn.pow _)
  · apply ContinuousOn.rpow_const
    · exact (continuousOn_const.add continuousOn_const).sub
        (continuousOn_const.mul Real.continuous_cos.continuousOn)
    · intro θ _; left; exact (denom_pos σ θ hσ).ne'
  · intro θ hθ; exact (Real.rpow_pos_of_pos (denom_pos σ θ hσ) _).ne'

private lemma poissonNormConst_pos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hd : 2 ≤ d) : 0 < poissonNormConst d σ := by
  unfold poissonNormConst
  have hf_cont := poissonKernelDensity_continuousOn d σ hσ
  have hf_nonneg : ∀ θ ∈ Set.Ioc 0 Real.pi, 0 ≤ poissonKernelDensity d σ θ :=
    fun θ hθ => poissonKernelDensity_nonneg d σ hσ θ (Set.Ioc_subset_Icc_self hθ) hd
  have hpi2_mem : Real.pi / 2 ∈ Set.Icc 0 Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hf_pos_pi2 : 0 < poissonKernelDensity d σ (Real.pi / 2) := by
    simp only [poissonKernelDensity, Real.sin_pi_div_two, Real.cos_pi_div_two, one_pow]
    apply div_pos
    · exact mul_pos (by nlinarith [hσ.1, hσ.2, mul_pos hσ.1 hσ.1]) one_pos
    · apply Real.rpow_pos_of_pos
      simp only [mul_zero, sub_zero]
      nlinarith [hσ.1, hσ.2, mul_pos hσ.1 hσ.1]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt Real.pi_pos)]
  exact intervalIntegral.integral_pos Real.pi_pos hf_cont hf_nonneg
    ⟨Real.pi / 2, hpi2_mem, hf_pos_pi2⟩

/-! ## Probability measure instance -/

/-- The Poisson marginal is a probability measure when σ ∈ (0,1). -/
theorem poissonMarginal_isProbMeasure (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hd : 2 ≤ d) : IsProbabilityMeasure (poissonMarginal d σ) := by
  rw [isProbabilityMeasure_iff]
  simp only [poissonMarginal, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hc := poissonNormConst_pos d σ hσ hd
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc 0 Real.pi)]
      (fun θ => poissonKernelDensity d σ θ / poissonNormConst d σ) :=
    (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun θ hθ =>
      div_nonneg (poissonKernelDensity_nonneg d σ hσ θ hθ hd) hc.le)
  have hintbl : Integrable (fun θ => poissonKernelDensity d σ θ / poissonNormConst d σ)
      (volume.restrict (Icc 0 Real.pi)) :=
    (poissonKernelDensity_continuousOn d σ hσ |>.div_const _).integrableOn_Icc.integrable
  rw [← ofReal_integral_eq_lintegral_ofReal hintbl hnonneg, integral_div,
    show (∫ θ, poissonKernelDensity d σ θ ∂volume.restrict (Icc 0 Real.pi)) =
        poissonNormConst d σ from rfl,
    div_self hc.ne', ENNReal.ofReal_one]

/-! ## Key moment property (sorry — requires Poisson kernel moment theorem) -/

/-- The mean of cos θ under the Poisson marginal equals σ.
    σ = E[cos θ] = average amplitude overlap between perturbed and ideal state.
    Proof: l=1 case of the Gegenbauer moment theorem (§6 of the derivation). -/
theorem poissonMarginal_mean_cos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ, cos θ ∂(poissonMarginal d σ) = σ := by
  sorry -- Blocked on M6: poissonMarginal_gegen_moment at l=1

/-! ## The isotropic error state -/

/-- The state after a single isotropic error with perturbation angle θ and noise direction e₂.
    Ψ = cos θ · Φ + sin θ · e₂
    where Φ is the ideal state, e₂ ⊥ Φ is a random unit vector. -/
noncomputable def isotropicError (Φ e₂ : E n) (θ : ℝ) : E n :=
  cos θ • Φ + sin θ • e₂

/-- The error state has norm 1 when Φ and e₂ are unit vectors and e₂ ⊥ Φ. -/
lemma isotropicError_norm (Φ e₂ : E n) (θ : ℝ)
    (hΦ : ‖Φ‖ = 1) (he₂ : ‖e₂‖ = 1) (hperp : inner (𝕜 := ℝ) Φ e₂ = 0) :
    ‖isotropicError Φ e₂ θ‖ = 1 := by
  have hsq : ‖isotropicError Φ e₂ θ‖ ^ 2 = 1 := by
    rw [isotropicError, norm_add_sq_real]
    have h1 : ‖cos θ • Φ‖ ^ 2 = cos θ ^ 2 := by
      rw [norm_smul, mul_pow]; simp [Real.norm_eq_abs, sq_abs, hΦ]
    have h2 : ‖sin θ • e₂‖ ^ 2 = sin θ ^ 2 := by
      rw [norm_smul, mul_pow]; simp [Real.norm_eq_abs, sq_abs, he₂]
    have h3 : inner (𝕜 := ℝ) (cos θ • Φ) (sin θ • e₂) = 0 := by
      simp [inner_smul_left, inner_smul_right, hperp]
    rw [h1, h2, h3]
    linarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (isotropicError Φ e₂ θ), sq_nonneg (‖isotropicError Φ e₂ θ‖ - 1)]

/-! ## TDD spot-checks -/

-- isotropicError with θ=0 returns Φ (only the cos term survives)
example (Φ e₂ : E n) : isotropicError Φ e₂ 0 = Φ := by
  simp [isotropicError, cos_zero, sin_zero]

-- isotropicError with θ=π/2 returns e₂ (only the sin term survives)
example (Φ e₂ : E n) : isotropicError Φ e₂ (Real.pi / 2) = e₂ := by
  simp [isotropicError, Real.cos_pi_div_two, Real.sin_pi_div_two]

end IsotropicGrover
