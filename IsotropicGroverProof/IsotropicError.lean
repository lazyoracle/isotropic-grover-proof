-- IsotropicGroverProof/IsotropicError.lean
-- M2: The isotropic error model — Poisson kernel marginal density g(θ;σ),
--     the error state Ψ = cos θ · Φ + sin θ · e₂, and 1D FTC recurrences for
--     all-dimension first and second moments of the Poisson marginal.
--
-- SORRY BUDGET: 0
-- AXIOM BUDGET: 0
--   PROVED (poissonMarginal_isProbMeasure): normalization via interval integral positivity
--   PROVED (poissonMarginal_mean_cos): first moment E[cos θ] = σ for all d ≥ 2 via 1D FTC
--     and two-step induction from d = 2 (complex Poisson) and d = 3 (elementary antiderivative)
--   PROVED (halfcircle_cos_sq_eq): unnormalized second moment recurrence for all d ≥ 2 via 1D FTC

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import IsotropicGroverProof.Defs

/-!
# Isotropic Error Model

Poisson kernel marginal density `g(θ; σ)`, the error state `Ψ = cos θ · Φ + sin θ · e₂`,
and all-dimension first and second moment recurrences (`E[cos θ] = σ` and `halfcircle_cos_sq_eq`)
for `d ≥ 2`.
-/

namespace IsotropicGrover

open MeasureTheory Real Set intervalIntegral

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

private lemma poissonKernelDensity_continuous (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    Continuous (poissonKernelDensity d σ) := by
  unfold poissonKernelDensity
  apply Continuous.div
  · exact continuous_const.mul (Real.continuous_sin.pow _)
  · apply Continuous.rpow_const
    · exact (continuous_const.add continuous_const).sub
        (continuous_const.mul Real.continuous_cos)
    · intro θ; left; exact (denom_pos σ θ hσ).ne'
  · intro θ; exact (Real.rpow_pos_of_pos (denom_pos σ θ hσ) _).ne'

private lemma poissonKernelDensity_continuousOn (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ContinuousOn (poissonKernelDensity d σ) (Set.Icc 0 Real.pi) :=
  (poissonKernelDensity_continuous d σ hσ).continuousOn

/-- The normalization constant of the Poisson kernel marginal is strictly positive
    for `σ ∈ (0, 1)` and `d ≥ 2`. -/
lemma poissonNormConst_pos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
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

/-- Set integral over `[0, π]` equals the interval integral `0..π`. -/
lemma Icc_to_interval_d2 (f : ℝ → ℝ) :
    ∫ θ in Set.Icc (0 : ℝ) Real.pi, f θ = ∫ θ in (0 : ℝ)..Real.pi, f θ := by
  rw [intervalIntegral.integral_of_le Real.pi_pos.le,
    ← integral_Icc_eq_integral_Ioc' (f := f) Real.volume_singleton]

/-- `poissonNormConst d σ` expressed as an `intervalIntegral` over `0..π`. -/
lemma poissonNormConst_eq_intervalIntegral (d : ℕ) (σ : ℝ) :
    poissonNormConst d σ = ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ :=
  Icc_to_interval_d2 _

/-- Generic reduction of expectations under `poissonMarginal d σ` to an `intervalIntegral`
    over `0..π` divided by `poissonNormConst d σ`. -/
lemma integral_poissonMarginal_eq (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d)
    {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ θ, f θ ∂(poissonMarginal d σ) =
    (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * f θ) / poissonNormConst d σ := by
  let _ := hf
  unfold poissonMarginal
  have hnc_pos : 0 < poissonNormConst d σ := poissonNormConst_pos d σ hσ hd
  have h_meas : Measurable (fun θ =>
      ENNReal.ofReal (poissonKernelDensity d σ θ / poissonNormConst d σ)) :=
    ((poissonKernelDensity_continuous d σ hσ).measurable.div_const _).ennreal_ofReal
  have h_lt_top : ∀ᵐ θ ∂MeasureTheory.volume.restrict (Set.Icc 0 Real.pi),
      ENNReal.ofReal (poissonKernelDensity d σ θ / poissonNormConst d σ) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul h_meas h_lt_top]
  have hnn_ae : ∀ᵐ θ ∂MeasureTheory.volume.restrict (Set.Icc 0 Real.pi),
      0 ≤ poissonKernelDensity d σ θ / poissonNormConst d σ := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _
      (fun θ hθ => div_nonneg (poissonKernelDensity_nonneg d σ hσ θ hθ hd) hnc_pos.le)
  have step1 : ∫ θ,
        (ENNReal.ofReal (poissonKernelDensity d σ θ /
          poissonNormConst d σ)).toReal • f θ
        ∂MeasureTheory.volume.restrict (Set.Icc 0 Real.pi) =
      ∫ θ in Set.Icc 0 Real.pi, poissonKernelDensity d σ θ / poissonNormConst d σ * f θ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hnn_ae] with θ hθ
    rw [ENNReal.toReal_ofReal hθ, smul_eq_mul]
  rw [step1]
  simp_rw [div_mul_eq_mul_div]
  rw [MeasureTheory.integral_div, Icc_to_interval_d2]

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
  rw [← ofReal_integral_eq_lintegral_ofReal hintbl hnonneg, MeasureTheory.integral_div,
    show (∫ θ, poissonKernelDensity d σ θ ∂volume.restrict (Icc 0 Real.pi)) =
        poissonNormConst d σ from rfl,
    div_self hc.ne', ENNReal.ofReal_one]

/-! ## Key moment property -/

/-! ### d=2 helpers: complex Poisson formula yields ∫ pKD2*cos = π*σ -/

private lemma poissonKernelDensity_d2 (σ θ : ℝ) : poissonKernelDensity 2 σ θ =
    (1 - σ ^ 2) / (1 + σ ^ 2 - 2 * σ * cos θ) := by
  unfold poissonKernelDensity; norm_num

private lemma norm_sq_exp_sub_d2 (σ θ : ℝ) :
    ‖(Complex.exp (↑θ * Complex.I) - ↑σ : ℂ)‖^2 = 1 + σ^2 - 2*σ*(cos θ) := by
  have h1 : (Complex.exp (↑θ * Complex.I) - ↑σ).re = cos θ - σ := by
    simp [Complex.exp_mul_I, Complex.cos_ofReal_re]
  have h2 : (Complex.exp (↑θ * Complex.I) - ↑σ).im = sin θ := by
    simp [Complex.exp_mul_I, Complex.sin_ofReal_re]
  rw [RCLike.norm_sq_eq_def]
  rw [← show (Complex.exp (↑θ * Complex.I) - ↑σ).re =
    RCLike.re (Complex.exp (↑θ * Complex.I) - ↑σ) from rfl]
  rw [← show (Complex.exp (↑θ * Complex.I) - ↑σ).im =
    RCLike.im (Complex.exp (↑θ * Complex.I) - ↑σ) from rfl]
  rw [h1, h2]; nlinarith [Real.sin_sq_add_cos_sq θ]

private lemma pK_is_pKDens_d2 (σ θ : ℝ) :
    poissonKernel (0:ℂ) (σ:ℂ) (Complex.exp (↑θ * Complex.I)) = poissonKernelDensity 2 σ θ := by
  rw [poissonKernel_def, poissonKernelDensity_d2]
  simp only [sub_zero, Complex.norm_exp_ofReal_mul_I, one_pow]
  rw [norm_sq_exp_sub_d2]; norm_num

private lemma pK_circ_cont_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    Continuous (fun θ : ℝ => poissonKernel (0:ℂ) (σ:ℂ) (circleMap 0 1 θ)) := by
  unfold poissonKernel; simp only [sub_zero]
  apply Continuous.div
  · exact (continuous_circleMap 0 1 |>.norm.pow 2).sub continuous_const
  · exact (continuous_circleMap 0 1 |>.sub continuous_const |>.norm.pow 2)
  · intro θ; apply pow_ne_zero; rw [norm_ne_zero_iff]
    exact sub_ne_zero.mpr (by
      intro h; have : ‖circleMap (0:ℂ) 1 θ‖ = ‖(σ:ℂ)‖ := by rw [h]
      rw [norm_circleMap_zero] at this; simp [Complex.norm_real, abs_of_pos hσ.1] at this
      linarith [hσ.2])

private lemma pK_id_intbl_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    IntervalIntegrable (fun θ => (poissonKernel (0:ℂ) (σ:ℂ) • id) (circleMap 0 1 θ))
    volume 0 (2 * Real.pi) := by
  apply ContinuousOn.intervalIntegrable; apply Continuous.continuousOn
  have hfun : (fun θ : ℝ => (poissonKernel (0:ℂ) (σ:ℂ) • id) (circleMap 0 1 θ))
      = fun θ : ℝ =>
        (↑(poissonKernel (0:ℂ) (σ:ℂ) (circleMap 0 1 θ)) : ℂ) *
          circleMap (0:ℂ) 1 θ := by
    funext θ
    change poissonKernel (0:ℂ) (↑σ) (circleMap 0 1 θ) • id (circleMap 0 1 θ) = _
    rw [Function.id_def]; exact RCLike.real_smul_eq_coe_mul _ _
  rw [hfun]
  exact (Complex.continuous_ofReal.comp (pK_circ_cont_d2 σ hσ)).mul (continuous_circleMap 0 1)

private lemma pK_const_intbl_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    IntervalIntegrable (fun θ => (poissonKernel (0:ℂ) (σ:ℂ) • (fun _ => (1:ℂ))) (circleMap 0 1 θ))
    volume 0 (2 * Real.pi) := by
  apply ContinuousOn.intervalIntegrable; apply Continuous.continuousOn
  have hfun : (fun θ : ℝ => (poissonKernel (0:ℂ) (σ:ℂ) • (fun _ => (1:ℂ))) (circleMap 0 1 θ))
      = fun θ : ℝ => (↑(poissonKernel (0:ℂ) (σ:ℂ) (circleMap 0 1 θ)) : ℂ) := by
    funext θ
    change poissonKernel (0:ℂ) (↑σ) (circleMap 0 1 θ) • (1:ℂ) = _
    exact (RCLike.real_smul_eq_coe_mul _ 1).trans (mul_one _)
  rw [hfun]; exact Complex.continuous_ofReal.comp (pK_circ_cont_d2 σ hσ)

private lemma fullcircle_re_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (f : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) 1))
    (hf_intbl : IntervalIntegrable (fun θ => (poissonKernel (0 : ℂ) (σ : ℂ) • f) (circleMap 0 1 θ))
      volume 0 (2 * Real.pi)) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi,
      ((poissonKernel (0:ℂ) (σ:ℂ) • f) (circleMap 0 1 θ)).re = (f (σ : ℂ)).re := by
  have hw : (σ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball, Complex.norm_real, abs_of_pos hσ.1, hσ.2]
  have key0 : (Real.circleAverage (poissonKernel (0:ℂ) (σ:ℂ) • f) 0 1).re = (f (σ : ℂ)).re :=
    congrArg Complex.re (hf.circleAverage_poissonKernel_smul hw)
  rw [Real.circleAverage_def] at key0
  have key : (((2 * Real.pi)⁻¹ : ℝ) • ∫ (θ : ℝ) in (0:ℝ)..2 * Real.pi,
      (poissonKernel (0:ℂ) (↑σ) • f) (circleMap 0 1 θ) : ℂ).re = (f (σ : ℂ)).re := key0
  simp only [Complex.smul_re, smul_eq_mul] at key
  rwa [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hf_intbl] at key

private lemma fullcircle_cos_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, poissonKernelDensity 2 σ θ * cos θ = σ := by
  have h := fullcircle_re_d2 σ hσ id differentiableOn_id.diffContOnCl (pK_id_intbl_d2 σ hσ)
  have hval : (id (σ : ℂ)).re = σ := Complex.ofReal_re σ
  rw [hval] at h
  have heq : ∀ θ : ℝ, ((poissonKernel (0:ℂ) (↑σ) • (id : ℂ → ℂ)) (circleMap 0 1 θ)).re =
      poissonKernelDensity 2 σ θ * cos θ := by
    intro θ
    change (poissonKernel (0:ℂ) (↑σ) (circleMap 0 1 θ) • circleMap 0 1 θ).re = _
    have hcm : circleMap (0:ℂ) 1 θ = Complex.exp (↑θ * Complex.I) := by simp [circleMap]
    rw [hcm]; simp only [Complex.smul_re]
    rw [pK_is_pKDens_d2, Complex.exp_mul_I]
    simp [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.I_re,
          Complex.I_im, Complex.sin_ofReal_re]
  simp_rw [heq] at h; linarith

private lemma fullcircle_norm_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, poissonKernelDensity 2 σ θ = 1 := by
  have h := fullcircle_re_d2 σ hσ (fun _ => 1)
    (differentiableOn_const _ |>.diffContOnCl) (pK_const_intbl_d2 σ hσ)
  have hval : ((fun _ : ℂ => (1:ℂ)) (σ : ℂ)).re = 1 := Complex.one_re
  rw [hval] at h
  have heq : ∀ θ : ℝ, ((poissonKernel (0:ℂ) (↑σ) • (fun _ : ℂ => (1:ℂ))) (circleMap 0 1 θ)).re =
      poissonKernelDensity 2 σ θ := by
    intro θ
    rw [show (poissonKernel (0:ℂ) (↑σ) • (fun _ : ℂ => (1:ℂ))) (circleMap 0 1 θ) =
        poissonKernel (0:ℂ) (↑σ) (circleMap 0 1 θ) • (1:ℂ) from rfl]
    rw [show poissonKernel (0:ℂ) (↑σ) (circleMap 0 1 θ) • (1:ℂ) =
      ↑(poissonKernel (0:ℂ) (↑σ) (circleMap 0 1 θ)) * 1 from RCLike.real_smul_eq_coe_mul _ _]
    simp only [mul_one, Complex.ofReal_re]
    have hcm : circleMap (0:ℂ) 1 θ = Complex.exp (↑θ * Complex.I) := by simp [circleMap]
    rw [hcm, pK_is_pKDens_d2]
  simp_rw [heq] at h; linarith

private lemma fold_sym_d2 (f : ℝ → ℝ) (hf : ∀ θ, f (2 * Real.pi - θ) = f θ)
    (hf_cont : Continuous f) :
    ∫ θ in (0:ℝ)..2 * Real.pi, f θ = 2 * ∫ θ in (0:ℝ)..Real.pi, f θ := by
  have hf_int1 : IntervalIntegrable f MeasureTheory.volume 0 Real.pi :=
    hf_cont.intervalIntegrable 0 Real.pi
  have hf_int2 : IntervalIntegrable f MeasureTheory.volume Real.pi (2 * Real.pi) :=
    hf_cont.intervalIntegrable Real.pi (2 * Real.pi)
  have split := intervalIntegral.integral_add_adjacent_intervals hf_int1 hf_int2
  have key : ∫ θ in Real.pi..2 * Real.pi, f θ = ∫ θ in (0:ℝ)..Real.pi, f θ := by
    conv_lhs =>
      arg 1; ext θ
      rw [show f θ = (fun x => f (2 * Real.pi - x)) (2 * Real.pi - θ) from by simp]
    rw [intervalIntegral.integral_comp_sub_left (fun x => f (2 * Real.pi - x))]
    simp only [show 2 * Real.pi - 2 * Real.pi = 0 from by ring,
               show 2 * Real.pi - Real.pi = Real.pi from by ring]
    congr 1; funext θ; exact hf θ
  linarith [split, key,
    show ∫ θ in (0:ℝ)..2 * Real.pi, f θ = ∫ x in (0:ℝ)..2 * Real.pi, f x from rfl,
    show ∫ θ in (0:ℝ)..Real.pi, f θ = ∫ x in (0:ℝ)..Real.pi, f x from rfl,
    show ∫ θ in Real.pi..2 * Real.pi, f θ = ∫ x in Real.pi..2 * Real.pi, f x from rfl]

private lemma halfcircle_cos_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ in (0:ℝ)..Real.pi, poissonKernelDensity 2 σ θ * cos θ = Real.pi * σ := by
  have hcont : Continuous (fun θ => poissonKernelDensity 2 σ θ * cos θ) :=
    (poissonKernelDensity_continuous 2 σ hσ).mul continuous_cos
  have sym : ∀ θ, poissonKernelDensity 2 σ (2 * Real.pi - θ) * cos (2 * Real.pi - θ) =
             poissonKernelDensity 2 σ θ * cos θ := by
    intro θ; simp_rw [poissonKernelDensity_d2, Real.cos_two_pi_sub]
  have hfull := fullcircle_cos_d2 σ hσ
  have hfold := fold_sym_d2 _ sym hcont
  have h2pi : (2 * Real.pi) > 0 := by linarith [Real.pi_pos]
  have hfull' : ∫ θ in (0:ℝ)..2 * Real.pi,
      poissonKernelDensity 2 σ θ * cos θ = 2 * Real.pi * σ := by
    field_simp [h2pi.ne'] at hfull ⊢; linarith
  rw [hfold] at hfull'; linarith

private lemma halfcircle_norm_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ in (0:ℝ)..Real.pi, poissonKernelDensity 2 σ θ = Real.pi := by
  have sym : ∀ θ, poissonKernelDensity 2 σ (2 * Real.pi - θ) = poissonKernelDensity 2 σ θ := by
    intro θ; simp_rw [poissonKernelDensity_d2, Real.cos_two_pi_sub]
  have hfull := fullcircle_norm_d2 σ hσ
  have hfold := fold_sym_d2 _ sym (poissonKernelDensity_continuous 2 σ hσ)
  have h2pi : (2 * Real.pi) > 0 := by linarith [Real.pi_pos]
  have hfull' : ∫ θ in (0:ℝ)..2 * Real.pi, poissonKernelDensity 2 σ θ = 2 * Real.pi := by
    field_simp [h2pi.ne'] at hfull ⊢; linarith
  rw [hfold] at hfull'; linarith

/-! ### 1D FTC recurrences and d = 3 base case -/

private noncomputable abbrev poissonDenom (σ θ : ℝ) : ℝ :=
  1 + σ ^ 2 - 2 * σ * cos θ

private lemma hasDerivAt_poissonDenom (σ θ : ℝ) :
    HasDerivAt (poissonDenom σ) (2 * σ * sin θ) θ := by
  have h := (hasDerivAt_const θ (1 + σ ^ 2)).sub ((Real.hasDerivAt_cos θ).const_mul (2 * σ))
  convert h using 1
  ring

private lemma hasDerivAt_sin_pow_pred (d : ℕ) (hd : 2 ≤ d) (θ : ℝ) :
    HasDerivAt (fun x => sin x ^ (d - 1)) (((d : ℝ) - 1) * sin θ ^ (d - 2) * cos θ) θ := by
  have h := (Real.hasDerivAt_sin θ).pow (d - 1)
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  have hd2 : d - 1 - 1 = d - 2 := by omega
  change HasDerivAt (fun x => sin x ^ (d - 1)) _ θ at h
  rwa [hd1, hd2] at h

private lemma intervalIntegral_eq_zero_of_hasDerivAt {F f' : ℝ → ℝ}
    (hderiv : ∀ θ : ℝ, HasDerivAt F (f' θ) θ) (hf' : Continuous f')
    (hend : F Real.pi = F 0) :
    ∫ θ in (0 : ℝ)..Real.pi, f' θ = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
    (hf'.intervalIntegrable 0 Real.pi), hend, sub_self]

/-- Smooth antiderivative `F̃₀(θ) = (1 - σ²) sin^{d-1}θ · D(σ, θ)^{1 - d/2}` for the
    three-term moment relation connecting `I₂(d)`, `I₁(d)`, and `I₀(d)`. -/
private noncomputable def antiderivF0 (d : ℕ) (σ θ : ℝ) : ℝ :=
  (1 - σ ^ 2) * (sin θ ^ (d - 1) * poissonDenom σ θ ^ (1 - (d : ℝ) / 2))

private lemma hasDerivAt_antiderivF0 (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d)
    (θ : ℝ) :
    HasDerivAt (antiderivF0 d σ)
      (((d : ℝ) - 1) * (1 + σ ^ 2) * (poissonKernelDensity d σ θ * cos θ) -
        σ * (d : ℝ) * (poissonKernelDensity d σ θ * cos θ ^ 2) -
        ((d : ℝ) - 2) * σ * poissonKernelDensity d σ θ) θ := by
  have hD : 0 < poissonDenom σ θ := denom_pos σ θ hσ
  have h1 := hasDerivAt_sin_pow_pred d hd θ
  have h2 := (hasDerivAt_poissonDenom σ θ).rpow_const
    (p := 1 - (d : ℝ) / 2) (Or.inl hD.ne')
  have h := (h1.mul h2).const_mul (1 - σ ^ 2)
  unfold antiderivF0
  convert h using 1
  have hr1 : poissonDenom σ θ ^ (1 - (d : ℝ) / 2) =
      poissonDenom σ θ * (poissonDenom σ θ ^ ((d : ℝ) / 2))⁻¹ := by
    rw [Real.rpow_sub hD, Real.rpow_one, div_eq_mul_inv]
  have hr2 : poissonDenom σ θ ^ (1 - (d : ℝ) / 2 - 1) =
      (poissonDenom σ θ ^ ((d : ℝ) / 2))⁻¹ := by
    rw [show (1 : ℝ) - (d : ℝ) / 2 - 1 = -((d : ℝ) / 2) by ring, Real.rpow_neg hD.le]
  have hsin : sin θ ^ (d - 1) = sin θ ^ (d - 2) * sin θ := by
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
  rw [hr1, hr2, hsin]
  unfold poissonKernelDensity poissonDenom
  set P := (1 + σ ^ 2 - 2 * σ * cos θ) ^ ((d : ℝ) / 2)
  simp only [div_eq_mul_inv]
  linear_combination
    (1 - σ ^ 2) * sin θ ^ (d - 2) * ((d : ℝ) - 2) * σ * P⁻¹ * Real.sin_sq_add_cos_sq θ

private lemma halfcircle_three_term (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    σ * (d : ℝ) * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ ^ 2) =
    ((d : ℝ) - 1) * (1 + σ ^ 2) *
      (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ) -
    ((d : ℝ) - 2) * σ * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ) := by
  have hg := poissonKernelDensity_continuous d σ hσ
  have hi0 : IntervalIntegrable (poissonKernelDensity d σ) volume 0 Real.pi :=
    hg.intervalIntegrable 0 Real.pi
  have hi1 : IntervalIntegrable (fun θ => poissonKernelDensity d σ θ * cos θ) volume 0 Real.pi :=
    (hg.mul continuous_cos).intervalIntegrable 0 Real.pi
  have hi2 : IntervalIntegrable
      (fun θ => poissonKernelDensity d σ θ * cos θ ^ 2) volume 0 Real.pi :=
    (hg.mul (continuous_cos.pow 2)).intervalIntegrable 0 Real.pi
  have hcont : Continuous (fun θ =>
      ((d : ℝ) - 1) * (1 + σ ^ 2) * (poissonKernelDensity d σ θ * cos θ) -
        σ * (d : ℝ) * (poissonKernelDensity d σ θ * cos θ ^ 2) -
        ((d : ℝ) - 2) * σ * poissonKernelDensity d σ θ) :=
    ((continuous_const.mul (hg.mul continuous_cos)).sub
      (continuous_const.mul (hg.mul (continuous_cos.pow 2)))).sub
      (continuous_const.mul hg)
  have hend : antiderivF0 d σ Real.pi = antiderivF0 d σ 0 := by
    simp [antiderivF0, Real.sin_pi, Real.sin_zero, zero_pow (by omega : d - 1 ≠ 0)]
  have hftc := intervalIntegral_eq_zero_of_hasDerivAt
    (hasDerivAt_antiderivF0 d σ hσ hd) hcont hend
  rw [intervalIntegral.integral_sub
        ((hi1.const_mul _).sub (hi2.const_mul _)) (hi0.const_mul _),
      intervalIntegral.integral_sub (hi1.const_mul _) (hi2.const_mul _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hftc
  linarith

/-- Smooth antiderivative `G̃₀(θ) = (1 - σ²) sin^{d-1}θ · D(σ, θ)^{-d/2}` relating
    `I₀(d + 2)` to `I₁(d)`. -/
private noncomputable def antiderivG0 (d : ℕ) (σ θ : ℝ) : ℝ :=
  (1 - σ ^ 2) * (sin θ ^ (d - 1) * poissonDenom σ θ ^ (-(d : ℝ) / 2))

private lemma hasDerivAt_antiderivG0 (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d)
    (θ : ℝ) :
    HasDerivAt (antiderivG0 d σ)
      (((d : ℝ) - 1) * (poissonKernelDensity d σ θ * cos θ) -
        (d : ℝ) * σ * poissonKernelDensity (d + 2) σ θ) θ := by
  have hD : 0 < poissonDenom σ θ := denom_pos σ θ hσ
  have h1 := hasDerivAt_sin_pow_pred d hd θ
  have h2 := (hasDerivAt_poissonDenom σ θ).rpow_const
    (p := -(d : ℝ) / 2) (Or.inl hD.ne')
  have h := (h1.mul h2).const_mul (1 - σ ^ 2)
  unfold antiderivG0
  convert h using 1
  have hr1 : poissonDenom σ θ ^ (-(d : ℝ) / 2) =
      (poissonDenom σ θ ^ ((d : ℝ) / 2))⁻¹ := by
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hD.le]
  have hr2 : poissonDenom σ θ ^ (-(d : ℝ) / 2 - 1) =
      (poissonDenom σ θ ^ (((d + 2 : ℕ) : ℝ) / 2))⁻¹ := by
    have hexp : -(d : ℝ) / 2 - 1 = -(((d + 2 : ℕ) : ℝ) / 2) := by push_cast; ring
    rw [hexp, Real.rpow_neg hD.le]
  have hsin : sin θ ^ ((d + 2) - 2) = sin θ ^ (d - 1) * sin θ := by
    rw [show (d + 2) - 2 = (d - 1) + 1 by omega, pow_succ]
  rw [hr1, hr2]
  unfold poissonKernelDensity poissonDenom at *
  rw [hsin]
  simp only [div_eq_mul_inv]
  ring

private lemma halfcircle_step_norm (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    (d : ℝ) * σ * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ) =
    ((d : ℝ) - 1) * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ) := by
  have hg := poissonKernelDensity_continuous d σ hσ
  have hg2 := poissonKernelDensity_continuous (d + 2) σ hσ
  have hi1 : IntervalIntegrable (fun θ => poissonKernelDensity d σ θ * cos θ) volume 0 Real.pi :=
    (hg.mul continuous_cos).intervalIntegrable 0 Real.pi
  have hi0_next : IntervalIntegrable (poissonKernelDensity (d + 2) σ) volume 0 Real.pi :=
    hg2.intervalIntegrable 0 Real.pi
  have hcont : Continuous (fun θ =>
      ((d : ℝ) - 1) * (poissonKernelDensity d σ θ * cos θ) -
        (d : ℝ) * σ * poissonKernelDensity (d + 2) σ θ) :=
    (continuous_const.mul (hg.mul continuous_cos)).sub (continuous_const.mul hg2)
  have hend : antiderivG0 d σ Real.pi = antiderivG0 d σ 0 := by
    simp [antiderivG0, Real.sin_pi, Real.sin_zero, zero_pow (by omega : d - 1 ≠ 0)]
  have hftc := intervalIntegral_eq_zero_of_hasDerivAt
    (hasDerivAt_antiderivG0 d σ hσ hd) hcont hend
  rw [intervalIntegral.integral_sub (hi1.const_mul _) (hi0_next.const_mul _),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hftc
  linarith

/-- Smooth antiderivative `G̃₁(θ) = cos θ · G̃₀(θ)` relating `I₁(d + 2)` to `I₂(d)` and `I₀(d)`. -/
private noncomputable def antiderivG1 (d : ℕ) (σ θ : ℝ) : ℝ :=
  cos θ * antiderivG0 d σ θ

private lemma hasDerivAt_antiderivG1 (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d)
    (θ : ℝ) :
    HasDerivAt (antiderivG1 d σ)
      ((d : ℝ) * (poissonKernelDensity d σ θ * cos θ ^ 2) -
        poissonKernelDensity d σ θ -
        (d : ℝ) * σ * (poissonKernelDensity (d + 2) σ θ * cos θ)) θ := by
  have hD : 0 < poissonDenom σ θ := denom_pos σ θ hσ
  have h := (Real.hasDerivAt_cos θ).mul (hasDerivAt_antiderivG0 d σ hσ hd θ)
  unfold antiderivG1
  convert h using 1
  unfold antiderivG0
  have hr1 : poissonDenom σ θ ^ (-(d : ℝ) / 2) =
      (poissonDenom σ θ ^ ((d : ℝ) / 2))⁻¹ := by
    rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hD.le]
  have hsin : sin θ ^ (d - 1) = sin θ ^ (d - 2) * sin θ := by
    rw [show d - 1 = (d - 2) + 1 by omega, pow_succ]
  rw [hr1, hsin]
  have hg_eq : (1 - σ ^ 2) * (sin θ ^ (d - 2) * sin θ * (poissonDenom σ θ ^ ((d : ℝ) / 2))⁻¹) =
      poissonKernelDensity d σ θ * sin θ := by
    unfold poissonKernelDensity poissonDenom
    simp only [div_eq_mul_inv]
    ring
  rw [hg_eq]
  linear_combination poissonKernelDensity d σ θ * Real.sin_sq_add_cos_sq θ

private lemma halfcircle_step_cos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    (d : ℝ) * σ * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ * cos θ) =
    (d : ℝ) * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ ^ 2) -
      (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ) := by
  have hg := poissonKernelDensity_continuous d σ hσ
  have hg2 := poissonKernelDensity_continuous (d + 2) σ hσ
  have hi0 : IntervalIntegrable (poissonKernelDensity d σ) volume 0 Real.pi :=
    hg.intervalIntegrable 0 Real.pi
  have hi2 : IntervalIntegrable
      (fun θ => poissonKernelDensity d σ θ * cos θ ^ 2) volume 0 Real.pi :=
    (hg.mul (continuous_cos.pow 2)).intervalIntegrable 0 Real.pi
  have hi1_next : IntervalIntegrable
      (fun θ => poissonKernelDensity (d + 2) σ θ * cos θ) volume 0 Real.pi :=
    (hg2.mul continuous_cos).intervalIntegrable 0 Real.pi
  have hcont : Continuous (fun θ =>
      (d : ℝ) * (poissonKernelDensity d σ θ * cos θ ^ 2) -
        poissonKernelDensity d σ θ -
        (d : ℝ) * σ * (poissonKernelDensity (d + 2) σ θ * cos θ)) :=
    ((continuous_const.mul (hg.mul (continuous_cos.pow 2))).sub hg).sub
      (continuous_const.mul (hg2.mul continuous_cos))
  have hend : antiderivG1 d σ Real.pi = antiderivG1 d σ 0 := by
    simp [antiderivG1, antiderivG0, Real.sin_pi, Real.sin_zero, zero_pow (by omega : d - 1 ≠ 0)]
  have hftc := intervalIntegral_eq_zero_of_hasDerivAt
    (hasDerivAt_antiderivG1 d σ hσ hd) hcont hend
  rw [intervalIntegral.integral_sub
        ((hi2.const_mul _).sub hi0) (hi1_next.const_mul _),
      intervalIntegral.integral_sub (hi2.const_mul _) hi0,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hftc
  linarith

private lemma halfcircle_cos_step (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d)
    (ih : ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ =
          σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ) :
    ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ * cos θ =
    σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ := by
  have h3 := halfcircle_three_term d σ hσ hd
  have hG0 := halfcircle_step_norm d σ hσ hd
  have hG1 := halfcircle_step_cos d σ hσ hd
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdσ_ne : (d : ℝ) * σ ≠ 0 := mul_ne_zero hd_pos.ne' hσ.1.ne'
  rw [ih] at h3 hG0
  have hI2 : (d : ℝ) * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ ^ 2) =
      (((d : ℝ) - 1) * σ ^ 2 + 1) * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ) := by
    apply mul_left_cancel₀ hσ.1.ne'
    linear_combination h3
  have hkey : (d : ℝ) * σ *
      (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ * cos θ) =
      (d : ℝ) * σ *
      (σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ) := by
    linear_combination hG1 + hI2 - σ * hG0
  exact mul_left_cancel₀ hdσ_ne hkey

/-- Smooth antiderivative `H̃₃(θ)` for the `d = 3` base case `I₁(3) = σ I₀(3)`. -/
private noncomputable def antiderivH3 (σ θ : ℝ) : ℝ :=
  (-(1 - σ ^ 2) / (2 * σ ^ 2)) *
    ((1 - σ ^ 2) * poissonDenom σ θ ^ (-(1 : ℝ) / 2) +
      poissonDenom σ θ ^ ((1 : ℝ) / 2))

private lemma hasDerivAt_antiderivH3 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (θ : ℝ) :
    HasDerivAt (antiderivH3 σ)
      (poissonKernelDensity 3 σ θ * cos θ - σ * poissonKernelDensity 3 σ θ) θ := by
  have hD : 0 < poissonDenom σ θ := denom_pos σ θ hσ
  have hm := ((hasDerivAt_poissonDenom σ θ).rpow_const
    (p := -(1 : ℝ) / 2) (Or.inl hD.ne')).const_mul (1 - σ ^ 2)
  have hp := (hasDerivAt_poissonDenom σ θ).rpow_const
    (p := (1 : ℝ) / 2) (Or.inl hD.ne')
  have h := (hm.add hp).const_mul (-(1 - σ ^ 2) / (2 * σ ^ 2))
  unfold antiderivH3
  convert h using 1
  have hr1 : poissonDenom σ θ ^ (-(1 : ℝ) / 2 - 1) =
      (poissonDenom σ θ ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [show -(1 : ℝ) / 2 - 1 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hD.le]
  have hr2 : poissonDenom σ θ ^ ((1 : ℝ) / 2 - 1) =
      poissonDenom σ θ / poissonDenom σ θ ^ ((3 : ℝ) / 2) := by
    rw [show (1 : ℝ) / 2 - 1 = 1 - (3 : ℝ) / 2 by ring, Real.rpow_sub hD, Real.rpow_one]
  rw [hr1, hr2]
  unfold poissonKernelDensity poissonDenom
  have hDp_ne : (1 + σ ^ 2 - 2 * σ * cos θ) ^ ((3 : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hD _).ne'
  have hσ_ne : σ ≠ 0 := hσ.1.ne'
  norm_num
  field_simp [hDp_ne, hσ_ne]
  ring

private lemma sq_rpow_half_of_pos {a : ℝ} (ha : 0 < a) :
    (a ^ 2) ^ ((1 : ℝ) / 2) = a := by
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
  norm_num

private lemma sq_rpow_neg_half_of_pos {a : ℝ} (ha : 0 < a) :
    (a ^ 2) ^ (-(1 : ℝ) / 2) = a⁻¹ := by
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
  norm_num
  exact Real.rpow_neg_one a

private lemma antiderivH3_endpoints (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    antiderivH3 σ Real.pi = antiderivH3 σ 0 := by
  unfold antiderivH3 poissonDenom
  have h1m : 0 < 1 - σ := by linarith [hσ.2]
  have h1p : 0 < 1 + σ := by linarith [hσ.1]
  have hD0 : 1 + σ ^ 2 - 2 * σ * cos 0 = (1 - σ) ^ 2 := by
    rw [Real.cos_zero]; ring
  have hDpi : 1 + σ ^ 2 - 2 * σ * cos Real.pi = (1 + σ) ^ 2 := by
    rw [Real.cos_pi]; ring
  rw [hD0, hDpi, sq_rpow_half_of_pos h1m, sq_rpow_neg_half_of_pos h1m,
      sq_rpow_half_of_pos h1p, sq_rpow_neg_half_of_pos h1p]
  congr 1
  field_simp [h1m.ne', h1p.ne']
  ring

private lemma halfcircle_cos_d3 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity 3 σ θ * cos θ =
    σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity 3 σ θ := by
  have hg := poissonKernelDensity_continuous 3 σ hσ
  have hi0 : IntervalIntegrable (poissonKernelDensity 3 σ) volume 0 Real.pi :=
    hg.intervalIntegrable 0 Real.pi
  have hi1 : IntervalIntegrable (fun θ => poissonKernelDensity 3 σ θ * cos θ) volume 0 Real.pi :=
    (hg.mul continuous_cos).intervalIntegrable 0 Real.pi
  have hcont : Continuous
      (fun θ => poissonKernelDensity 3 σ θ * cos θ - σ * poissonKernelDensity 3 σ θ) :=
    (hg.mul continuous_cos).sub (continuous_const.mul hg)
  have hftc := intervalIntegral_eq_zero_of_hasDerivAt
    (hasDerivAt_antiderivH3 σ hσ) hcont (antiderivH3_endpoints σ hσ)
  rw [intervalIntegral.integral_sub hi1 (hi0.const_mul _),
      intervalIntegral.integral_const_mul] at hftc
  linarith

/-! ## All-dimension first and second moment identities -/

/-- Unnormalized first moment identity `I₁(d) = σ · I₀(d)` for all `d ≥ 2`, proved by
    two-step induction from `d = 2` (complex Poisson) and `d = 3` (`antiderivH3`). -/
lemma halfcircle_cos_eq (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ =
    σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ := by
  match d with
  | 0 | 1 => omega
  | 2 =>
    rw [halfcircle_cos_d2 σ hσ, halfcircle_norm_d2 σ hσ]
    ring
  | 3 =>
    exact halfcircle_cos_d3 σ hσ
  | d + 4 =>
    have ih := halfcircle_cos_eq (d + 2) σ hσ (by omega)
    exact halfcircle_cos_step (d + 2) σ hσ (by omega) ih

/-- The mean of `cos θ` under the Poisson marginal equals `σ` for all `d ≥ 2`.
    `σ = E[cos θ]` represents the average amplitude overlap between the perturbed
    and ideal state. -/
theorem poissonMarginal_mean_cos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ, cos θ ∂(poissonMarginal d σ) = σ := by
  have hnc_ne : poissonNormConst d σ ≠ 0 := (poissonNormConst_pos d σ hσ hd).ne'
  rw [integral_poissonMarginal_eq d σ hσ hd continuous_cos,
      halfcircle_cos_eq d σ hσ hd, ← poissonNormConst_eq_intervalIntegral]
  exact mul_div_cancel_right₀ σ hnc_ne

/-- Specialization of `poissonMarginal_mean_cos` to `d = 2` (retained for backwards
    compatibility). -/
theorem poissonMarginal_mean_cos_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ, cos θ ∂(poissonMarginal 2 σ) = σ :=
  poissonMarginal_mean_cos 2 σ hσ (by norm_num)

/-- Unnormalized second moment identity `I₂(d) = ((d - 1) σ² + 1) / d · I₀(d)` for all `d ≥ 2`,
    deduced directly from the three-term FTC identity `halfcircle_three_term` and
    `halfcircle_cos_eq`. -/
theorem halfcircle_cos_sq_eq (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ ^ 2 =
    ((d - 1 : ℝ) * σ ^ 2 + 1) / d * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ := by
  have h3 := halfcircle_three_term d σ hσ hd
  rw [halfcircle_cos_eq d σ hσ hd] at h3
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hσ_ne : σ ≠ 0 := hσ.1.ne'
  apply mul_left_cancel₀ (mul_ne_zero hσ_ne hd_ne)
  calc
    σ * (d : ℝ) * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ ^ 2
      = ((d : ℝ) - 1) * (1 + σ ^ 2) *
          (σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ) -
        ((d : ℝ) - 2) * σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ := h3
    _ = σ * (d : ℝ) * (((d - 1 : ℝ) * σ ^ 2 + 1) / d *
          ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ) := by
        field_simp [hd_ne]
        ring

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
  simp [isotropicError, Real.cos_zero, Real.sin_zero]

-- isotropicError with θ=π/2 returns e₂ (only the sin term survives)
example (Φ e₂ : E n) : isotropicError Φ e₂ (Real.pi / 2) = e₂ := by
  simp [isotropicError, Real.cos_pi_div_two, Real.sin_pi_div_two]

/--
info: 'IsotropicGrover.poissonMarginal_mean_cos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms poissonMarginal_mean_cos

/--
info: 'IsotropicGrover.halfcircle_cos_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms halfcircle_cos_sq_eq

end IsotropicGrover
