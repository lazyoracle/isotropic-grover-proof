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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import IsotropicGroverProof.Defs

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
  rw [← ofReal_integral_eq_lintegral_ofReal hintbl hnonneg, MeasureTheory.integral_div,
    show (∫ θ, poissonKernelDensity d σ θ ∂volume.restrict (Icc 0 Real.pi)) =
        poissonNormConst d σ from rfl,
    div_self hc.ne', ENNReal.ofReal_one]

/-! ## Key moment property -/

/-! ### d=2 helpers: complex Poisson formula yields ∫ pKD2*cos = π*σ -/

private lemma poissonKernelDensity_d2 (σ θ : ℝ) : poissonKernelDensity 2 σ θ =
    (1 - σ ^ 2) / (1 + σ ^ 2 - 2 * σ * cos θ) := by
  unfold poissonKernelDensity; norm_num

private lemma poissonKernelDensity_d2_pos (σ θ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    0 < poissonKernelDensity 2 σ θ := by
  rw [poissonKernelDensity_d2]
  apply div_pos
  · nlinarith [hσ.1, hσ.2, mul_pos hσ.1 hσ.1]
  · exact denom_pos σ θ hσ

private lemma poissonKernelDensity_d2_cont (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    Continuous (poissonKernelDensity 2 σ) := by
  have : poissonKernelDensity 2 σ = fun θ => (1 - σ ^ 2) / (1 + σ ^ 2 - 2 * σ * cos θ) := by
    funext θ; exact poissonKernelDensity_d2 σ θ
  rw [this]
  apply Continuous.div continuous_const
  · exact (continuous_const.add continuous_const).sub (continuous_const.mul continuous_cos)
  · intro θ; exact (denom_pos σ θ hσ).ne'

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
  rw [show (∫ (θ : ℝ) in (0:ℝ)..2 * Real.pi, (poissonKernel (0:ℂ) (↑σ) • f) (circleMap 0 1 θ)).re
    = ∫ (θ : ℝ) in (0:ℝ)..2 * Real.pi, ((poissonKernel (0:ℂ) (↑σ) • f) (circleMap 0 1 θ)).re from by
    convert ((RCLike.reCLM (K := ℂ)).intervalIntegral_comp_comm hf_intbl).symm using 1] at key
  linarith

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

private lemma Icc_to_interval_d2 (f : ℝ → ℝ) :
    ∫ θ in Set.Icc (0:ℝ) Real.pi, f θ = ∫ θ in (0:ℝ)..Real.pi, f θ := by
  rw [intervalIntegral.integral_of_le Real.pi_pos.le,
    ← integral_Icc_eq_integral_Ioc' (f := f) Real.volume_singleton]

private lemma halfcircle_cos_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ in (0:ℝ)..Real.pi, poissonKernelDensity 2 σ θ * cos θ = Real.pi * σ := by
  have hcont : Continuous (fun θ => poissonKernelDensity 2 σ θ * cos θ) :=
    (poissonKernelDensity_d2_cont σ hσ).mul continuous_cos
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
  have hfold := fold_sym_d2 _ sym (poissonKernelDensity_d2_cont σ hσ)
  have h2pi : (2 * Real.pi) > 0 := by linarith [Real.pi_pos]
  have hfull' : ∫ θ in (0:ℝ)..2 * Real.pi, poissonKernelDensity 2 σ θ = 2 * Real.pi := by
    field_simp [h2pi.ne'] at hfull ⊢; linarith
  rw [hfold] at hfull'; linarith

private lemma poissonNormConst_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    poissonNormConst 2 σ = Real.pi := by
  unfold poissonNormConst; rw [Icc_to_interval_d2]; exact halfcircle_norm_d2 σ hσ

/-- The mean of cos θ under the Poisson marginal equals σ.
    σ = E[cos θ] = average amplitude overlap between perturbed and ideal state.
    Proof for d=2: the complex Poisson integral formula applied to f(z)=z gives
    (2π)⁻¹ ∫₀^{2π} pK(σ,e^{iθ}) e^{iθ} dθ = σ; taking real parts and folding by symmetry
    yields ∫₀^π pKDens2(σ,θ) cos θ dθ = π σ, which divided by the normalization constant π gives σ.
    For d≥3: sorry (same depth as poissonIntegral_cos_sq). -/
theorem poissonMarginal_mean_cos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ, cos θ ∂(poissonMarginal d σ) = σ := by
  -- d=2 case: full proof via complex Poisson formula
  by_cases hd2 : d = 2
  · subst hd2
    unfold poissonMarginal
    have hnc : poissonNormConst 2 σ = Real.pi := poissonNormConst_d2 σ hσ
    have hnc_pos : 0 < poissonNormConst 2 σ := by rw [hnc]; exact Real.pi_pos
    have h_meas : Measurable (fun θ =>
        ENNReal.ofReal (poissonKernelDensity 2 σ θ / poissonNormConst 2 σ)) :=
      ((poissonKernelDensity_d2_cont σ hσ).measurable.div_const _).ennreal_ofReal
    have h_lt_top : ∀ᵐ θ ∂MeasureTheory.volume.restrict (Set.Icc 0 Real.pi),
        ENNReal.ofReal (poissonKernelDensity 2 σ θ / poissonNormConst 2 σ) < ⊤ :=
      ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
    rw [integral_withDensity_eq_integral_toReal_smul h_meas h_lt_top]
    have hnn_ae : ∀ᵐ θ ∂MeasureTheory.volume.restrict (Set.Icc 0 Real.pi),
        0 ≤ poissonKernelDensity 2 σ θ / poissonNormConst 2 σ := by
      rw [ae_restrict_iff' measurableSet_Icc]
      exact ae_of_all _ (fun θ _ => div_nonneg (poissonKernelDensity_d2_pos σ θ hσ).le hnc_pos.le)
    have step1 : ∫ θ,
          (ENNReal.ofReal (poissonKernelDensity 2 σ θ /
            poissonNormConst 2 σ)).toReal • cos θ
          ∂MeasureTheory.volume.restrict (Set.Icc 0 Real.pi) =
        ∫ θ in Set.Icc 0 Real.pi, poissonKernelDensity 2 σ θ / poissonNormConst 2 σ * cos θ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hnn_ae] with θ hθ
      rw [ENNReal.toReal_ofReal hθ, smul_eq_mul]
    rw [step1]
    simp_rw [div_mul_eq_mul_div]
    rw [MeasureTheory.integral_div, Icc_to_interval_d2, halfcircle_cos_d2 σ hσ, hnc]
    field_simp [Real.pi_pos.ne']
  -- d≥3 case: sorry (same depth as poissonIntegral_cos_sq)
  · sorry

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

end IsotropicGrover
