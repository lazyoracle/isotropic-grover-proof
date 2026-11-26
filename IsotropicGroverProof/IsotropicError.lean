-- IsotropicGroverProof/IsotropicError.lean
-- Single-gate isotropic pure-state error model: Poisson kernel marginal density g(θ; σ),
-- closed-interval angle measure poissonAngleMeasure on σ ∈ [0, 1], 1D FTC moment recurrences
-- proving E[cos θ] = σ and E[cos² θ] = ((d - 1)σ² + 1) / d for all d ≥ 2, and the perturbed
-- unit state isotropicError Φ e₂ θ = cos θ • Φ + sin θ • e₂.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import IsotropicGroverProof.Defs

/-!
# Isotropic Error Model

Poisson kernel marginal density `g(θ; σ)`, closed-interval angle measure `poissonAngleMeasure`
on `σ ∈ [0, 1]`, the error state `Ψ = cos θ · Φ + sin θ · e₂`, and all-dimension first and
second moment identities (`E[cos θ] = σ` and `E[cos² θ] = ((d - 1) σ² + 1) / d`) for `d ≥ 2`.
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

/-! ## Normalization and marginal integral helpers -/

private lemma denom_pos (σ θ : ℝ) (hσ : σ ∈ Set.Ico 0 1) :
    0 < 1 + σ ^ 2 - 2 * σ * cos θ := by
  have h1s : 0 < 1 - σ := sub_pos.mpr hσ.2
  have h1c : 0 ≤ 1 - cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
  nlinarith [sq_pos_of_pos h1s, mul_nonneg hσ.1 h1c]

private lemma one_sub_sq_pos (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) : 0 < 1 - σ ^ 2 := by
  have : 1 - σ ^ 2 = (1 - σ) * (1 + σ) := by ring
  rw [this]
  exact mul_pos (by linarith [hσ.2]) (by linarith [hσ.1])

private lemma poissonKernelDensity_nonneg (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi) (_hd : 2 ≤ d) :
    0 ≤ poissonKernelDensity d σ θ := by
  simp only [poissonKernelDensity]
  apply div_nonneg
  · exact mul_nonneg (one_sub_sq_pos σ hσ).le (pow_nonneg (Real.sin_nonneg_of_mem_Icc hθ) _)
  · exact Real.rpow_nonneg (denom_pos σ θ hσ).le _

private lemma poissonKernelDensity_continuous (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) :
    Continuous (poissonKernelDensity d σ) := by
  unfold poissonKernelDensity
  apply Continuous.div
  · exact continuous_const.mul (Real.continuous_sin.pow _)
  · apply Continuous.rpow_const
    · exact (continuous_const.add continuous_const).sub
        (continuous_const.mul Real.continuous_cos)
    · intro θ; left; exact (denom_pos σ θ hσ).ne'
  · intro θ; exact (Real.rpow_pos_of_pos (denom_pos σ θ hσ) _).ne'

/-- Set integral over `[0, π]` equals the interval integral `0..π`. -/
lemma Icc_to_interval (f : ℝ → ℝ) :
    ∫ θ in Set.Icc (0 : ℝ) Real.pi, f θ = ∫ θ in (0 : ℝ)..Real.pi, f θ := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]

/-- `poissonNormConst d σ` expressed as an `intervalIntegral` over `0..π`. -/
lemma poissonNormConst_eq_intervalIntegral (d : ℕ) (σ : ℝ) :
    poissonNormConst d σ = ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ :=
  Icc_to_interval _

/-- The normalization constant of the Poisson kernel marginal is strictly positive
    for `σ ∈ [0, 1)` and `d ≥ 2`. -/
lemma poissonNormConst_pos_Ico (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1)
    (hd : 2 ≤ d) : 0 < poissonNormConst d σ := by
  rw [poissonNormConst_eq_intervalIntegral]
  have hf_nonneg : ∀ θ ∈ Set.Ioc 0 Real.pi, 0 ≤ poissonKernelDensity d σ θ :=
    fun θ hθ => poissonKernelDensity_nonneg d σ hσ θ (Set.Ioc_subset_Icc_self hθ) hd
  have hpi2_mem : Real.pi / 2 ∈ Set.Icc 0 Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hf_pos_pi2 : 0 < poissonKernelDensity d σ (Real.pi / 2) := by
    simp only [poissonKernelDensity, Real.sin_pi_div_two, Real.cos_pi_div_two, one_pow]
    apply div_pos
    · exact mul_pos (one_sub_sq_pos σ hσ) one_pos
    · apply Real.rpow_pos_of_pos
      simp only [mul_zero, sub_zero]
      linarith [sq_nonneg σ]
  exact intervalIntegral.integral_pos Real.pi_pos
    (poissonKernelDensity_continuous d σ hσ).continuousOn hf_nonneg
    ⟨Real.pi / 2, hpi2_mem, hf_pos_pi2⟩

/-- The normalization constant of the Poisson kernel marginal is strictly positive
    for `σ ∈ (0, 1)` and `d ≥ 2`. -/
lemma poissonNormConst_pos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hd : 2 ≤ d) : 0 < poissonNormConst d σ :=
  poissonNormConst_pos_Ico d σ (Set.Ioo_subset_Ico_self hσ) hd

/-- Generic reduction of expectations under `poissonMarginal d σ` for `σ ∈ [0, 1)` to an
    `intervalIntegral` over `0..π` divided by `poissonNormConst d σ`. -/
lemma integral_poissonMarginal_eq_Ico (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d)
    (f : ℝ → ℝ) :
    ∫ θ, f θ ∂(poissonMarginal d σ) =
    (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * f θ) / poissonNormConst d σ := by
  unfold poissonMarginal
  have hnc := poissonNormConst_pos_Ico d σ hσ hd
  have h_meas : Measurable (fun θ =>
      ENNReal.ofReal (poissonKernelDensity d σ θ / poissonNormConst d σ)) :=
    ((poissonKernelDensity_continuous d σ hσ).measurable.div_const _).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul h_meas
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
      ← Icc_to_interval, ← MeasureTheory.integral_div]
  refine integral_congr_ae
    ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun θ hθ => ?_))
  dsimp only
  rw [ENNReal.toReal_ofReal
    (div_nonneg (poissonKernelDensity_nonneg d σ hσ θ hθ hd) hnc.le),
    smul_eq_mul, div_mul_eq_mul_div]

/-- Generic reduction of expectations under `poissonMarginal d σ` to an `intervalIntegral`
    over `0..π` divided by `poissonNormConst d σ`. -/
lemma integral_poissonMarginal_eq (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d)
    (f : ℝ → ℝ) :
    ∫ θ, f θ ∂(poissonMarginal d σ) =
    (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * f θ) / poissonNormConst d σ :=
  integral_poissonMarginal_eq_Ico d σ (Set.Ioo_subset_Ico_self hσ) hd f

/-! ## Probability measure instance -/

/-- The Poisson marginal is a probability measure when `σ ∈ [0, 1)` and `d ≥ 2`. -/
theorem poissonMarginal_isProbMeasure_Ico (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1)
    (hd : 2 ≤ d) : IsProbabilityMeasure (poissonMarginal d σ) := by
  rw [isProbabilityMeasure_iff]
  simp only [poissonMarginal, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hc := poissonNormConst_pos_Ico d σ hσ hd
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc 0 Real.pi)]
      (fun θ => poissonKernelDensity d σ θ / poissonNormConst d σ) :=
    (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun θ hθ =>
      div_nonneg (poissonKernelDensity_nonneg d σ hσ θ hθ hd) hc.le)
  have hintbl : Integrable (fun θ => poissonKernelDensity d σ θ / poissonNormConst d σ)
      (volume.restrict (Icc 0 Real.pi)) :=
    ((poissonKernelDensity_continuous d σ hσ).continuousOn.div_const _).integrableOn_Icc.integrable
  rw [← ofReal_integral_eq_lintegral_ofReal hintbl hnonneg, MeasureTheory.integral_div,
    show (∫ θ, poissonKernelDensity d σ θ ∂volume.restrict (Icc 0 Real.pi)) =
        poissonNormConst d σ from rfl,
    div_self hc.ne', ENNReal.ofReal_one]

/-- The Poisson marginal is a probability measure when σ ∈ (0,1). -/
theorem poissonMarginal_isProbMeasure (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hd : 2 ≤ d) : IsProbabilityMeasure (poissonMarginal d σ) :=
  poissonMarginal_isProbMeasure_Ico d σ (Set.Ioo_subset_Ico_self hσ) hd

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
    (poissonKernelDensity_continuous 2 σ (Set.Ioo_subset_Ico_self hσ)).mul continuous_cos
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
  have hfold := fold_sym_d2 _ sym (poissonKernelDensity_continuous 2 σ (Set.Ioo_subset_Ico_self hσ))
  have h2pi : (2 * Real.pi) > 0 := by linarith [Real.pi_pos]
  have hfull' : ∫ θ in (0:ℝ)..2 * Real.pi, poissonKernelDensity 2 σ θ = 2 * Real.pi := by
    field_simp [h2pi.ne'] at hfull ⊢; linarith
  rw [hfold] at hfull'; linarith

/-! ### 1D FTC recurrences and d = 3 base case -/

private noncomputable abbrev poissonDenom (σ θ : ℝ) : ℝ :=
  1 + σ ^ 2 - 2 * σ * cos θ

private lemma poissonKernelDensity_eq_mul_rpow_neg (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1)
    (θ : ℝ) :
    poissonKernelDensity d σ θ =
      (1 - σ ^ 2) * sin θ ^ (d - 2) * poissonDenom σ θ ^ (-(d : ℝ) / 2) := by
  unfold poissonKernelDensity poissonDenom
  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg (denom_pos σ θ hσ).le,
      div_eq_mul_inv]

private lemma poissonKernelDensity_add_two_mul_denom (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1)
    (hd : 2 ≤ d) (θ : ℝ) :
    poissonKernelDensity (d + 2) σ θ * poissonDenom σ θ =
      poissonKernelDensity d σ θ * sin θ ^ 2 := by
  have hD : poissonDenom σ θ ≠ 0 := (denom_pos σ θ hσ).ne'
  rw [poissonKernelDensity_eq_mul_rpow_neg (d + 2) σ hσ θ,
      poissonKernelDensity_eq_mul_rpow_neg d σ hσ θ,
      show -((d + 2 : ℕ) : ℝ) / 2 = -(d : ℝ) / 2 - 1 by push_cast; ring,
      Real.rpow_sub_one hD, mul_assoc, div_mul_cancel₀ _ hD,
      show (d + 2) - 2 = (d - 2) + 2 by omega, pow_add]
  ring

private lemma hasDerivAt_poissonDenom (σ θ : ℝ) :
    HasDerivAt (poissonDenom σ) (2 * σ * sin θ) θ := by
  convert (hasDerivAt_const θ (1 + σ ^ 2)).sub
    ((Real.hasDerivAt_cos θ).const_mul (2 * σ)) using 1
  ring

private lemma hasDerivAt_poissonDenom_rpow (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (p θ : ℝ) :
    HasDerivAt (fun x => poissonDenom σ x ^ p)
      (2 * σ * sin θ * p * poissonDenom σ θ ^ (p - 1)) θ :=
  (hasDerivAt_poissonDenom σ θ).rpow_const (p := p) (Or.inl (denom_pos σ θ hσ).ne')

private lemma hasDerivAt_sin_pow_pred (d : ℕ) (hd : 2 ≤ d) (θ : ℝ) :
    HasDerivAt (fun x => sin x ^ (d - 1)) (((d : ℝ) - 1) * sin θ ^ (d - 2) * cos θ) θ := by
  convert (Real.hasDerivAt_sin θ).pow (d - 1) using 1
  rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one, show d - 1 - 1 = d - 2 by omega]

private lemma intervalIntegral_eq_of_hasDerivAt_sub {F u v : ℝ → ℝ}
    (hderiv : ∀ θ : ℝ, HasDerivAt F (u θ - v θ) θ) (hu : Continuous u) (hv : Continuous v)
    (hend : F Real.pi = F 0) :
    ∫ θ in (0 : ℝ)..Real.pi, u θ = ∫ θ in (0 : ℝ)..Real.pi, v θ := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
    ((hu.sub hv).intervalIntegrable 0 Real.pi)
  rw [hend, sub_self, intervalIntegral.integral_sub
    (hu.intervalIntegrable 0 Real.pi) (hv.intervalIntegrable 0 Real.pi)] at h
  linarith

private lemma intervalIntegral_eq_of_hasDerivAt_sub_sub {F u₁ u₂ v : ℝ → ℝ}
    (hderiv : ∀ θ : ℝ, HasDerivAt F (u₁ θ - u₂ θ - v θ) θ)
    (hu₁ : Continuous u₁) (hu₂ : Continuous u₂) (hv : Continuous v)
    (hend : F Real.pi = F 0) :
    (∫ θ in (0 : ℝ)..Real.pi, u₁ θ) - (∫ θ in (0 : ℝ)..Real.pi, u₂ θ) =
      ∫ θ in (0 : ℝ)..Real.pi, v θ := by
  rw [← intervalIntegral.integral_sub
    (hu₁.intervalIntegrable 0 Real.pi) (hu₂.intervalIntegrable 0 Real.pi)]
  exact intervalIntegral_eq_of_hasDerivAt_sub hderiv (hu₁.sub hu₂) hv hend

/-- Smooth antiderivative `G̃₀(θ) = (1 - σ²) sin^{d-1}θ · D(σ, θ)^{-d/2}` relating
    `I₀(d + 2)` to `I₁(d)`. -/
private noncomputable def antiderivG0 (d : ℕ) (σ θ : ℝ) : ℝ :=
  (1 - σ ^ 2) * (sin θ ^ (d - 1) * poissonDenom σ θ ^ (-(d : ℝ) / 2))

private lemma antiderivG0_eq (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d) (θ : ℝ) :
    antiderivG0 d σ θ = poissonKernelDensity d σ θ * sin θ := by
  rw [antiderivG0, poissonKernelDensity_eq_mul_rpow_neg d σ hσ θ,
      show d - 1 = (d - 2) + 1 by omega, pow_succ]
  ring

private lemma hasDerivAt_antiderivG0 (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d)
    (θ : ℝ) :
    HasDerivAt (antiderivG0 d σ)
      (((d : ℝ) - 1) * (poissonKernelDensity d σ θ * cos θ) -
        (d : ℝ) * σ * poissonKernelDensity (d + 2) σ θ) θ := by
  unfold antiderivG0
  convert ((hasDerivAt_sin_pow_pred d hd θ).mul
    (hasDerivAt_poissonDenom_rpow σ hσ (-(d : ℝ) / 2) θ)).const_mul (1 - σ ^ 2) using 1
  rw [poissonKernelDensity_eq_mul_rpow_neg d σ hσ θ,
      poissonKernelDensity_eq_mul_rpow_neg (d + 2) σ hσ θ,
      show -(d : ℝ) / 2 - 1 = -((d + 2 : ℕ) : ℝ) / 2 by push_cast; ring,
      show (d + 2) - 2 = (d - 1) + 1 by omega, pow_succ]
  ring

private lemma halfcircle_step_norm (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d) :
    (d : ℝ) * σ * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ) =
    ((d : ℝ) - 1) * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ) := by
  have hg := poissonKernelDensity_continuous d σ hσ
  have hg2 := poissonKernelDensity_continuous (d + 2) σ hσ
  have h := intervalIntegral_eq_of_hasDerivAt_sub (hasDerivAt_antiderivG0 d σ hσ hd)
    (continuous_const.mul (hg.mul continuous_cos)) (continuous_const.mul hg2)
    (by simp [antiderivG0_eq d σ hσ hd])
  simp only [intervalIntegral.integral_const_mul] at h
  exact h.symm

/-- Smooth antiderivative `F̃₀(θ) = D(σ, θ) · G̃₀(θ) = (1 - σ²) sin^{d-1}θ · D(σ, θ)^{1 - d/2}`
    for the three-term moment relation connecting `I₂(d)`, `I₁(d)`, and `I₀(d)`. -/
private noncomputable def antiderivF0 (d : ℕ) (σ θ : ℝ) : ℝ :=
  poissonDenom σ θ * antiderivG0 d σ θ

private lemma hasDerivAt_antiderivF0 (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d)
    (θ : ℝ) :
    HasDerivAt (antiderivF0 d σ)
      (((d : ℝ) - 1) * (1 + σ ^ 2) * (poissonKernelDensity d σ θ * cos θ) -
        σ * (d : ℝ) * (poissonKernelDensity d σ θ * cos θ ^ 2) -
        ((d : ℝ) - 2) * σ * poissonKernelDensity d σ θ) θ := by
  unfold antiderivF0
  convert (hasDerivAt_poissonDenom σ θ).mul (hasDerivAt_antiderivG0 d σ hσ hd θ) using 1
  have h1 := antiderivG0_eq d σ hσ hd θ
  have h2 := poissonKernelDensity_add_two_mul_denom d σ hσ hd θ
  have hD : poissonDenom σ θ = 1 + σ ^ 2 - 2 * σ * cos θ := rfl
  linear_combination -2 * σ * sin θ * h1 + (d : ℝ) * σ * h2 -
    ((d : ℝ) - 1) * poissonKernelDensity d σ θ * cos θ * hD +
    ((d : ℝ) - 2) * σ * poissonKernelDensity d σ θ * Real.sin_sq_add_cos_sq θ

private lemma halfcircle_three_term (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d) :
    σ * (d : ℝ) * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ ^ 2) =
    ((d : ℝ) - 1) * (1 + σ ^ 2) *
      (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ) -
    ((d : ℝ) - 2) * σ * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ) := by
  have hg := poissonKernelDensity_continuous d σ hσ
  have h := intervalIntegral_eq_of_hasDerivAt_sub_sub (hasDerivAt_antiderivF0 d σ hσ hd)
    (continuous_const.mul (hg.mul continuous_cos))
    (continuous_const.mul (hg.mul (continuous_cos.pow 2)))
    (continuous_const.mul hg)
    (by simp [antiderivF0, antiderivG0_eq d σ hσ hd])
  simp only [intervalIntegral.integral_const_mul] at h
  linarith

/-- Smooth antiderivative `G̃₁(θ) = cos θ · G̃₀(θ)` relating `I₁(d + 2)` to `I₂(d)` and `I₀(d)`. -/
private noncomputable def antiderivG1 (d : ℕ) (σ θ : ℝ) : ℝ :=
  cos θ * antiderivG0 d σ θ

private lemma hasDerivAt_antiderivG1 (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d)
    (θ : ℝ) :
    HasDerivAt (antiderivG1 d σ)
      ((d : ℝ) * (poissonKernelDensity d σ θ * cos θ ^ 2) -
        poissonKernelDensity d σ θ -
        (d : ℝ) * σ * (poissonKernelDensity (d + 2) σ θ * cos θ)) θ := by
  unfold antiderivG1
  convert (Real.hasDerivAt_cos θ).mul (hasDerivAt_antiderivG0 d σ hσ hd θ) using 1
  rw [antiderivG0_eq d σ hσ hd θ]
  linear_combination poissonKernelDensity d σ θ * Real.sin_sq_add_cos_sq θ

private lemma halfcircle_step_cos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d) :
    (d : ℝ) * σ * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ * cos θ) =
    (d : ℝ) * (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ ^ 2) -
      (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ) := by
  have hg := poissonKernelDensity_continuous d σ hσ
  have hg2 := poissonKernelDensity_continuous (d + 2) σ hσ
  have h := intervalIntegral_eq_of_hasDerivAt_sub_sub (hasDerivAt_antiderivG1 d σ hσ hd)
    (continuous_const.mul (hg.mul (continuous_cos.pow 2))) hg
    (continuous_const.mul (hg2.mul continuous_cos))
    (by simp [antiderivG1, antiderivG0_eq d σ hσ hd])
  simp only [intervalIntegral.integral_const_mul] at h
  linarith

private lemma halfcircle_cos_step (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d)
    (ih : ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ =
          σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ) :
    ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ * cos θ =
    σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity (d + 2) σ θ := by
  have hσ' := Set.Ioo_subset_Ico_self hσ
  have h3 := halfcircle_three_term d σ hσ' hd
  have hG0 := halfcircle_step_norm d σ hσ' hd
  have hG1 := halfcircle_step_cos d σ hσ' hd
  rw [ih] at h3 hG0
  have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply mul_left_cancel₀ (mul_ne_zero hd_ne (pow_ne_zero 2 hσ.1.ne'))
  linear_combination σ * hG1 + h3 - σ ^ 2 * hG0

/-- Smooth antiderivative `H̃₃(θ)` for the `d = 3` base case `I₁(3) = σ I₀(3)`. -/
private noncomputable def antiderivH3 (σ θ : ℝ) : ℝ :=
  (-(1 - σ ^ 2) / (2 * σ ^ 2)) *
    ((1 - σ ^ 2) * poissonDenom σ θ ^ (-(1 : ℝ) / 2) +
      poissonDenom σ θ ^ ((1 : ℝ) / 2))

private lemma hasDerivAt_antiderivH3 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (θ : ℝ) :
    HasDerivAt (antiderivH3 σ)
      (poissonKernelDensity 3 σ θ * cos θ - σ * poissonKernelDensity 3 σ θ) θ := by
  have hσ' := Set.Ioo_subset_Ico_self hσ
  have hD := denom_pos σ θ hσ'
  have hm := (hasDerivAt_poissonDenom_rpow σ hσ' (-(1 : ℝ) / 2) θ).const_mul (1 - σ ^ 2)
  have hp := hasDerivAt_poissonDenom_rpow σ hσ' ((1 : ℝ) / 2) θ
  unfold antiderivH3
  convert (hm.add hp).const_mul (-(1 - σ ^ 2) / (2 * σ ^ 2)) using 1
  rw [poissonKernelDensity_eq_mul_rpow_neg 3 σ hσ' θ,
      show -(1 : ℝ) / 2 - 1 = -((3 : ℕ) : ℝ) / 2 by norm_num,
      show (1 : ℝ) / 2 - 1 = -((3 : ℕ) : ℝ) / 2 + 1 by norm_num,
      Real.rpow_add hD, Real.rpow_one]
  unfold poissonDenom
  norm_num
  field_simp [hσ.1.ne']
  ring

private lemma antiderivH3_endpoints (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    antiderivH3 σ Real.pi = antiderivH3 σ 0 := by
  have hsq : ∀ {a : ℝ}, 0 ≤ a →
      (a ^ 2) ^ ((1 : ℝ) / 2) = a ∧ (a ^ 2) ^ (-(1 : ℝ) / 2) = a⁻¹ := fun {a} ha => by
    have h : (a ^ 2) ^ ((1 : ℝ) / 2) = a := by
      rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha]; norm_num
    exact ⟨h, by rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg (sq_nonneg _), h]⟩
  have h1m : 0 < 1 - σ := by linarith [hσ.2]
  have h1p : 0 < 1 + σ := by linarith [hσ.1]
  unfold antiderivH3 poissonDenom
  rw [Real.cos_zero, Real.cos_pi,
      show 1 + σ ^ 2 - 2 * σ * 1 = (1 - σ) ^ 2 by ring,
      show 1 + σ ^ 2 - 2 * σ * -1 = (1 + σ) ^ 2 by ring,
      (hsq h1m.le).1, (hsq h1m.le).2, (hsq h1p.le).1, (hsq h1p.le).2]
  congr 1
  field_simp [h1m.ne', h1p.ne']
  ring

private lemma halfcircle_cos_d3 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity 3 σ θ * cos θ =
    σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity 3 σ θ := by
  have hg := poissonKernelDensity_continuous 3 σ (Set.Ioo_subset_Ico_self hσ)
  have h := intervalIntegral_eq_of_hasDerivAt_sub (hasDerivAt_antiderivH3 σ hσ)
    (hg.mul continuous_cos) (continuous_const.mul hg) (antiderivH3_endpoints σ hσ)
  rwa [intervalIntegral.integral_const_mul] at h

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

/-- Unnormalized first moment identity on `[0, 1)`: includes `σ = 0` via 1D FTC on `sin^{d-1} θ`. -/
lemma halfcircle_cos_eq_Ico (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d) :
    ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ =
    σ * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ := by
  rcases eq_or_lt_of_le hσ.1 with rfl | hσ_pos
  · have h := halfcircle_step_norm d 0 hσ hd
    have hd1 : (d : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
      linarith
    simp only [mul_zero, zero_mul] at h ⊢
    exact mul_left_cancel₀ hd1 (by linarith)
  · exact halfcircle_cos_eq d σ ⟨hσ_pos, hσ.2⟩ hd

/-- The mean of `cos θ` under `poissonMarginal d σ` equals `σ` for all `σ ∈ [0, 1)` and `d ≥ 2`. -/
theorem poissonMarginal_mean_cos_Ico (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d) :
    ∫ θ, cos θ ∂(poissonMarginal d σ) = σ := by
  rw [integral_poissonMarginal_eq_Ico d σ hσ hd, halfcircle_cos_eq_Ico d σ hσ hd,
      ← poissonNormConst_eq_intervalIntegral]
  exact mul_div_cancel_right₀ σ (poissonNormConst_pos_Ico d σ hσ hd).ne'

/-- The mean of `cos θ` under the Poisson marginal equals `σ` for all `d ≥ 2`.
    `σ = E[cos θ]` represents the average amplitude overlap between the perturbed
    and ideal state. -/
theorem poissonMarginal_mean_cos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ, cos θ ∂(poissonMarginal d σ) = σ :=
  poissonMarginal_mean_cos_Ico d σ (Set.Ioo_subset_Ico_self hσ) hd

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
  have h3 := halfcircle_three_term d σ (Set.Ioo_subset_Ico_self hσ) hd
  rw [halfcircle_cos_eq d σ hσ hd] at h3
  have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply mul_left_cancel₀ hσ.1.ne'
  field_simp [hd_ne]
  linear_combination h3

/-- Unnormalized second moment identity on `[0, 1)`: includes `σ = 0` via 1D FTC on
    `sin^{d-1} θ cos θ`. -/
theorem halfcircle_cos_sq_eq_Ico (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d) :
    ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ ^ 2 =
    ((d - 1 : ℝ) * σ ^ 2 + 1) / d * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ := by
  rcases eq_or_lt_of_le hσ.1 with rfl | hσ_pos
  · have h := halfcircle_step_cos d 0 hσ hd
    have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), zero_add] at h ⊢
    field_simp [hd_ne]
    linarith
  · exact halfcircle_cos_sq_eq d σ ⟨hσ_pos, hσ.2⟩ hd

/-- Second moment of `cos θ` under `poissonMarginal d σ` for all `σ ∈ [0, 1)` and `d ≥ 2`. -/
theorem poissonMarginal_cos_sq_Ico (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ico 0 1) (hd : 2 ≤ d) :
    ∫ θ, (cos θ) ^ 2 ∂(poissonMarginal d σ) = ((d - 1 : ℝ) * σ ^ 2 + 1) / d := by
  rw [integral_poissonMarginal_eq_Ico d σ hσ hd, halfcircle_cos_sq_eq_Ico d σ hσ hd,
      ← poissonNormConst_eq_intervalIntegral]
  exact mul_div_cancel_right₀ _ (poissonNormConst_pos_Ico d σ hσ hd).ne'

/-! ## Closed-interval angle measure on `[0, 1]` -/

/-- Extended angle perturbation measure on `[0, 1]`: coincides with `poissonMarginal d σ`
    for `σ ∈ [0, 1)` and equals `Measure.dirac 0` at the noiseless endpoint `σ = 1`. -/
noncomputable def poissonAngleMeasure (d : ℕ) (σ : ℝ) : Measure ℝ :=
  if σ = 1 then Measure.dirac 0 else poissonMarginal d σ

/-- `poissonAngleMeasure d σ` is a probability measure for all `σ ∈ [0, 1]` and `d ≥ 2`. -/
theorem poissonAngleMeasure_isProbMeasure (d : ℕ) (σ : ℝ)
    (hσ : σ ∈ Set.Icc 0 1) (hd : 2 ≤ d) :
    IsProbabilityMeasure (poissonAngleMeasure d σ) := by
  unfold poissonAngleMeasure
  split_ifs with h1
  · infer_instance
  · exact poissonMarginal_isProbMeasure_Ico d σ ⟨hσ.1, lt_of_le_of_ne hσ.2 h1⟩ hd

/-- `poissonAngleMeasure (d n) σ` is a probability measure for all `σ ∈ [0, 1]`. -/
lemma poissonAngleMeasure_d_isProbMeasure (n : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (poissonAngleMeasure (d n) σ) :=
  poissonAngleMeasure_isProbMeasure (d n) σ hσ (two_le_d n)

/-- First moment `E[cos θ] = σ` under `poissonAngleMeasure d σ` for all `σ ∈ [0, 1]` and `d ≥ 2`. -/
theorem poissonAngleMeasure_mean_cos (d : ℕ) (σ : ℝ)
    (hσ : σ ∈ Set.Icc 0 1) (hd : 2 ≤ d) :
    ∫ θ, cos θ ∂(poissonAngleMeasure d σ) = σ := by
  unfold poissonAngleMeasure
  split_ifs with h1
  · simp [h1]
  · exact poissonMarginal_mean_cos_Ico d σ ⟨hσ.1, lt_of_le_of_ne hσ.2 h1⟩ hd

/-- Second moment `E[cos² θ] = ((d - 1) σ² + 1) / d` under `poissonAngleMeasure d σ`
    for all `σ ∈ [0, 1]` and `d ≥ 2`. -/
theorem poissonAngleMeasure_cos_sq (d : ℕ) (σ : ℝ)
    (hσ : σ ∈ Set.Icc 0 1) (hd : 2 ≤ d) :
    ∫ θ, (cos θ) ^ 2 ∂(poissonAngleMeasure d σ) = ((d - 1 : ℝ) * σ ^ 2 + 1) / d := by
  unfold poissonAngleMeasure
  split_ifs with h1
  · subst h1
    have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [integral_dirac, Real.cos_zero, one_pow, mul_one]
    field_simp [hd_ne]
    ring
  · exact poissonMarginal_cos_sq_Ico d σ ⟨hσ.1, lt_of_le_of_ne hσ.2 h1⟩ hd

/-- `cos² θ` is integrable under any probability measure on `ℝ`. -/
lemma cos_sq_integrable_prob {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    Integrable (fun θ => cos θ ^ 2) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (continuous_cos.pow 2).measurable.aestronglyMeasurable
  · filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]

/-- `sin² θ` is integrable under any probability measure on `ℝ`. -/
lemma sin_sq_integrable_prob {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    Integrable (fun θ => sin θ ^ 2) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · exact (continuous_sin.pow 2).measurable.aestronglyMeasurable
  · filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]

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

/--
info: 'IsotropicGrover.poissonAngleMeasure_isProbMeasure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms poissonAngleMeasure_isProbMeasure

/--
info: 'IsotropicGrover.poissonAngleMeasure_mean_cos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms poissonAngleMeasure_mean_cos

/--
info: 'IsotropicGrover.poissonAngleMeasure_cos_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms poissonAngleMeasure_cos_sq

#check @poissonAngleMeasure
#check @poissonAngleMeasure_isProbMeasure
#check @poissonAngleMeasure_mean_cos
#check @poissonAngleMeasure_cos_sq

end IsotropicGrover
