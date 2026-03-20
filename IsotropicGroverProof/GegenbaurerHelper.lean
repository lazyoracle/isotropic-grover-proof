-- Helper file for poissonIntegral_cos_sq (d=2 case)
-- Proves the Poisson integral formula for h(ξ) = cos²θ when d = 2,
-- using Mathlib's complex Poisson formula and symmetry of the kernel.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import IsotropicGroverProof.IsotropicError

set_option maxHeartbeats 400000

namespace IsotropicGrover

open Real MeasureTheory Complex Set MeasureTheory.Measure intervalIntegral

/-! ## d=2 auxiliary: density is continuous -/

private lemma denom_pos_d2 (σ θ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    0 < 1 + σ ^ 2 - 2 * σ * Real.cos θ := by
  have hcos : Real.cos θ ≤ 1 := Real.cos_le_one θ
  nlinarith [sq_nonneg (σ - Real.cos θ), sq_nonneg (1 - σ), hσ.1, hσ.2]

/-- For d=2, poissonKernelDensity is continuous on all of ℝ when σ ∈ (0,1). -/
lemma poissonKernelDensity_continuous_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    Continuous (poissonKernelDensity 2 σ) := by
  unfold poissonKernelDensity
  simp only [Nat.sub_self, pow_zero, mul_one]
  apply Continuous.div
  · exact continuous_const
  · apply Continuous.rpow_const
    · exact (continuous_const.add continuous_const).sub
        (continuous_const.mul Real.continuous_cos)
    · intro θ; left; exact (denom_pos_d2 σ θ hσ).ne'
  · intro θ; exact (Real.rpow_pos_of_pos (denom_pos_d2 σ θ hσ) _).ne'

/-! ## Helpers for the Poisson kernel formula -/

-- ‖exp(iθ) - σ‖² = 1 + σ² - 2σcosθ
private lemma norm_sq_exp_sub_real (σ θ : ℝ) :
    ‖Complex.exp (↑θ * I) - ↑σ‖ ^ 2 = 1 + σ ^ 2 - 2 * σ * Real.cos θ := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
             Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
             Complex.ofReal_re, Complex.ofReal_im]
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 :=
    by linarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [Real.cos_sq_le_one θ, sq_nonneg (Real.sin θ)]

private lemma norm_ofReal_eq (σ : ℝ) : ‖(σ : ℂ)‖ = |σ| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

-- On unit circle: poissonKernel 0 σ (exp(iθ)) = poissonKernelDensity 2 σ θ
private lemma poissonKernel_eq_density_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (θ : ℝ) :
    poissonKernel 0 (σ : ℂ) (Complex.exp (↑θ * I)) = poissonKernelDensity 2 σ θ := by
  simp only [poissonKernel_def, poissonKernelDensity, sub_zero]
  have hnorm1 : ‖Complex.exp (↑θ * I)‖ ^ 2 = 1 := by
    rw [Complex.norm_exp_ofReal_mul_I]; norm_num
  have hnormσ : ‖(σ : ℂ)‖ ^ 2 = σ ^ 2 := by
    rw [norm_ofReal_eq, sq_abs]
  rw [hnorm1, hnormσ, norm_sq_exp_sub_real σ θ]
  simp only [Nat.sub_self, pow_zero, mul_one]
  norm_cast
  rw [show (2 : ℝ) / 2 = 1 from by norm_num, rpow_one]

private lemma holo_F : Differentiable ℂ (fun z : ℂ => z ^ 2 / 2 + 1/2) := by fun_prop

private lemma sigma_in_ball (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    (σ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, Complex.dist_eq, sub_zero, norm_ofReal_eq, abs_of_pos hσ.1]
  exact hσ.2

-- Re(z²/2 + 1/2) = z.re² when ‖z‖ = 1
private lemma re_F_on_sphere (z : ℂ) (hz : ‖z‖ = 1) :
    (z ^ 2 / 2 + 1/2 : ℂ).re = z.re ^ 2 := by
  have hzim_sq : z.im ^ 2 = 1 - z.re ^ 2 := by
    have hns := Complex.normSq_eq_norm_sq z
    rw [hz, one_pow] at hns
    simp only [Complex.normSq_apply] at hns
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have h1 : (z ^ 2 / 2 : ℂ).re = (z.re ^ 2 - z.im ^ 2) / 2 := by
    rw [Complex.div_re]; simp [sq, Complex.mul_re]; ring
  have h2 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  simp only [Complex.add_re, h1, h2, hzim_sq]; ring

private lemma poissonKernel_contOn_sphere (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ContinuousOn (poissonKernel 0 (σ : ℂ)) (Metric.sphere (0 : ℂ) 1) := by
  intro z hz
  simp only [Metric.mem_sphere, dist_zero_right] at hz
  apply ContinuousAt.continuousWithinAt
  show ContinuousAt (fun w : ℂ =>
      (‖w - 0‖ ^ 2 - ‖(σ:ℂ) - 0‖ ^ 2) / ‖(w - 0) - ((σ:ℂ) - 0)‖ ^ 2) z
  simp only [sub_zero]
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · rw [pow_ne_zero_iff (by norm_num), norm_ne_zero_iff, sub_ne_zero]
    intro heq
    rw [heq, norm_ofReal_eq, abs_of_pos hσ.1] at hz
    linarith [hσ.2]

private lemma hci_F (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    CircleIntegrable (poissonKernel 0 (σ : ℂ) • (fun z : ℂ => z ^ 2 / 2 + 1/2)) 0 1 := by
  apply ContinuousOn.circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have heq : poissonKernel 0 (σ : ℂ) • (fun z : ℂ => z ^ 2 / 2 + 1/2) =
      fun z : ℂ => (↑(poissonKernel 0 (σ : ℂ) z) : ℂ) * (z ^ 2 / 2 + 1/2) := by
    ext z; simp [Complex.real_smul]
  rw [heq]
  apply ContinuousOn.mul
  · exact Complex.continuous_ofReal.continuousOn.comp
      (poissonKernel_contOn_sphere σ hσ) (Set.mapsTo_univ _ _)
  · exact holo_F.continuous.continuousOn

/-! ## Circle average formulas -/

-- Circle average of K · Re(·)² = (1 + σ²)/2  (from Poisson formula for F(z)=z²/2+1/2)
private lemma circleAverage_poissonKernel_re_sq (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    Real.circleAverage (fun z => poissonKernel 0 (σ : ℂ) z * z.re ^ 2) 0 1 =
    (1 + σ ^ 2) / 2 := by
  have hF : DiffContOnCl ℂ (fun z : ℂ => z ^ 2 / 2 + 1/2) (Metric.ball 0 1) :=
    holo_F.diffContOnCl
  have hpoisson :
      Real.circleAverage (poissonKernel 0 (σ : ℂ) • (fun z : ℂ => z ^ 2 / 2 + 1/2)) 0 1 =
      ((σ : ℂ) ^ 2 / 2 + 1/2) :=
    hF.circleAverage_poissonKernel_smul (sigma_in_ball σ hσ)
  have hFσ : ((σ : ℂ) ^ 2 / 2 + 1/2 : ℂ).re = (1 + σ^2) / 2 := by
    have h1 : ((σ : ℂ)^2/2 : ℂ).re = σ^2/2 := by
      have h1a : ((σ : ℂ)^2/2 : ℂ).re = ((σ : ℂ)^2).re / 2 := by
        rw [Complex.div_re]; simp [Complex.normSq_ofReal]; ring
      rw [h1a]; norm_cast
    have h2 : (1/2 : ℂ).re = 1/2 := by norm_num
    simp only [Complex.add_re, h1, h2]; ring
  have hlhs_eq :
      Real.circleAverage (fun z => poissonKernel 0 (σ : ℂ) z * z.re ^ 2) 0 1 =
      Real.circleAverage (fun z =>
          (poissonKernel 0 (σ:ℂ) • (fun z : ℂ => z^2/2+1/2)) z |>.re) 0 1 := by
    apply circleAverage_congr_sphere
    intro z hz
    simp only [Metric.mem_sphere, dist_zero_right, abs_one] at hz
    show poissonKernel 0 (↑σ) z * z.re ^ 2 =
        (poissonKernel 0 ↑σ z • (z ^ 2 / 2 + 1 / 2 : ℂ)).re
    rw [Complex.smul_re, smul_eq_mul, re_F_on_sphere z hz]
  rw [hlhs_eq]
  have hci := hci_F σ hσ
  have heq_re : (fun z =>
      (poissonKernel 0 (σ:ℂ) • (fun z : ℂ => z^2/2+1/2)) z |>.re) =
      (Complex.reCLM : ℂ →L[ℝ] ℝ) ∘ (poissonKernel 0 (σ:ℂ) • (fun z : ℂ => z^2/2+1/2)) := by
    ext z; simp [Complex.reCLM_apply]
  rw [heq_re, Complex.reCLM.circleAverage_comp_comm hci]
  simp only [Complex.reCLM_apply, hpoisson, hFσ]

-- Circle average of K = 1  (from Poisson formula for F(z)=1)
private lemma circleAverage_poissonKernel_eq_one (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    Real.circleAverage (poissonKernel 0 (σ : ℂ)) 0 1 = 1 := by
  have hci : CircleIntegrable (poissonKernel 0 (σ : ℂ)) 0 1 :=
    (poissonKernel_contOn_sphere σ hσ).circleIntegrable (by norm_num)
  have hci_ofReal : CircleIntegrable (Complex.ofReal ∘ poissonKernel 0 (σ:ℂ)) 0 1 :=
    Complex.continuous_ofReal.continuousOn.comp
      (poissonKernel_contOn_sphere σ hσ) (Set.mapsTo_univ _ _) |>.circleIntegrable (by norm_num)
  have hcommute : Real.circleAverage (Complex.ofReal ∘ poissonKernel 0 (σ:ℂ)) 0 1 =
      ↑(Real.circleAverage (poissonKernel 0 (σ:ℂ)) 0 1) := by
    have h := Complex.ofRealCLM.circleAverage_comp_comm hci
    simp only [Complex.ofRealCLM_apply] at h; exact h
  have hkey : Real.circleAverage (Complex.ofReal ∘ poissonKernel 0 (σ:ℂ)) 0 1 = 1 := by
    have hF : DiffContOnCl ℂ (fun z : ℂ => (1 : ℂ)) (Metric.ball 0 1) :=
      (differentiable_const (1 : ℂ)).diffContOnCl
    have hpoisson := hF.circleAverage_poissonKernel_smul (sigma_in_ball σ hσ)
    have : Real.circleAverage (Complex.ofReal ∘ poissonKernel 0 (σ:ℂ)) 0 1 =
        Real.circleAverage (poissonKernel 0 (σ:ℂ) • (fun _ : ℂ => (1 : ℂ))) 0 1 := by
      apply circleAverage_congr_sphere; intro z _; simp [Complex.real_smul]
    rw [this]; exact hpoisson
  rw [hcommute] at hkey; exact_mod_cast hkey

/-! ## Full-circle interval integrals (d=2) -/

private lemma circleMap_zero_one (θ : ℝ) : circleMap 0 1 θ = Complex.exp (↑θ * I) := by
  simp [circleMap]

-- ∫₀^{2π} poissonKernelDensity 2 σ θ dθ = 2π
private lemma intervalIntegral_kernel_two_pi (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ in (0:ℝ)..2 * π, poissonKernelDensity 2 σ θ = 2 * π := by
  have hca := circleAverage_poissonKernel_eq_one σ hσ
  rw [Real.circleAverage_def] at hca
  have heq : ∫ θ in (0:ℝ)..2 * π, poissonKernel 0 (σ : ℂ) (circleMap 0 1 θ) =
      ∫ θ in (0:ℝ)..2 * π, poissonKernelDensity 2 σ θ := by
    apply integral_congr; intro θ _
    simp only [circleMap_zero_one, poissonKernel_eq_density_d2 σ hσ]
  rw [heq] at hca
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [smul_eq_mul] at hca
  field_simp [hpi.ne'] at hca
  linarith

-- ∫₀^{2π} poissonKernelDensity 2 σ θ * cos²θ dθ = π * (1 + σ²)
private lemma intervalIntegral_kernel_cos_sq_two_pi (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ in (0:ℝ)..2 * π, poissonKernelDensity 2 σ θ * Real.cos θ ^ 2 = π * (1 + σ ^ 2) := by
  have hca := circleAverage_poissonKernel_re_sq σ hσ
  rw [Real.circleAverage_def] at hca
  have heq : ∫ θ in (0:ℝ)..2 * π,
      poissonKernel 0 (σ : ℂ) (circleMap 0 1 θ) * (circleMap 0 1 θ).re ^ 2 =
      ∫ θ in (0:ℝ)..2 * π, poissonKernelDensity 2 σ θ * Real.cos θ ^ 2 := by
    apply integral_congr; intro θ _
    simp only [circleMap_zero_one, poissonKernel_eq_density_d2 σ hσ,
               Complex.exp_ofReal_mul_I_re]
  rw [heq] at hca
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [smul_eq_mul] at hca
  field_simp [hpi.ne'] at hca
  linarith

/-! ## Folding [0,2π] → [0,π] by kernel symmetry -/

-- d=2 kernel is symmetric under θ ↦ 2π - θ
private lemma poissonKernelDensity_two_symm (σ θ : ℝ) :
    poissonKernelDensity 2 σ (2 * π - θ) = poissonKernelDensity 2 σ θ := by
  simp only [poissonKernelDensity, Nat.sub_self, pow_zero, mul_one, Real.cos_two_pi_sub]

-- For f symmetric under 2π-reflection: ∫_π^{2π} f = ∫_0^π f
private lemma fold_integral {f : ℝ → ℝ} (hf : ∀ θ, f (2*π - θ) = f θ)
    (hf_cont : ContinuousOn f (Set.Icc 0 (2*π))) :
    ∫ θ in (π:ℝ)..2*π, f θ = ∫ θ in (0:ℝ)..π, f θ := by
  rw [show ∫ θ in (π:ℝ)..2*π, f θ = ∫ θ in (π:ℝ)..2*π, f (2*π - θ) from
    integral_congr (fun θ _ => (hf θ).symm)]
  rw [integral_comp_sub_left]
  congr 1 <;> ring

-- ∫₀^π poissonKernelDensity 2 σ θ dθ = π
private lemma intervalIntegral_kernel_pi (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ in (0:ℝ)..π, poissonKernelDensity 2 σ θ = π := by
  have hfull := intervalIntegral_kernel_two_pi σ hσ
  have hK_cont : ContinuousOn (poissonKernelDensity 2 σ) (Set.Icc 0 (2*π)) :=
    (poissonKernelDensity_continuous_d2 σ hσ).continuousOn
  have hK_ibl1 : IntervalIntegrable (poissonKernelDensity 2 σ) volume 0 π :=
    (hK_cont.mono (Set.Icc_subset_Icc_right (by linarith [Real.pi_pos]))).intervalIntegrable_of_Icc
      Real.pi_pos.le
  have hK_ibl2 : IntervalIntegrable (poissonKernelDensity 2 σ) volume π (2*π) :=
    (hK_cont.mono (Set.Icc_subset_Icc_left Real.pi_pos.le)).intervalIntegrable_of_Icc
      (by linarith [Real.pi_pos])
  have hsplit := integral_add_adjacent_intervals hK_ibl1 hK_ibl2
  have hsym := fold_integral (poissonKernelDensity_two_symm σ) hK_cont
  linarith

-- ∫₀^π poissonKernelDensity 2 σ θ * cos²θ dθ = π * (1 + σ²) / 2
private lemma intervalIntegral_kernel_cos_sq_pi (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ in (0:ℝ)..π, poissonKernelDensity 2 σ θ * Real.cos θ ^ 2 = π * (1 + σ ^ 2) / 2 := by
  have hfull := intervalIntegral_kernel_cos_sq_two_pi σ hσ
  have hKcos_cont : ContinuousOn (fun θ => poissonKernelDensity 2 σ θ * Real.cos θ ^ 2)
      (Set.Icc 0 (2*π)) :=
    ((poissonKernelDensity_continuous_d2 σ hσ).continuousOn).mul
      (Real.continuous_cos.pow 2).continuousOn
  have hKcos_ibl1 : IntervalIntegrable (fun θ => poissonKernelDensity 2 σ θ * Real.cos θ ^ 2)
      volume 0 π :=
    (hKcos_cont.mono (Set.Icc_subset_Icc_right (by linarith [Real.pi_pos]))).intervalIntegrable_of_Icc
      Real.pi_pos.le
  have hKcos_ibl2 : IntervalIntegrable (fun θ => poissonKernelDensity 2 σ θ * Real.cos θ ^ 2)
      volume π (2*π) :=
    (hKcos_cont.mono (Set.Icc_subset_Icc_left Real.pi_pos.le)).intervalIntegrable_of_Icc
      (by linarith [Real.pi_pos])
  have hsplit := integral_add_adjacent_intervals hKcos_ibl1 hKcos_ibl2
  have hsym : ∫ θ in (π:ℝ)..2*π, poissonKernelDensity 2 σ θ * Real.cos θ ^ 2 =
      ∫ θ in (0:ℝ)..π, poissonKernelDensity 2 σ θ * Real.cos θ ^ 2 :=
    fold_integral (fun θ => by rw [poissonKernelDensity_two_symm, Real.cos_two_pi_sub])
      hKcos_cont
  linarith

/-! ## poissonNormConst 2 σ = π -/

/-- The normalization constant for d=2 equals π. -/
lemma poissonNormConst_two (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    poissonNormConst 2 σ = π := by
  rw [poissonNormConst, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]
  exact intervalIntegral_kernel_pi σ hσ

/-! ## Main d=2 result -/

/-- Poisson integral formula for h(ξ) = cos²θ at d = 2:
    E[cos²θ] = (σ² + 1) / 2 = ((2-1)σ² + 1) / 2. -/
theorem poissonIntegral_cos_sq_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ, Real.cos θ ^ 2 ∂(poissonMarginal 2 σ) =
    ((2 - 1 : ℝ) * σ ^ 2 + 1) / 2 := by
  simp only [poissonMarginal]
  have hC := poissonNormConst_two σ hσ
  have hCpos : 0 < poissonNormConst 2 σ := by rw [hC]; exact Real.pi_pos
  -- Density is measurable and a.e. finite
  have hK_meas : Measurable (poissonKernelDensity 2 σ) :=
    (poissonKernelDensity_continuous_d2 σ hσ).measurable
  have hdens_meas : Measurable (fun θ =>
      ENNReal.ofReal (poissonKernelDensity 2 σ θ / poissonNormConst 2 σ)) :=
    (hK_meas.div_const _).ennreal_ofReal
  have hdens_lt_top : ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 π)),
      ENNReal.ofReal (poissonKernelDensity 2 σ θ / poissonNormConst 2 σ) < ⊤ :=
    ae_of_all _ (fun θ => ENNReal.ofReal_lt_top)
  -- Unfold withDensity integral
  rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_lt_top]
  -- toReal ∘ ofReal = id for nonneg inputs
  have hK_nonneg : ∀ θ, 0 ≤ poissonKernelDensity 2 σ θ / poissonNormConst 2 σ := fun θ => by
    apply div_nonneg _ hCpos.le
    simp only [poissonKernelDensity, Nat.sub_self, pow_zero, mul_one]
    exact div_nonneg (by nlinarith [hσ.1, hσ.2, mul_pos hσ.1 hσ.1])
      (Real.rpow_nonneg (denom_pos_d2 σ θ hσ).le _)
  simp_rw [ENNReal.toReal_ofReal (hK_nonneg _), smul_eq_mul]
  -- Convert set integral to interval integral
  rw [show ∫ θ in Set.Icc 0 π,
      poissonKernelDensity 2 σ θ / poissonNormConst 2 σ * Real.cos θ ^ 2 =
      ∫ θ in (0:ℝ)..π, poissonKernelDensity 2 σ θ / poissonNormConst 2 σ * Real.cos θ ^ 2 from
    by rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]]
  -- Factor out 1/C
  rw [show ∫ θ in (0:ℝ)..π, poissonKernelDensity 2 σ θ / poissonNormConst 2 σ * Real.cos θ ^ 2 =
      (1 / poissonNormConst 2 σ) * ∫ θ in (0:ℝ)..π,
      poissonKernelDensity 2 σ θ * Real.cos θ ^ 2 from
    by rw [show ∫ θ in (0:ℝ)..π,
        poissonKernelDensity 2 σ θ / poissonNormConst 2 σ * Real.cos θ ^ 2 =
        ∫ θ in (0:ℝ)..π,
        (1 / poissonNormConst 2 σ) * (poissonKernelDensity 2 σ θ * Real.cos θ ^ 2) from
      intervalIntegral.integral_congr (fun θ _ => by ring),
      intervalIntegral.integral_const_mul]]
  -- Substitute known values
  rw [hC, intervalIntegral_kernel_cos_sq_pi σ hσ]
  field_simp [Real.pi_pos.ne']
  ring

end IsotropicGrover
