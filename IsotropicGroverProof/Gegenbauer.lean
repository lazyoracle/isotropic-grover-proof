-- IsotropicGroverProof/Gegenbauer.lean
-- M6: Gegenbauer (ultraspherical) polynomials C_l^μ, the Poisson kernel moment
--     theorem E[C_l^μ(cos θ)] = σ^l · C_l^μ(1), and the derivation of
--     f₂ = ((d-1)σ^{2G} + 1) / d.
--
-- NOTE: The parameter conventionally called λ is renamed to `μ` here because
--       `λ` is a reserved keyword in Lean 4 (lambda abstraction).
--
-- SORRY BUDGET: 1
--   sorry 1 (poissonMarginal_gegen_moment): the Poisson kernel Gegenbauer moment theorem.
--     Source: Axler, Bourdon & Ramey, "Harmonic Function Theory" 2nd ed., Ch. 5.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import IsotropicGroverProof.Composition

namespace IsotropicGrover

open Real MeasureTheory

/-! ## Gegenbauer polynomials C_l^μ(x) -/

/-- Gegenbauer (ultraspherical) polynomials C_l^μ defined by the three-term recurrence:
    C_0^μ(x) = 1
    C_1^μ(x) = 2μx
    C_{l+2}^μ(x) = (2x(μ+l+1) · C_{l+1}^μ(x) - (2μ+l) · C_l^μ(x)) / (l+2)
    These are the zonal spherical harmonics on S^{d-1} with μ = (d-2)/2. -/
noncomputable def gegen (μ : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * μ * x
  | (l + 2), x =>
      (2 * x * (μ + l + 1) * gegen μ (l + 1) x - (2 * μ + l) * gegen μ l x) / (l + 2)

/-- Evaluate C_l^μ at x = 1 using the same recurrence. -/
noncomputable def gegenAt1 (μ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * μ
  | (l + 2) =>
      (2 * (μ + l + 1) * gegenAt1 μ (l + 1) - (2 * μ + l) * gegenAt1 μ l) / (l + 2)

/-! ## Key values -/

@[simp] lemma gegen_zero (μ x : ℝ) : gegen μ 0 x = 1 := rfl
@[simp] lemma gegen_one (μ x : ℝ) : gegen μ 1 x = 2 * μ * x := rfl
@[simp] lemma gegenAt1_zero (μ : ℝ) : gegenAt1 μ 0 = 1 := rfl
@[simp] lemma gegenAt1_one (μ : ℝ) : gegenAt1 μ 1 = 2 * μ := rfl

/-- C_2^μ(x) = 2μ(μ+1)x² - μ -/
lemma gegen_two (μ x : ℝ) : gegen μ 2 x = 2 * μ * (μ + 1) * x ^ 2 - μ := by
  simp [gegen]; ring

/-- C_2^μ(1) = μ(2μ+1) -/
lemma gegenAt1_two (μ : ℝ) : gegenAt1 μ 2 = μ * (2 * μ + 1) := by
  simp [gegenAt1]; ring

/-! ## The Poisson kernel Gegenbauer moment theorem (sorry — Axler-Bourdon-Ramey Ch.5) -/

/-- For θ distributed according to poissonMarginal d σ, we have:
    E[C_l^μ(cos θ)] = σ^l · C_l^μ(1)
    where μ = (d-2)/2.
    Reference: Axler, Bourdon & Ramey, "Harmonic Function Theory" 2nd ed., Ch. 5. -/
theorem poissonMarginal_gegen_moment (d l : ℕ) (σ : ℝ)
    (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ, gegen ((↑d - 2) / 2) l (cos θ) ∂(poissonMarginal d σ) =
    σ ^ l * gegenAt1 ((↑d - 2) / 2) l := by
  sorry -- Cited from Axler-Bourdon-Ramey Ch.5: Poisson kernel generating function identity

/-! ## Extracting f₂ = ((d-1)σ^{2G} + 1) / d -/

/-- The second moment f₂ = E[cos²θ_G] = ((d-1)σ^{2G} + 1) / d.
    Derivation: apply the moment theorem at l=2, solve for E[cos²θ] = f₂.
    Requires d ≥ 3 so that the Gegenbauer parameter μ = (d-2)/2 is nonzero. -/
theorem f₂_formula (d_val G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hd : 3 ≤ d_val) (hG : 0 < G) :
    f₂ d_val G σ = ((d_val - 1 : ℝ) * σ ^ (2 * G) + 1) / d_val := by
  simp only [f₂, composedMeasure]
  -- d ≥ 2 for the moment theorem
  have hd2 : 2 ≤ d_val := by omega
  -- σ^G ∈ (0,1)
  have hσG : σ ^ G ∈ Set.Ioo 0 1 :=
    ⟨pow_pos hσ.1 G, pow_lt_one₀ hσ.1.le hσ.2 hG.ne'⟩
  -- The measure
  set ν := poissonMarginal d_val (σ ^ G) with hν_def
  -- Gegenbauer parameter μ_p = (d-2)/2
  set μ_p := ((d_val : ℝ) - 2) / 2 with hμ_def
  -- Probability measure instance (uses poissonMarginal_isProbMeasure, which is sorry'd)
  haveI hprob : IsProbabilityMeasure ν :=
    poissonMarginal_isProbMeasure d_val (σ ^ G) hσG hd2
  -- μ_p > 0 since d_val ≥ 3
  have hd_cast : (3 : ℝ) ≤ (d_val : ℝ) := by exact_mod_cast hd
  have hd_ne : (d_val : ℝ) ≠ 0 := by linarith
  have hd2_ne : (d_val : ℝ) - 2 ≠ 0 := by linarith
  have hμ_pos : 0 < μ_p := by simp only [hμ_def]; linarith
  have h2μμ1_ne : 2 * μ_p * (μ_p + 1) ≠ 0 := by positivity
  -- Moment theorem at l=2 (uses poissonMarginal_gegen_moment, which is sorry'd)
  have mom2 : ∫ θ : ℝ, gegen μ_p 2 (Real.cos θ) ∂ν = (σ ^ G) ^ 2 * gegenAt1 μ_p 2 :=
    poissonMarginal_gegen_moment d_val 2 (σ ^ G) hσG hd2
  -- Integrability of cos²θ (bounded in [0,1], probability measure is finite)
  have hcos2_int : Integrable (fun θ : ℝ => (Real.cos θ) ^ 2) ν := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact (Real.continuous_cos.pow 2).measurable.aestronglyMeasurable
    · filter_upwards with θ
      have h1 : 0 ≤ (Real.cos θ) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  -- Relate ∫ gegen μ_p 2 (cos θ) to ∫ (cos θ)^2 via gegen_two
  have h_int_gegen : ∫ θ : ℝ, gegen μ_p 2 (Real.cos θ) ∂ν =
      2 * μ_p * (μ_p + 1) * ∫ θ : ℝ, (Real.cos θ) ^ 2 ∂ν - μ_p := by
    have hf : Integrable (fun θ : ℝ => 2 * μ_p * (μ_p + 1) * (Real.cos θ) ^ 2) ν :=
      hcos2_int.const_mul (2 * μ_p * (μ_p + 1))
    have hg : Integrable (fun _ : ℝ => μ_p) ν := integrable_const _
    calc ∫ θ : ℝ, gegen μ_p 2 (Real.cos θ) ∂ν
        = ∫ θ : ℝ, (2 * μ_p * (μ_p + 1) * (Real.cos θ) ^ 2 - μ_p) ∂ν := by
            congr 1; ext θ; exact gegen_two μ_p (Real.cos θ)
      _ = ∫ θ : ℝ, 2 * μ_p * (μ_p + 1) * (Real.cos θ) ^ 2 ∂ν - ∫ _ : ℝ, μ_p ∂ν :=
            integral_sub hf hg
      _ = 2 * μ_p * (μ_p + 1) * ∫ θ : ℝ, (Real.cos θ) ^ 2 ∂ν - μ_p := by
            rw [integral_const_mul, integral_const]
            simp [Measure.real, hprob.measure_univ]
  -- Solve for ∫ (cos θ)^2
  have h_cos2 : ∫ θ : ℝ, (Real.cos θ) ^ 2 ∂ν =
      ((σ ^ G) ^ 2 * gegenAt1 μ_p 2 + μ_p) / (2 * μ_p * (μ_p + 1)) := by
    have heq : 2 * μ_p * (μ_p + 1) * ∫ θ : ℝ, (Real.cos θ) ^ 2 ∂ν =
               (σ ^ G) ^ 2 * gegenAt1 μ_p 2 + μ_p := by linarith [h_int_gegen, mom2]
    rw [eq_div_iff h2μμ1_ne, mul_comm (∫ θ : ℝ, (Real.cos θ) ^ 2 ∂ν)]
    exact heq
  -- Substitute and do final algebra
  rw [h_cos2, gegenAt1_two]
  have hσG2 : (σ ^ G) ^ 2 = σ ^ (2 * G) := by ring
  simp only [hμ_def, hσG2]
  field_simp [hd_ne, hd2_ne]
  ring

/-! ## TDD spot-checks -/

-- Verify gegen_two: C_2^μ(1) = μ(2μ+1) (consistency with gegenAt1_two)
example (μ : ℝ) : gegen μ 2 1 = gegenAt1 μ 2 := by
  rw [gegen_two, gegenAt1_two]; ring

-- For μ=1: C_2^1(x) = 4x² - 1 (Chebyshev U₂ up to scaling)
example (x : ℝ) : gegen 1 2 x = 4 * x ^ 2 - 1 := by rw [gegen_two]; ring

-- f₂ at σ=0: f₂ = 1/d (uniform over sphere)
example (d_val G : ℕ) (_ : 2 ≤ d_val) (hG : 0 < G) :
    ((d_val - 1 : ℝ) * (0 : ℝ) ^ (2 * G) + 1) / d_val = 1 / d_val := by
  have hGne : 2 * G ≠ 0 := by omega
  simp only [zero_pow hGne, mul_zero, zero_add]

-- f₂ at σ=1: f₂ = 1 (perfect gates)
example (d_val G : ℕ) (hd : 0 < d_val) :
    ((d_val - 1 : ℝ) * (1 : ℝ) ^ (2 * G) + 1) / d_val = 1 := by
  have hd' : (d_val : ℝ) ≠ 0 := Nat.cast_pos.mpr hd |>.ne'
  field_simp [hd']; ring

-- Numeric check: n=2 (d=8), G=1, σ=1/2: f₂ = (7 * 1/4 + 1) / 8 = 11/32
example : (((8 : ℝ) - 1) * (1/2 : ℝ) ^ 2 + 1) / 8 = 11/32 := by norm_num

end IsotropicGrover
