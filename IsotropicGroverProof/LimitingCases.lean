-- IsotropicGroverProof/LimitingCases.lean
-- M8: Limiting case corollaries — pure continuity/arithmetic, no sorrys.
--     1. σ^{2G} → 1 (perfect gates):  E[p_e] → p_ideal
--     2. σ^{2G} → 0 (full decoherence): E[p_e] → 1/N

import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed
import IsotropicGroverProof.MainTheorem

namespace IsotropicGrover

open Filter Topology Real MeasureTheory

variable {n : ℕ}

/-! ## The mixture function -/

/-- The mixture formula as a real function of fidelity f ∈ [0,1]. -/
noncomputable def mixtureProb (p : ℝ) (N : ℕ) (f : ℝ) : ℝ :=
  f * p + (1 - f) / N

/-- mixtureProb is continuous (affine function of f). -/
lemma mixtureProb_continuous (p : ℝ) (N : ℕ) : Continuous (mixtureProb p N) := by
  unfold mixtureProb
  fun_prop

/-! ## Limiting case 1: perfect gates -/

/-- When fidelity f = 1 (σ^{2G} = 1), the mixture reduces to the ideal success probability.
    The σ=1 case: no noise, so E[p_e] = p_ideal exactly. -/
lemma mixtureProb_at_one (p : ℝ) (N : ℕ) : mixtureProb p N 1 = p := by
  simp [mixtureProb]

/-- As f → 1, the expected success probability tends to p_ideal. -/
theorem tendsto_ideal_as_fidelity_one (p : ℝ) (N : ℕ) :
    Tendsto (mixtureProb p N) (𝓝 1) (𝓝 p) := by
  have h : ContinuousAt (mixtureProb p N) 1 := (mixtureProb_continuous p N).continuousAt
  simp only [ContinuousAt, mixtureProb_at_one] at h
  exact h

/-! ## Limiting case 2: full decoherence -/

/-- When fidelity f = 0 (σ^{2G} = 0), the mixture reduces to 1/N (uniform random guess). -/
lemma mixtureProb_at_zero (p : ℝ) (N : ℕ) : mixtureProb p N 0 = 1 / N := by
  simp [mixtureProb]

/-- As f → 0, the expected success probability tends to 1/N.
    The decoherent limit: the algorithm is no better than random guessing. -/
theorem tendsto_random_as_fidelity_zero (p : ℝ) (N : ℕ) :
    Tendsto (mixtureProb p N) (𝓝 0) (𝓝 (1 / N)) := by
  have h : ContinuousAt (mixtureProb p N) 0 := (mixtureProb_continuous p N).continuousAt
  simp only [ContinuousAt, mixtureProb_at_zero] at h
  exact h

/-! ## Monotonicity: more noise → worse performance -/

/-- The mixture probability is monotone increasing in the fidelity f,
    provided p_ideal ≥ 1/N (which is guaranteed for Grover at optimal iterations). -/
lemma mixtureProb_mono (p : ℝ) (N : ℕ) (hN : 0 < N)
    (hp : 1 / (N : ℝ) ≤ p) : Monotone (mixtureProb p N) := by
  intro f₁ f₂ hf
  simp only [mixtureProb]
  have hN' : (N : ℝ) > 0 := Nat.cast_pos.mpr hN
  have hN'' : (N : ℝ) ≠ 0 := hN'.ne'
  suffices h : 0 ≤ f₂ * p + (1 - f₂) / ↑N - (f₁ * p + (1 - f₁) / ↑N) by linarith
  have key : f₂ * p + (1 - f₂) / ↑N - (f₁ * p + (1 - f₁) / ↑N) =
             (f₂ - f₁) * (p - 1 / ↑N) := by field_simp; ring
  rw [key]
  exact mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hp)

/-! ## Connection to isotropicGrover_main -/

/-- The RHS of `isotropicGrover_main` matches `mixtureProb` evaluated at fidelity `σ^(2G)`
    and database size `2^n`. -/
theorem isotropicGrover_rhs_eq_mixtureProb (G : ℕ) (σ : ℝ) (Φ : E n) (w : Fin (2 ^ n)) :
    σ ^ (2 * G) * succProb n Φ w + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) =
    mixtureProb (succProb n Φ w) (2 ^ n) (σ ^ (2 * G)) := by
  simp only [mixtureProb, Nat.cast_pow, Nat.cast_ofNat]

/-- The LHS of `isotropicGrover_main` (the expected noisy Grover success probability under
    the error model) equals `mixtureProb` evaluated at fidelity `σ^(2G)`. -/
theorem isotropicGrover_lhs_eq_mixtureProb (G : ℕ) (hG : 0 < G) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) :
    (∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
          ∂(perpSphereMeasure Φ)
      ∂(composedMeasure (d n) G σ)) =
    mixtureProb (succProb n Φ w) (2 ^ n) (σ ^ (2 * G)) := by
  rw [isotropicGrover_main G hG σ hσ Φ hΦ w]
  simp only [mixtureProb, Nat.cast_pow, Nat.cast_ofNat]

/-! ## Limiting behavior under per-gate fidelity parameter σ -/

/-- For any ideal probability `p`, database size `N`, and gate count `G`,
    the function `σ ↦ mixtureProb p N (σ^(2G))` is continuous everywhere on `ℝ`. -/
lemma continuous_mixtureProb_pow (p : ℝ) (N : ℕ) (G : ℕ) :
    Continuous (fun σ : ℝ => mixtureProb p N (σ ^ (2 * G))) :=
  (mixtureProb_continuous p N).comp (continuous_pow (2 * G))

/-- As the per-gate parameter `σ → 1`, the mixture tends to `p` (ideal success probability). -/
theorem tendsto_mixtureProb_pow_as_sigma_one (p : ℝ) (N : ℕ) (G : ℕ) :
    Tendsto (fun σ : ℝ => mixtureProb p N (σ ^ (2 * G))) (𝓝 1) (𝓝 p) := by
  have hc := (continuous_mixtureProb_pow p N G).continuousAt (x := 1)
  simp only [ContinuousAt, one_pow, mixtureProb_at_one] at hc
  exact hc

/-- As the per-gate parameter `σ → 0` with `G > 0`, the mixture tends to `1/N` (random guess). -/
theorem tendsto_mixtureProb_pow_as_sigma_zero (p : ℝ) (N : ℕ) {G : ℕ} (hG : 0 < G) :
    Tendsto (fun σ : ℝ => mixtureProb p N (σ ^ (2 * G))) (𝓝 0) (𝓝 (1 / (N : ℝ))) := by
  have hc := (continuous_mixtureProb_pow p N G).continuousAt (x := 0)
  have h2G : 2 * G ≠ 0 := by omega
  simp only [ContinuousAt, zero_pow h2G, mixtureProb_at_zero] at hc
  exact hc

/-! ## Direct limiting case corollaries for isotropicGrover_main -/

/-- Limiting case 1: As per-gate fidelity `σ → 1` within `(0, 1)`,
    the expected noisy success probability converges to the ideal success probability `p_ideal`. -/
theorem tendsto_expectedSuccProb_as_sigma_one (G : ℕ) (hG : 0 < G)
    (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) :
    Tendsto (fun σ => ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
               ∂(perpSphereMeasure Φ)
             ∂(composedMeasure (d n) G σ))
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (succProb n Φ w)) := by
  have heq : (fun σ => ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
                 ∂(perpSphereMeasure Φ)
               ∂(composedMeasure (d n) G σ)) =ᶠ[𝓝[Set.Ioo 0 1] 1]
             (fun σ => mixtureProb (succProb n Φ w) (2 ^ n) (σ ^ (2 * G))) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact isotropicGrover_lhs_eq_mixtureProb G hG σ hσ Φ hΦ w
  refine Tendsto.congr' heq.symm ?_
  exact (tendsto_mixtureProb_pow_as_sigma_one (succProb n Φ w) (2 ^ n) G).mono_left
    nhdsWithin_le_nhds

/-- Limiting case 1 (left neighborhood): As `σ → 1⁻` (from the left),
    the expected noisy success probability converges to the ideal success probability. -/
theorem tendsto_expectedSuccProb_as_sigma_one_left (G : ℕ) (hG : 0 < G)
    (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) :
    Tendsto (fun σ => ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
               ∂(perpSphereMeasure Φ)
             ∂(composedMeasure (d n) G σ))
      (𝓝[<] 1) (𝓝 (succProb n Φ w)) := by
  rw [← nhdsWithin_Ioo_eq_nhdsLT zero_lt_one]
  exact tendsto_expectedSuccProb_as_sigma_one G hG Φ hΦ w

/-- Limiting case 2: As per-gate fidelity `σ → 0` within `(0, 1)`,
    the expected noisy success probability converges to `1 / 2^n` (random guess). -/
theorem tendsto_expectedSuccProb_as_sigma_zero (G : ℕ) (hG : 0 < G)
    (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) :
    Tendsto (fun σ => ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
               ∂(perpSphereMeasure Φ)
             ∂(composedMeasure (d n) G σ))
      (𝓝[Set.Ioo 0 1] 0) (𝓝 (1 / (2 ^ n : ℝ))) := by
  have heq : (fun σ => ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
                 ∂(perpSphereMeasure Φ)
               ∂(composedMeasure (d n) G σ)) =ᶠ[𝓝[Set.Ioo 0 1] 0]
             (fun σ => mixtureProb (succProb n Φ w) (2 ^ n) (σ ^ (2 * G))) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact isotropicGrover_lhs_eq_mixtureProb G hG σ hσ Φ hΦ w
  refine Tendsto.congr' heq.symm ?_
  have hlim := tendsto_mixtureProb_pow_as_sigma_zero (succProb n Φ w) (2 ^ n) hG
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hlim
  exact hlim.mono_left nhdsWithin_le_nhds

/-- Limiting case 2 (right neighborhood): As `σ → 0⁺` (from the right),
    the expected noisy success probability converges to `1 / 2^n`. -/
theorem tendsto_expectedSuccProb_as_sigma_zero_right (G : ℕ) (hG : 0 < G)
    (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) :
    Tendsto (fun σ => ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
               ∂(perpSphereMeasure Φ)
             ∂(composedMeasure (d n) G σ))
      (𝓝[>] 0) (𝓝 (1 / (2 ^ n : ℝ))) := by
  rw [← nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
  exact tendsto_expectedSuccProb_as_sigma_zero G hG Φ hΦ w

/-! ## TDD spot-checks -/

-- Numeric: n=2 (N=4), p_ideal=0.9609, σ=0.99, G=100
-- σ^{2G} ≈ 0.99^200 ≈ 0.134
-- E[p_e] ≈ 0.134 * 0.9609 + (1-0.134)/4 ≈ 0.1288 + 0.2165 ≈ 0.345
example : mixtureProb 1 4 1 = 1 := by simp [mixtureProb]
example : mixtureProb 1 4 0 = 1/4 := by simp [mixtureProb]
example : mixtureProb (1/2 : ℝ) 4 0 = 1/4 := by simp [mixtureProb]
example : mixtureProb (1/2 : ℝ) 4 1 = 1/2 := by simp [mixtureProb]

-- Verify the key limiting values and connections
#check @tendsto_ideal_as_fidelity_one
#check @tendsto_random_as_fidelity_zero
#check @isotropicGrover_rhs_eq_mixtureProb
#check @isotropicGrover_lhs_eq_mixtureProb
#check @tendsto_expectedSuccProb_as_sigma_one
#check @tendsto_expectedSuccProb_as_sigma_zero

end IsotropicGrover
