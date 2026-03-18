-- IsotropicGroverProof/SecondMoment.lean
-- M5: The second moment matrix E[e₂ e₂ᵀ] = P_{V⊥}/(d-1), where P_{V⊥} is the
--     orthogonal projector onto V_perp. Derives the decoherent floor formula:
--     E[|⟨w|e₂⟩|²] = (2 - p_ideal)/(d - 1)
--
-- SORRY BUDGET: 2
--   sorry 1 (secondMoment_eq_scalar_perp): Schur-type invariance argument
--   sorry 2 (trace_secondMoment_eq_one): blocked by perpSphereMeasure construction

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.L2Space
import IsotropicGroverProof.CrossTerm

namespace IsotropicGrover

open MeasureTheory InnerProductSpace ContinuousLinearMap Real

variable {n : ℕ}

/-! ## Orthogonal projector onto V_perp -/

/-- The orthogonal projector onto V_perp(Φ) = (ℝ · Φ)^⊥. -/
noncomputable def P_perp (Φ : E n) : E n →L[ℝ] E n :=
  (V_perp Φ).subtypeL ∘L (V_perp Φ).orthogonalProjection

/-- P_perp acts as the identity minus projection onto Φ:
    P_perp Φ v = v - ⟪Φ, v⟫ · Φ (when ‖Φ‖ = 1). -/
lemma P_perp_apply (Φ v : E n) (hΦ : ‖Φ‖ = 1) :
    P_perp Φ v = v - ⟪Φ, v⟫_ℝ • Φ := by
  simp only [P_perp, V_perp]
  change (Submodule.span ℝ {Φ})ᗮ.starProjection v = v - ⟪Φ, v⟫_ℝ • Φ
  rw [Submodule.starProjection_orthogonal_val]
  congr 1
  exact Submodule.starProjection_unit_singleton (𝕜 := ℝ) hΦ v

/-! ## Second moment matrix = (1/(d-1)) · P_perp (sorry — Schur argument) -/

/-- Every continuous linear operator T : E n → E n that commutes with all rotations
    fixing Φ must be a scalar multiple of P_perp Φ (restricted to V_perp) plus
    a scalar multiple of the rank-1 projector onto Φ.
    When T = E[e₂ e₂ᵀ] with e₂ ∈ V_perp, the Φ-component vanishes,
    so T = c · P_perp for some c. -/
theorem secondMoment_eq_scalar_perp (Φ : E n) (hΦ : ‖Φ‖ = 1) :
    ∃ c : ℝ, ∀ u : E n,
      ∫ e₂, ⟪(e₂ : E n), u⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Φ) =
      c • P_perp Φ u := by
  sorry -- Schur-type: rotational invariance of perpSphereMeasure forces scalar × P_perp

/-- The trace of the second moment operator equals 1 (since ‖e₂‖ = 1 a.s.). -/
lemma trace_secondMoment_eq_one (Φ : E n) (hΦ : ‖Φ‖ = 1) :
    ∑ i : Fin (d n),
      ∫ e₂, ⟪(e₂ : E n), stdBasisVec n i⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) = 1 := by
  -- Integrability: ⟨e₂, eᵢ⟩² ≤ 1 on the unit sphere
  have hint : ∀ i : Fin (d n),
      Integrable (fun e₂ : E n => inner (𝕜 := ℝ) e₂ (stdBasisVec n i) ^ 2)
        (perpSphereMeasure Φ) := by
    intro i
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact ((inner_integrable Φ (stdBasisVec n i)).aestronglyMeasurable).pow 2
    · filter_upwards [perpSphereMeasure_norm_ae Φ] with e₂ ⟨_, he₂⟩
      have h := abs_real_inner_le_norm e₂ (stdBasisVec n i)
      rw [he₂, stdBasisVec_norm, mul_one] at h
      have hnn : 0 ≤ inner (𝕜 := ℝ) e₂ (stdBasisVec n i) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      nlinarith [sq_abs (inner (𝕜 := ℝ) e₂ (stdBasisVec n i)),
                 abs_nonneg (inner (𝕜 := ℝ) e₂ (stdBasisVec n i))]
  -- Exchange sum and integral
  rw [← integral_finset_sum Finset.univ (fun i _ => hint i)]
  -- Parseval identity: ∑ ⟨e₂, eᵢ⟩² = ‖e₂‖²
  have hparseval : ∀ e₂ : E n,
      ∑ i : Fin (d n), inner (𝕜 := ℝ) e₂ (stdBasisVec n i) ^ 2 = ‖e₂‖ ^ 2 := by
    intro e₂
    have hi : ∀ i : Fin (d n), inner (𝕜 := ℝ) e₂ (stdBasisVec n i) = e₂ i := fun i => by
      simp [stdBasisVec, ← EuclideanSpace.basisFun_apply]
    simp_rw [hi]
    exact (EuclideanSpace.real_norm_sq_eq e₂).symm
  simp_rw [hparseval]
  -- ‖e₂‖² = 1 a.e. (supported on unit sphere)
  have hae : ∀ᵐ e₂ ∂(perpSphereMeasure Φ), ‖e₂‖ ^ 2 = 1 := by
    filter_upwards [perpSphereMeasure_norm_ae Φ] with e₂ ⟨_, he₂⟩
    rw [he₂, one_pow]
  rw [integral_congr_ae hae]
  -- ∫ 1 dμ = 1 (probability measure)
  haveI : IsProbabilityMeasure (perpSphereMeasure Φ) := perpSphereMeasure_isProbMeasure Φ
  rw [integral_const]
  simp [Measure.real, IsProbabilityMeasure.measure_univ]

/-- The trace of P_perp equals d - 1 (the dimension of V_perp). -/
lemma trace_P_perp (Φ : E n) (hΦ : ‖Φ‖ = 1) :
    ∑ i : Fin (d n), ⟪P_perp Φ (stdBasisVec n i), stdBasisVec n i⟫_ℝ = d n - 1 := by
  simp_rw [P_perp_apply Φ _ hΦ, inner_sub_left, real_inner_smul_left]
  simp_rw [Finset.sum_sub_distrib]
  have h1 : ∑ i : Fin (d n), inner (𝕜 := ℝ) (stdBasisVec n i) (stdBasisVec n i) = (d n : ℝ) := by
    simp_rw [real_inner_self_eq_norm_sq, stdBasisVec_norm, one_pow]; simp
  have hi : ∀ i : Fin (d n), inner (𝕜 := ℝ) Φ (stdBasisVec n i) = Φ i := by
    intro i; simp [stdBasisVec, ← EuclideanSpace.basisFun_apply]
  simp_rw [hi]
  have h2 : ∑ i : Fin (d n), Φ i * Φ i = 1 := by
    have key := (EuclideanSpace.real_norm_sq_eq Φ).symm
    rw [hΦ, one_pow] at key
    convert key using 1; congr 1; ext i; ring
  linarith

/-- The second moment operator is (1/(d-1)) · P_perp. -/
theorem secondMoment_coeff (Φ : E n) (hΦ : ‖Φ‖ = 1) (hn : 2 ≤ d n) :
    ∀ u : E n,
      ∫ e₂, ⟪(e₂ : E n), u⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Φ) =
      (1 / ((d n : ℝ) - 1)) • P_perp Φ u := by
  obtain ⟨c, hc⟩ := secondMoment_eq_scalar_perp Φ hΦ
  intro u
  rw [hc]
  congr 1
  -- Determine c from the trace constraint: c * (d n - 1) = 1
  have hc_val : c = 1 / ((d n : ℝ) - 1) := by
    have htrace : c * ((d n : ℝ) - 1) = 1 := by
      have h1 := trace_secondMoment_eq_one Φ hΦ
      have h2 := trace_P_perp Φ hΦ
      -- Derive integrability of ⟨e₂, u⟩ • e₂ via Cauchy-Schwarz and norm-squared integrability
      have norm_sq_int : Integrable (fun e₂ : E n => ‖e₂‖ ^ 2) (perpSphereMeasure Φ) := by
        have : (fun e₂ : E n => ‖e₂‖ ^ 2) = fun e₂ => ∑ w : Fin (2 ^ n), succProb n e₂ w := by
          ext e₂; exact (sum_succProb_eq_norm_sq n e₂).symm
        rw [this]
        exact integrable_finset_sum _ (fun w _ => succProb_integrable Φ w)
      have smul_int : ∀ v : E n, Integrable (fun e₂ : E n => inner (𝕜 := ℝ) e₂ v • e₂)
          (perpSphereMeasure Φ) := by
        intro v
        apply Integrable.mono' (norm_sq_int.const_mul ‖v‖)
        · exact ((inner_integrable Φ v).aestronglyMeasurable).smul aestronglyMeasurable_id
        · filter_upwards with e₂
          rw [norm_smul]
          calc ‖inner (𝕜 := ℝ) e₂ v‖ * ‖e₂‖
              ≤ ‖e₂‖ * ‖v‖ * ‖e₂‖ := by
                  apply mul_le_mul_of_nonneg_right
                  · rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm e₂ v
                  · exact norm_nonneg _
            _ = ‖v‖ * ‖e₂‖ ^ 2 := by ring
      -- For each i, ∫ ⟨e₂, eᵢ⟩² ∂μ = c * ⟨P_perp Φ eᵢ, eᵢ⟩
      have key : ∀ i : Fin (d n),
          ∫ e₂, ⟪(e₂ : E n), stdBasisVec n i⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) =
          c * ⟪P_perp Φ (stdBasisVec n i), stdBasisVec n i⟫_ℝ := by
        intro i
        have hi := hc (stdBasisVec n i)
        have step : ⟪∫ e₂, ⟪(e₂ : E n), stdBasisVec n i⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Φ),
                      stdBasisVec n i⟫_ℝ = c * ⟪P_perp Φ (stdBasisVec n i), stdBasisVec n i⟫_ℝ := by
          rw [hi]; simp [real_inner_smul_left]
        rw [← step, real_inner_comm, ← integral_inner (smul_int _) (stdBasisVec n i)]
        congr 1; ext e₂
        simp only [real_inner_smul_right, sq, real_inner_comm (stdBasisVec n i)]
      have hsum : ∑ i : Fin (d n),
          ∫ e₂, ⟪(e₂ : E n), stdBasisVec n i⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) =
          c * ∑ i : Fin (d n), ⟪P_perp Φ (stdBasisVec n i), stdBasisVec n i⟫_ℝ := by
        simp_rw [key]; rw [← Finset.mul_sum]
      rw [hsum, h2] at h1; linarith
    have hd1 : (0 : ℝ) < (d n : ℝ) - 1 := by
      have h : 1 < d n := by
        simp only [d]
        have : 0 < 2 ^ n := pow_pos (by norm_num) n
        omega
      have : (1 : ℝ) < (d n : ℝ) := by exact_mod_cast h
      linarith
    field_simp at htrace ⊢
    linarith
  rw [hc_val]

/-! ## Decoherent floor formula -/

/-- The decoherent floor: the expected success probability when the state is
    uniform over V_perp (full decoherence limit).
    E[|⟨w|e₂⟩|²] = (2 - p_ideal)/(d - 1) -/
theorem decoherent_floor (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) (hn : 2 ≤ d n) :
    ∫ e₂, succProb n (e₂ : E n) w ∂(perpSphereMeasure Φ) =
    (2 - succProb n Φ w) / ((d n : ℝ) - 1) := by
  have hd1_ne : (d n : ℝ) - 1 ≠ 0 := by
    have : 1 < d n := by simp only [d]; have := @Nat.one_le_two_pow n; omega
    have : (1 : ℝ) < (d n : ℝ) := by exact_mod_cast this
    linarith
  -- Integrability of ‖e₂‖² (as a sum of succProb over all w)
  have norm_sq_int : Integrable (fun e₂ : E n => ‖e₂‖ ^ 2) (perpSphereMeasure Φ) := by
    have : (fun e₂ : E n => ‖e₂‖ ^ 2) = fun e₂ => ∑ w : Fin (2 ^ n), succProb n e₂ w := by
      ext e₂; exact (sum_succProb_eq_norm_sq n e₂).symm
    rw [this]
    exact integrable_finset_sum _ (fun w _ => succProb_integrable Φ w)
  -- Integrability of ⟨e₂, u⟩ • e₂ via Cauchy-Schwarz bound
  have smul_int : ∀ v : E n, Integrable (fun e₂ : E n => inner (𝕜 := ℝ) e₂ v • e₂)
      (perpSphereMeasure Φ) := by
    intro v
    apply Integrable.mono' (norm_sq_int.const_mul ‖v‖)
    · exact ((inner_integrable Φ v).aestronglyMeasurable).smul aestronglyMeasurable_id
    · filter_upwards with e₂
      rw [norm_smul]
      calc ‖inner (𝕜 := ℝ) e₂ v‖ * ‖e₂‖
          ≤ ‖e₂‖ * ‖v‖ * ‖e₂‖ := by
              apply mul_le_mul_of_nonneg_right
              · rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm e₂ v
              · exact norm_nonneg _
        _ = ‖v‖ * ‖e₂‖ ^ 2 := by ring
  -- Key lemma: ∫ ⟨e₂, û⟩² ∂μ = (1 - ⟨Φ, û⟩²)/(d-1) for unit vectors û
  have scalar : ∀ û : E n, ‖û‖ = 1 →
      ∫ e₂, ⟪(e₂ : E n), û⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) =
      (1 - ⟪Φ, û⟫_ℝ ^ 2) / ((d n : ℝ) - 1) := by
    intro û hû
    -- Express ∫ ⟨e₂, û⟩² as inner of second moment vector with û
    have lhs_eq : ∫ e₂, ⟪(e₂ : E n), û⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) =
        ⟪∫ e₂, ⟪(e₂ : E n), û⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Φ), û⟫_ℝ := by
      rw [real_inner_comm, ← integral_inner (smul_int _) û]
      congr 1; ext e₂
      simp only [real_inner_smul_right, sq, real_inner_comm û]
    rw [lhs_eq, secondMoment_coeff Φ hΦ hn û]
    simp only [real_inner_smul_left]
    rw [P_perp_apply Φ û hΦ, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hû, one_pow]
    field_simp
  -- Apply scalar to both basis vectors of succProb
  have hû₀ : ‖stdBasisVec n (succProbIdx0 n w)‖ = 1 := stdBasisVec_norm n _
  have hû₁ : ‖stdBasisVec n (succProbIdx1 n w)‖ = 1 := stdBasisVec_norm n _
  -- Integrability of each squared inner product
  have sq_int₀ : Integrable (fun e₂ : E n => inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) ^ 2)
      (perpSphereMeasure Φ) := by
    apply Integrable.mono (succProb_integrable Φ w)
    · exact (inner_integrable Φ _).aestronglyMeasurable.pow 2
    · filter_upwards with e₂
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg (succProb_nonneg n e₂ w)]
      exact le_add_of_nonneg_right (sq_nonneg _)
  have sq_int₁ : Integrable (fun e₂ : E n => inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)) ^ 2)
      (perpSphereMeasure Φ) := by
    apply Integrable.mono (succProb_integrable Φ w)
    · exact (inner_integrable Φ _).aestronglyMeasurable.pow 2
    · filter_upwards with e₂
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg (succProb_nonneg n e₂ w)]
      exact le_add_of_nonneg_left (sq_nonneg _)
  simp only [succProb]
  rw [integral_add sq_int₀ sq_int₁, scalar _ hû₀, scalar _ hû₁]
  field_simp
  ring

/-! ## TDD spot-checks -/

-- P_perp is idempotent
example (n : ℕ) (Φ : E n) (hΦ : ‖Φ‖ = 1) (v : E n) :
    P_perp Φ (P_perp Φ v) = P_perp Φ v := by
  rw [show P_perp Φ = (V_perp Φ).starProjection from rfl]
  exact congrFun (congrArg DFunLike.coe (V_perp Φ).isIdempotentElem_starProjection) v

-- For large d, decoherent floor → 1/N
-- (2 - p_ideal)/(d-1) → 1/N as d = 2N → ∞ and p_ideal → 1
example : (2 - (1:ℝ)) / (8 - 1) = 1/7 := by norm_num

end IsotropicGrover
