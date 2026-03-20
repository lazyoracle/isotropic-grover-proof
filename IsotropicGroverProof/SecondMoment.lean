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
  -- Setup: ONB of V_perp, define c as ∫ ⟨e₂, b₀⟩²
  let b := stdOrthonormalBasis ℝ ↥(V_perp Φ)
  have hVfr : 0 < Module.finrank ℝ ↥(V_perp Φ) := by
    have hd : 2 ≤ d n := by simp [d]; linarith [Nat.one_le_two_pow (n := n)]
    have horth := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := E n)
      (Submodule.span ℝ {Φ})
    have hfin : Module.finrank ℝ (E n) = d n := by simp [E]
    have hspan : Module.finrank ℝ (Submodule.span ℝ {Φ} : Submodule ℝ (E n)) ≤ 1 :=
      (finrank_span_le_card ({Φ} : Set (E n))).trans (by simp)
    change 0 < Module.finrank ℝ ↥(Submodule.span ℝ {Φ} : Submodule ℝ (E n))ᗮ
    have h2 : Module.finrank ℝ ↥(Submodule.span ℝ {Φ} : Submodule ℝ (E n)) +
              Module.finrank ℝ ↥(Submodule.span ℝ {Φ} : Submodule ℝ (E n))ᗮ = d n := by
      linarith [horth]
    omega
  let i₀ : Fin (Module.finrank ℝ ↥(V_perp Φ)) := ⟨0, hVfr⟩
  use ∫ e₂, ⟪e₂, ((b i₀ : ↥(V_perp Φ)) : E n)⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ)
  set c := ∫ e₂, ⟪e₂, ((b i₀ : ↥(V_perp Φ)) : E n)⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) with hc_def
  -- Integrability helpers
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
  -- Product integrability helper
  have prod_int : ∀ (y z : E n),
      Integrable (fun e₂ : E n => ⟪e₂, y⟫_ℝ * ⟪e₂, z⟫_ℝ) (perpSphereMeasure Φ) := by
    intro y z
    apply Integrable.mono' (norm_sq_int.const_mul (‖y‖ * ‖z‖))
    · exact ((inner_integrable Φ y).aestronglyMeasurable.mul
        (inner_integrable Φ z).aestronglyMeasurable)
    · filter_upwards with e₂
      rw [Real.norm_eq_abs, abs_mul]
      calc |⟪e₂, y⟫_ℝ| * |⟪e₂, z⟫_ℝ|
          ≤ (‖e₂‖ * ‖y‖) * (‖e₂‖ * ‖z‖) := by
            apply mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
              (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = (‖y‖ * ‖z‖) * ‖e₂‖ ^ 2 := by ring
  intro u
  -- Show equality via ext_inner_right: suffices ∀ w, ⟪LHS, w⟫ = ⟪RHS, w⟫
  apply ext_inner_right ℝ
  intro w
  -- RHS: ⟪c • P_perp Φ u, w⟫ = c * ⟪P_perp Φ u, w⟫
  rw [real_inner_smul_left]
  -- LHS: ⟪∫ ⟨e₂, u⟩ e₂, w⟫ = ∫ ⟨e₂, u⟩⟨e₂, w⟩
  have lhs_rw : ⟪∫ e₂, ⟪(e₂ : E n), u⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Φ), w⟫_ℝ =
      ∫ e₂, ⟪(e₂ : E n), u⟫_ℝ * ⟪(e₂ : E n), w⟫_ℝ ∂(perpSphereMeasure Φ) := by
    rw [real_inner_comm, ← integral_inner (smul_int u) w]
    congr 1; ext e₂
    rw [real_inner_smul_right, real_inner_comm w]
  rw [lhs_rw]
  -- Goal: ∫ ⟨e₂, u⟩⟨e₂, w⟩ dμ = c * ⟪P_perp Φ u, w⟫
  -- Step: use a.e. membership to replace u → P_perp u and w → P_perp w
  -- Since e₂ ∈ V_perp a.e., ⟪e₂, u⟫ = ⟪e₂, P_perp u⟫ a.e.
  have ae_u : ∀ᵐ e₂ ∂(perpSphereMeasure Φ),
      ⟪e₂, u⟫_ℝ = ⟪e₂, P_perp Φ u⟫_ℝ := by
    filter_upwards [perpSphereMeasure_norm_ae Φ] with e₂ ⟨he₂_mem, _⟩
    rw [P_perp_apply Φ u hΦ, inner_sub_right, inner_smul_right]
    have : ⟪e₂, Φ⟫_ℝ = 0 := by
      rw [real_inner_comm]; exact (mem_V_perp_iff Φ e₂).mp he₂_mem
    simp [this]
  have ae_w : ∀ᵐ e₂ ∂(perpSphereMeasure Φ),
      ⟪e₂, w⟫_ℝ = ⟪e₂, P_perp Φ w⟫_ℝ := by
    filter_upwards [perpSphereMeasure_norm_ae Φ] with e₂ ⟨he₂_mem, _⟩
    rw [P_perp_apply Φ w hΦ, inner_sub_right, inner_smul_right]
    have : ⟪e₂, Φ⟫_ℝ = 0 := by
      rw [real_inner_comm]; exact (mem_V_perp_iff Φ e₂).mp he₂_mem
    simp [this]
  rw [integral_congr_ae (by filter_upwards [ae_u, ae_w] with e₂ hu hw; rw [hu, hw])]
  -- Now goal: ∫ ⟨e₂, P_perp u⟩⟨e₂, P_perp w⟩ dμ = c * ⟪P_perp u, w⟫
  -- P_perp u ∈ V_perp and P_perp w ∈ V_perp. Also ⟪P_perp u, w⟫ = ⟪P_perp u, P_perp w⟫
  have hPu_mem : P_perp Φ u ∈ V_perp Φ := by
    rw [mem_V_perp_iff, P_perp_apply Φ u hΦ, inner_sub_right, inner_smul_right,
        real_inner_self_eq_norm_sq, hΦ, one_pow, mul_one, sub_self]
  have hPw_mem : P_perp Φ w ∈ V_perp Φ := by
    rw [mem_V_perp_iff, P_perp_apply Φ w hΦ, inner_sub_right, inner_smul_right,
        real_inner_self_eq_norm_sq, hΦ, one_pow, mul_one, sub_self]
  -- ⟪P_perp u, w⟫ = ⟪P_perp u, P_perp w⟫ (since P_perp is self-adjoint/idempotent)
  have inner_Pu_w : ⟪P_perp Φ u, w⟫_ℝ = ⟪P_perp Φ u, P_perp Φ w⟫_ℝ := by
    rw [P_perp_apply Φ w hΦ, inner_sub_right, inner_smul_right]
    have : ⟪P_perp Φ u, Φ⟫_ℝ = 0 := by
      rw [real_inner_comm]; exact (mem_V_perp_iff Φ _).mp hPu_mem
    simp [this]
  rw [inner_Pu_w]
  -- Now goal: ∫ ⟨e₂, P_perp u⟩⟨e₂, P_perp w⟩ dμ = c * ⟪P_perp u, P_perp w⟫
  -- Lift P_perp u and P_perp w to elements of V_perp
  set u' := P_perp Φ u with hu'_def
  set w' := P_perp Φ w with hw'_def
  -- Lift to V_perp subtypes
  let uV : ↥(V_perp Φ) := ⟨u', hPu_mem⟩
  let wV : ↥(V_perp Φ) := ⟨w', hPw_mem⟩
  -- Expand u' and w' in the ONB b of V_perp
  -- u' = ∑ i, ⟪b i, uV⟫ • (b i : E n) (using OrthonormalBasis.sum_repr')
  have hu'_expand : u' = ∑ i, ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ • ((b i : ↥(V_perp Φ)) : E n) := by
    have h := b.sum_repr' uV
    -- h : ∑ i, ⟪b i, uV⟫ • b i = uV
    -- Coerce both sides to E n
    change u' = _
    conv_lhs => rw [show u' = (uV : E n) from rfl, ← congrArg Subtype.val h]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_inner]
  -- Similarly for w'
  have hw'_expand : w' = ∑ j, ⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ • ((b j : ↥(V_perp Φ)) : E n) := by
    have h := b.sum_repr' wV
    change w' = _
    conv_lhs => rw [show w' = (wV : E n) from rfl, ← congrArg Subtype.val h]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Submodule.coe_inner]
  -- Rewrite inner products using ONB expansion
  -- ⟪e₂, u'⟫ = ∑ i, ⟪b i, uV⟫ * ⟪e₂, b i⟫
  have inner_u'_expand : ∀ e₂ : E n,
      ⟪e₂, u'⟫_ℝ = ∑ i, ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ := by
    intro e₂; rw [hu'_expand, inner_sum]; congr 1; ext i; rw [inner_smul_right]
  have inner_w'_expand : ∀ e₂ : E n,
      ⟪e₂, w'⟫_ℝ = ∑ j, ⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ * ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ := by
    intro e₂; rw [hw'_expand, inner_sum]; congr 1; ext j; rw [inner_smul_right]
  -- Rewrite the integrand (only on LHS to avoid rewriting RHS ⟪u', w'⟫)
  have integrand_rw : ∀ e₂ : E n,
      ⟪e₂, u'⟫_ℝ * ⟪e₂, w'⟫_ℝ =
      ∑ i, ∑ j, (⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ) *
        (⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ * ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ) := by
    intro e₂; rw [inner_u'_expand, inner_w'_expand, Finset.sum_mul_sum]
  simp_rw [integrand_rw]
  -- ∫ ∑ᵢ ∑ⱼ aᵢ bⱼ ⟨e₂, bᵢ⟩ ⟨e₂, bⱼ⟩ = ∑ᵢ ∑ⱼ aᵢ bⱼ ∫ ⟨e₂, bᵢ⟩ ⟨e₂, bⱼ⟩
  -- Exchange integral and sum
  rw [integral_finset_sum _ (fun i _ => ?_)]
  · -- After exchange, use off-diagonal vanishing and diagonal equality
    -- ∑ᵢ ∑ⱼ aᵢ bⱼ ∫ ⟨e₂, bᵢ⟩⟨e₂, bⱼ⟩ = ∑ᵢ aᵢ bᵢ * c (diagonal only)
    -- First: the inner product ⟪P_perp u, P_perp w⟫ via ONB
    have inner_onb : ⟪u', w'⟫_ℝ = ∑ i, ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪(b i : ↥(V_perp Φ)), wV⟫_ℝ := by
      have h := b.sum_inner_mul_inner (𝕜 := ℝ) uV wV
      simp only [Submodule.coe_inner] at h ⊢
      rw [← h]
      congr 1; ext i; rw [real_inner_comm]
    rw [inner_onb, Finset.mul_sum]
    congr 1; ext i
    rw [integral_finset_sum _ (fun j _ => ?_)]
    · -- For each (i,j): ∫ aᵢ bⱼ ⟨e₂, bᵢ⟩⟨e₂, bⱼ⟩ = aᵢ bⱼ ∫ ⟨e₂, bᵢ⟩⟨e₂, bⱼ⟩
      -- Use integral_perpSphere_inner_mul_ortho for i ≠ j, integral_perpSphere_inner_sq_eq for i = j
      -- Split into diagonal and off-diagonal
      -- ∑ⱼ aᵢ bⱼ ∫ ⟨e₂, bᵢ⟩⟨e₂, bⱼ⟩ = aᵢ bᵢ * ∫ ⟨e₂, bᵢ⟩² + ∑_{j≠i} aᵢ bⱼ * 0
      -- Pull constant factors out of the integral
      have pull_const : ∀ j,
          ∫ e₂, ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
            (⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ * ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ) ∂(perpSphereMeasure Φ) =
          ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ *
            ∫ e₂, ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ * ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ ∂(perpSphereMeasure Φ) := by
        intro j
        rw [show (fun e₂ => ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
              (⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ * ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)) =
            (fun e₂ => (⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ) *
              (⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ * ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)) from by ext; ring]
        rw [integral_const_mul]
      simp_rw [pull_const]
      -- For j ≠ i: ∫ ⟨e₂, bᵢ⟩⟨e₂, bⱼ⟩ = 0
      -- For j = i: ∫ ⟨e₂, bᵢ⟩⟨e₂, bᵢ⟩ = ∫ ⟨e₂, bᵢ⟩² = c
      have ortho : ∀ j, i ≠ j →
          ∫ e₂, ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ * ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ
            ∂(perpSphereMeasure Φ) = 0 := by
        intro j hij
        exact integral_perpSphere_inner_mul_ortho Φ (b i) (b j)
          (by rw [← Submodule.coe_inner]; exact b.orthonormal.2 hij)
      have diag : ∫ e₂, ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
          ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ ∂(perpSphereMeasure Φ) = c := by
        have hmul_sq : ∀ e₂ : E n, ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
            ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ = ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ ^ 2 := by
          intro e₂; ring
        simp_rw [hmul_sq]
        exact integral_perpSphere_inner_sq_eq Φ (b i) (b i₀)
          (by rw [Submodule.norm_coe]; exact b.orthonormal.1 i)
          (by rw [Submodule.norm_coe]; exact b.orthonormal.1 i₀)
      -- Use Finset.sum_eq_single to isolate diagonal term
      rw [Finset.sum_eq_single i]
      · rw [diag]; ring
      · intro j _ hij
        rw [ortho j (Ne.symm hij), mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · -- Integrability of the inner summand for each j
      have hrw : (fun a => ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪a, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
          (⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ * ⟪a, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)) =
        (fun a => (⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ) *
          (⟪a, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ * ⟪a, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)) := by ext; ring
      rw [hrw]; exact (prod_int _ _).const_mul _
  · -- Integrability of the outer summand for each i (a sum over j)
    apply integrable_finset_sum; intro j _
    have hrw : (fun a => ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪a, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
        (⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ * ⟪a, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)) =
      (fun a => (⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ) *
        (⟪a, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ * ⟪a, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)) := by ext; ring
    rw [hrw]; exact (prod_int _ _).const_mul _

/-- The trace of the second moment operator equals 1 (since ‖e₂‖ = 1 a.s.). -/
lemma trace_secondMoment_eq_one (Φ : E n) (_hΦ : ‖Φ‖ = 1) :
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
theorem secondMoment_coeff (Φ : E n) (hΦ : ‖Φ‖ = 1) (_hn : 2 ≤ d n) :
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
  have sq_int₀ : Integrable (fun e₂ : E n =>
      inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx0 n w)) ^ 2)
      (perpSphereMeasure Φ) := by
    apply Integrable.mono (succProb_integrable Φ w)
    · exact (inner_integrable Φ _).aestronglyMeasurable.pow 2
    · filter_upwards with e₂
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg (succProb_nonneg n e₂ w)]
      exact le_add_of_nonneg_right (sq_nonneg _)
  have sq_int₁ : Integrable (fun e₂ : E n =>
      inner (𝕜 := ℝ) e₂ (stdBasisVec n (succProbIdx1 n w)) ^ 2)
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
example (n : ℕ) (Φ : E n) (_ : ‖Φ‖ = 1) (v : E n) :
    P_perp Φ (P_perp Φ v) = P_perp Φ v := by
  rw [show P_perp Φ = (V_perp Φ).starProjection from rfl]
  exact congrFun (congrArg DFunLike.coe (V_perp Φ).isIdempotentElem_starProjection) v

-- For large d, decoherent floor → 1/N
-- (2 - p_ideal)/(d-1) → 1/N as d = 2N → ∞ and p_ideal → 1
example : (2 - (1:ℝ)) / (8 - 1) = 1/7 := by norm_num

end IsotropicGrover
