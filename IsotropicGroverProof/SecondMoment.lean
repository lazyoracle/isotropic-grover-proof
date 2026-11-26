-- IsotropicGroverProof/SecondMoment.lean
-- Equatorial second-moment operator E[e₂ e₂ᵀ] = P_{V⊥} / (d - 1), the decoherent floor
-- formula (2 - p_ideal) / (d - 1), and the general bilinear second-moment identity
-- isotropicError_bilinear_secondMoment across σ ∈ [0, 1].

import Mathlib.MeasureTheory.Function.L2Space
import IsotropicGroverProof.CrossTerm

/-!
# Second Moment on the Perpendicular Sphere

Proves `E[e₂ e₂ᵀ] = P_{V⊥} / (d - 1)` by orthogonal invariance and trace normalization,
derives the decoherent floor `E[|⟨w|e₂⟩|²] = (2 - p_ideal) / (d - 1)`, and establishes the
general bilinear second-moment identity `isotropicError_bilinear_secondMoment` on `σ ∈ [0, 1]`.
-/

namespace IsotropicGrover

open MeasureTheory InnerProductSpace ContinuousLinearMap Real

variable {n : ℕ}

/-! ## Orthogonal projector onto V_perp -/

/-- The orthogonal projector onto V_perp(Φ) = (ℝ · Φ)^⊥. -/
noncomputable def P_perp (Φ : E n) : E n →L[ℝ] E n :=
  (V_perp Φ).starProjection

/-- P_perp acts as the identity minus projection onto Φ:
    P_perp Φ v = v - ⟪Φ, v⟫ · Φ (when ‖Φ‖ = 1). -/
lemma P_perp_apply (Φ v : E n) (hΦ : ‖Φ‖ = 1) :
    P_perp Φ v = v - ⟪Φ, v⟫_ℝ • Φ := by
  simp only [P_perp, V_perp]
  rw [Submodule.starProjection_orthogonal_val]
  congr 1
  exact Submodule.starProjection_unit_singleton (𝕜 := ℝ) hΦ v

/-! ## Second moment matrix = (1/(d-1)) · P_perp -/

private lemma perpSphere_smul_integrable (Ψ u : E n) :
    Integrable (fun e₂ : E n => ⟪e₂, u⟫_ℝ • e₂) (perpSphereMeasure Ψ) := by
  apply Integrable.mono' (integrable_const ‖u‖)
  · exact ((inner_integrable Ψ u).aestronglyMeasurable).smul aestronglyMeasurable_id
  · filter_upwards [perpSphereMeasure_norm_ae Ψ] with e₂ ⟨_, he₂⟩
    rw [norm_smul, Real.norm_eq_abs, he₂, mul_one]
    exact le_trans (abs_real_inner_le_norm e₂ u) (by rw [he₂, one_mul])

private lemma perpSphere_inner_mul_integrable (Ψ u v : E n) :
    Integrable (fun e₂ : E n => ⟪e₂, u⟫_ℝ * ⟪e₂, v⟫_ℝ) (perpSphereMeasure Ψ) := by
  apply Integrable.mono' (integrable_const (‖u‖ * ‖v‖))
  · exact (inner_integrable Ψ u).aestronglyMeasurable.mul
      (inner_integrable Ψ v).aestronglyMeasurable
  · filter_upwards [perpSphereMeasure_norm_ae Ψ] with e₂ ⟨_, he₂⟩
    rw [Real.norm_eq_abs, abs_mul]
    calc |⟪e₂, u⟫_ℝ| * |⟪e₂, v⟫_ℝ|
        ≤ (‖e₂‖ * ‖u‖) * (‖e₂‖ * ‖v‖) :=
          mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
            (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖u‖ * ‖v‖ := by rw [he₂]; ring

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
  let i₀ : Fin (Module.finrank ℝ ↥(V_perp Φ)) := ⟨0, V_perp_finrank_pos Φ⟩
  use ∫ e₂, ⟪e₂, ((b i₀ : ↥(V_perp Φ)) : E n)⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ)
  set c := ∫ e₂, ⟪e₂, ((b i₀ : ↥(V_perp Φ)) : E n)⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) with hc_def
  intro u
  -- Show equality via ext_inner_right: suffices ∀ w, ⟪LHS, w⟫ = ⟪RHS, w⟫
  apply ext_inner_right ℝ
  intro w
  -- RHS: ⟪c • P_perp Φ u, w⟫ = c * ⟪P_perp Φ u, w⟫
  rw [real_inner_smul_left]
  -- LHS: ⟪∫ ⟨e₂, u⟩ e₂, w⟫ = ∫ ⟨e₂, u⟩⟨e₂, w⟩
  have lhs_rw : ⟪∫ e₂, ⟪(e₂ : E n), u⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Φ), w⟫_ℝ =
      ∫ e₂, ⟪(e₂ : E n), u⟫_ℝ * ⟪(e₂ : E n), w⟫_ℝ ∂(perpSphereMeasure Φ) := by
    rw [real_inner_comm, ← integral_inner (perpSphere_smul_integrable Φ u) w]
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
  rw [integral_finsetSum _ (fun i _ => ?_)]
  · -- After exchange, use off-diagonal vanishing and diagonal equality
    -- ∑ᵢ ∑ⱼ aᵢ bⱼ ∫ ⟨e₂, bᵢ⟩⟨e₂, bⱼ⟩ = ∑ᵢ aᵢ bᵢ * c (diagonal only)
    -- First: the inner product ⟪P_perp u, P_perp w⟫ via ONB
    have inner_onb : ⟪u', w'⟫_ℝ =
        ∑ i, ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪(b i : ↥(V_perp Φ)), wV⟫_ℝ := by
      have h := b.sum_inner_mul_inner (𝕜 := ℝ) uV wV
      simp only [Submodule.coe_inner] at h ⊢
      rw [← h]
      congr 1; ext i; rw [real_inner_comm]
    rw [inner_onb, Finset.mul_sum]
    congr 1; ext i
    rw [integral_finsetSum _ (fun j _ => ?_)]
    · -- For each (i,j): ∫ aᵢ bⱼ ⟨e₂, bᵢ⟩⟨e₂, bⱼ⟩ =
      --   aᵢ bⱼ ∫ ⟨e₂, bᵢ⟩⟨e₂, bⱼ⟩
      -- Use integral_perpSphere_inner_mul_ortho for i ≠ j,
      --   integral_perpSphere_inner_sq_eq for i = j
      -- Split into diagonal and off-diagonal
      -- ∑ⱼ aᵢ bⱼ ∫ ⟨e₂, bᵢ⟩⟨e₂, bⱼ⟩ = aᵢ bᵢ * ∫ ⟨e₂, bᵢ⟩² + ∑_{j≠i} aᵢ bⱼ * 0
      -- Pull constant factors out of the integral
      have pull_const : ∀ j,
          ∫ e₂, ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
            (⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ *
              ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)
            ∂(perpSphereMeasure Φ) =
          ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ *
            ⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ *
            ∫ e₂, ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
              ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ
            ∂(perpSphereMeasure Φ) := by
        intro j
        rw [show (fun e₂ => ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
              (⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ * ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)) =
            (fun e₂ => (⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ) *
              (⟪e₂, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
                ⟪e₂, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ))
            from by ext; ring]
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
      rw [hrw]; exact (perpSphere_inner_mul_integrable Φ _ _).const_mul _
  · -- Integrability of the outer summand for each i (a sum over j)
    apply integrable_finsetSum; intro j _
    have hrw : (fun a => ⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪a, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ *
        (⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ * ⟪a, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)) =
      (fun a => (⟪(b i : ↥(V_perp Φ)), uV⟫_ℝ * ⟪(b j : ↥(V_perp Φ)), wV⟫_ℝ) *
        (⟪a, ((b i : ↥(V_perp Φ)) : E n)⟫_ℝ * ⟪a, ((b j : ↥(V_perp Φ)) : E n)⟫_ℝ)) := by ext; ring
    rw [hrw]; exact (perpSphere_inner_mul_integrable Φ _ _).const_mul _

/-- The trace of the second moment operator equals 1 (since ‖e₂‖ = 1 a.s.). -/
lemma trace_secondMoment_eq_one (Φ : E n) (_hΦ : ‖Φ‖ = 1) :
    ∑ i : Fin (d n),
      ∫ e₂, ⟪(e₂ : E n), stdBasisVec n i⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) = 1 := by
  have hint : ∀ i : Fin (d n),
      Integrable (fun e₂ : E n => ⟪e₂, stdBasisVec n i⟫_ℝ ^ 2) (perpSphereMeasure Φ) := fun i => by
    simpa only [sq] using perpSphere_inner_mul_integrable Φ (stdBasisVec n i) (stdBasisVec n i)
  rw [← integral_finsetSum Finset.univ (fun i _ => hint i)]
  have hae : ∀ᵐ e₂ ∂(perpSphereMeasure Φ),
      ∑ i : Fin (d n), ⟪e₂, stdBasisVec n i⟫_ℝ ^ 2 = 1 := by
    filter_upwards [perpSphereMeasure_norm_ae Φ] with e₂ ⟨_, he₂⟩
    simp_rw [inner_stdBasisVec_eq_apply, ← EuclideanSpace.real_norm_sq_eq, he₂, one_pow]
  rw [integral_congr_ae hae, integral_const]
  simp [Measure.real]

/-- The trace of P_perp equals d - 1 (the dimension of V_perp). -/
lemma trace_P_perp (Φ : E n) (hΦ : ‖Φ‖ = 1) :
    ∑ i : Fin (d n), ⟪P_perp Φ (stdBasisVec n i), stdBasisVec n i⟫_ℝ = d n - 1 := by
  simp_rw [P_perp_apply Φ _ hΦ, inner_sub_left, real_inner_smul_left, Finset.sum_sub_distrib,
    real_inner_self_eq_norm_sq, stdBasisVec_norm, one_pow, inner_stdBasisVec_eq_apply, ← sq]
  have hnorm := (EuclideanSpace.real_norm_sq_eq Φ).symm
  rw [hΦ, one_pow] at hnorm
  simp [hnorm]

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
      -- For each i, ∫ ⟨e₂, eᵢ⟩² ∂μ = c * ⟨P_perp Φ eᵢ, eᵢ⟩
      have key : ∀ i : Fin (d n),
          ∫ e₂, ⟪(e₂ : E n), stdBasisVec n i⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) =
          c * ⟪P_perp Φ (stdBasisVec n i), stdBasisVec n i⟫_ℝ := by
        intro i
        have hi := hc (stdBasisVec n i)
        have step : ⟪∫ e₂, ⟪(e₂ : E n), stdBasisVec n i⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Φ),
                      stdBasisVec n i⟫_ℝ = c * ⟪P_perp Φ (stdBasisVec n i), stdBasisVec n i⟫_ℝ := by
          rw [hi]; simp [real_inner_smul_left]
        rw [← step, real_inner_comm,
            ← integral_inner (perpSphere_smul_integrable Φ _) (stdBasisVec n i)]
        congr 1; ext e₂
        simp only [real_inner_smul_right, sq, real_inner_comm (stdBasisVec n i)]
      have hsum : ∑ i : Fin (d n),
          ∫ e₂, ⟪(e₂ : E n), stdBasisVec n i⟫_ℝ ^ 2 ∂(perpSphereMeasure Φ) =
          c * ∑ i : Fin (d n), ⟪P_perp Φ (stdBasisVec n i), stdBasisVec n i⟫_ℝ := by
        simp_rw [key]; rw [← Finset.mul_sum]
      rw [hsum, h2] at h1; linarith
    have hd1 := cast_d_sub_one_pos n
    field_simp at htrace ⊢
    linarith
  rw [hc_val]

/-! ## Bilinear expectation on `perpSphereMeasure` and decoherent floor -/

/-- Bilinear expectation of inner products over `perpSphereMeasure Ψ`:
    `∫ e₂, ⟪e₂, u⟫ ⟪e₂, v⟫ = (⟪u, v⟫ - ⟪Ψ, u⟫ ⟪Ψ, v⟫) / (d n - 1)`. -/
theorem perpSphere_inner_mul_inner (Ψ : E n) (hΨ : ‖Ψ‖ = 1) (u v : E n) :
    ∫ e₂, ⟪e₂, u⟫_ℝ * ⟪e₂, v⟫_ℝ ∂(perpSphereMeasure Ψ) =
    (⟪u, v⟫_ℝ - ⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) / ((d n : ℝ) - 1) := by
  have lhs_eq : ∫ e₂, ⟪e₂, u⟫_ℝ * ⟪e₂, v⟫_ℝ ∂(perpSphereMeasure Ψ) =
      ⟪∫ e₂, ⟪(e₂ : E n), u⟫_ℝ • (e₂ : E n) ∂(perpSphereMeasure Ψ), v⟫_ℝ := by
    rw [real_inner_comm, ← integral_inner (perpSphere_smul_integrable Ψ u) v]
    congr 1; ext e₂
    rw [real_inner_smul_right, real_inner_comm v]
  rw [lhs_eq, secondMoment_coeff Ψ hΨ (two_le_d n) u, real_inner_smul_left,
      P_perp_apply Ψ u hΨ, inner_sub_left, real_inner_smul_left]
  ring

/-- The decoherent floor: the expected success probability when the state is
    uniform over V_perp (full decoherence limit).
    E[|⟨w|e₂⟩|²] = (2 - p_ideal)/(d - 1) -/
theorem decoherent_floor (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) (_hn : 2 ≤ d n) :
    ∫ e₂, succProb n (e₂ : E n) w ∂(perpSphereMeasure Φ) =
    (2 - succProb n Φ w) / ((d n : ℝ) - 1) := by
  set e₀ := stdBasisVec n (succProbIdx0 n w)
  set e₁ := stdBasisVec n (succProbIdx1 n w)
  have hsq₀ : Integrable (fun e₂ : E n => ⟪e₂, e₀⟫_ℝ ^ 2) (perpSphereMeasure Φ) := by
    simpa only [sq] using perpSphere_inner_mul_integrable Φ e₀ e₀
  have hsq₁ : Integrable (fun e₂ : E n => ⟪e₂, e₁⟫_ℝ ^ 2) (perpSphereMeasure Φ) := by
    simpa only [sq] using perpSphere_inner_mul_integrable Φ e₁ e₁
  have he₀ : ⟪e₀, e₀⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, stdBasisVec_norm, one_pow]
  have he₁ : ⟪e₁, e₁⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, stdBasisVec_norm, one_pow]
  simp only [succProb]
  rw [integral_add hsq₀ hsq₁]
  simp_rw [sq]
  rw [perpSphere_inner_mul_inner Φ hΦ e₀ e₀, perpSphere_inner_mul_inner Φ hΦ e₁ e₁, he₀, he₁]
  ring

/-! ## General bilinear second-moment identity on `[0, 1]` -/

private lemma isotropicError_bilinear_expand (Ψ e₂ u v : E n) (θ : ℝ) :
    ⟪isotropicError Ψ e₂ θ, u⟫_ℝ * ⟪isotropicError Ψ e₂ θ, v⟫_ℝ =
    cos θ ^ 2 * (⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) +
    ((cos θ * sin θ * ⟪Ψ, u⟫_ℝ) * ⟪e₂, v⟫_ℝ +
     (cos θ * sin θ * ⟪Ψ, v⟫_ℝ) * ⟪e₂, u⟫_ℝ) +
    sin θ ^ 2 * (⟪e₂, u⟫_ℝ * ⟪e₂, v⟫_ℝ) := by
  simp only [isotropicError, inner_add_left, real_inner_smul_left]
  ring

private lemma isotropicError_inner_mul_integrable (Ψ u v : E n) (θ : ℝ) :
    Integrable (fun e₂ : E n =>
      ⟪isotropicError Ψ e₂ θ, u⟫_ℝ * ⟪isotropicError Ψ e₂ θ, v⟫_ℝ) (perpSphereMeasure Ψ) := by
  simp_rw [isotropicError_bilinear_expand]
  exact ((integrable_const _).fun_add
    (((inner_integrable Ψ v).const_mul _).fun_add ((inner_integrable Ψ u).const_mul _))).fun_add
    ((perpSphere_inner_mul_integrable Ψ u v).const_mul _)

private lemma integral_e₂_bilinear (Ψ : E n) (hΨ : ‖Ψ‖ = 1) (u v : E n) (θ : ℝ) :
    ∫ e₂, ⟪isotropicError Ψ e₂ θ, u⟫_ℝ * ⟪isotropicError Ψ e₂ θ, v⟫_ℝ
      ∂(perpSphereMeasure Ψ) =
    cos θ ^ 2 * (⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) +
    sin θ ^ 2 * ((⟪u, v⟫_ℝ - ⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) / ((d n : ℝ) - 1)) := by
  have hf1 : Integrable (fun _ : E n => cos θ ^ 2 * (⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ))
      (perpSphereMeasure Ψ) := integrable_const _
  have hf2a := (inner_integrable Ψ v).const_mul (cos θ * sin θ * ⟪Ψ, u⟫_ℝ)
  have hf2b := (inner_integrable Ψ u).const_mul (cos θ * sin θ * ⟪Ψ, v⟫_ℝ)
  have hf3 := (perpSphere_inner_mul_integrable Ψ u v).const_mul (sin θ ^ 2)
  simp_rw [isotropicError_bilinear_expand]
  rw [integral_add (hf1.fun_add (hf2a.fun_add hf2b)) hf3,
      integral_add hf1 (hf2a.fun_add hf2b), integral_add hf2a hf2b,
      integral_const, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_perp_inner_eq_zero Ψ v, integral_perp_inner_eq_zero Ψ u,
      perpSphere_inner_mul_inner Ψ hΨ u v]
  simp

/-- **General bilinear second-moment identity** for a single isotropic sphere error step
    with parameter `σ ∈ [0, 1]`, unit vector `‖Ψ‖ = 1`, and arbitrary vectors `u, v : E n`. -/
theorem isotropicError_bilinear_secondMoment (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (Ψ : E n) (hΨ : ‖Ψ‖ = 1) (u v : E n) :
    ∫ θ, ∫ e₂, ⟪isotropicError Ψ e₂ θ, u⟫_ℝ * ⟪isotropicError Ψ e₂ θ, v⟫_ℝ
          ∂(perpSphereMeasure Ψ) ∂(poissonAngleMeasure (d n) σ) =
    σ ^ 2 * (⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) + (1 - σ ^ 2) / (d n : ℝ) * ⟪u, v⟫_ℝ := by
  set μ := poissonAngleMeasure (d n) σ
  have : IsProbabilityMeasure μ := poissonAngleMeasure_d_isProbMeasure n σ hσ
  simp_rw [integral_e₂_bilinear Ψ hΨ u v]
  rw [integral_add (cos_sq_integrable_prob.mul_const _) (sin_sq_integrable_prob.mul_const _),
      integral_mul_const, integral_mul_const,
      integral_sin_sq_eq_one_sub_integral_cos_sq,
      poissonAngleMeasure_cos_sq (d n) σ hσ (two_le_d n)]
  have hd_ne := cast_d_ne_zero n
  have hd1_ne := cast_d_sub_one_ne_zero n
  field_simp [hd_ne, hd1_ne]
  ring

/-- Single-step expected success probability under `poissonAngleMeasure (d n) σ` for all
    `σ ∈ [0, 1]`, derived directly as a corollary of `isotropicError_bilinear_secondMoment`. -/
theorem isotropicError_succProb_oneStep (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (Ψ : E n) (hΨ : ‖Ψ‖ = 1) (w : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, succProb n (isotropicError Ψ e₂ θ) w
          ∂(perpSphereMeasure Ψ) ∂(poissonAngleMeasure (d n) σ) =
    σ ^ 2 * succProb n Ψ w + (1 - σ ^ 2) / (2 ^ n : ℝ) := by
  set μ := poissonAngleMeasure (d n) σ
  have : IsProbabilityMeasure μ := poissonAngleMeasure_d_isProbMeasure n σ hσ
  set e₀ := stdBasisVec n (succProbIdx0 n w)
  set e₁ := stdBasisVec n (succProbIdx1 n w)
  have hinner : ∀ θ : ℝ,
      ∫ e₂, succProb n (isotropicError Ψ e₂ θ) w ∂(perpSphereMeasure Ψ) =
      (∫ e₂, ⟪isotropicError Ψ e₂ θ, e₀⟫_ℝ * ⟪isotropicError Ψ e₂ θ, e₀⟫_ℝ
        ∂(perpSphereMeasure Ψ)) +
      (∫ e₂, ⟪isotropicError Ψ e₂ θ, e₁⟫_ℝ * ⟪isotropicError Ψ e₂ θ, e₁⟫_ℝ
        ∂(perpSphereMeasure Ψ)) := by
    intro θ
    simp only [succProb, sq]
    exact integral_add (isotropicError_inner_mul_integrable Ψ e₀ e₀ θ)
      (isotropicError_inner_mul_integrable Ψ e₁ e₁ θ)
  have hint_θ : ∀ u : E n,
      Integrable (fun θ => ∫ e₂, ⟪isotropicError Ψ e₂ θ, u⟫_ℝ * ⟪isotropicError Ψ e₂ θ, u⟫_ℝ
        ∂(perpSphereMeasure Ψ)) μ := by
    intro u
    simp_rw [integral_e₂_bilinear Ψ hΨ u u]
    exact (cos_sq_integrable_prob.mul_const _).add (sin_sq_integrable_prob.mul_const _)
  simp_rw [hinner]
  rw [integral_add (hint_θ e₀) (hint_θ e₁),
      isotropicError_bilinear_secondMoment σ hσ Ψ hΨ e₀ e₀,
      isotropicError_bilinear_secondMoment σ hσ Ψ hΨ e₁ e₁]
  have he₀ : ⟪e₀, e₀⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, stdBasisVec_norm, one_pow]
  have he₁ : ⟪e₁, e₁⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, stdBasisVec_norm, one_pow]
  have hN_ne : (2 ^ n : ℝ) ≠ 0 := by positivity
  simp only [succProb, sq, he₀, he₁, cast_d n]
  field_simp [hN_ne]
  ring

/-! ## TDD spot-checks -/

-- P_perp is idempotent
example (n : ℕ) (Φ : E n) (_ : ‖Φ‖ = 1) (v : E n) :
    P_perp Φ (P_perp Φ v) = P_perp Φ v :=
  congrFun (congrArg DFunLike.coe (V_perp Φ).isIdempotentElem_starProjection) v

-- For large d, decoherent floor → 1/N
-- (2 - p_ideal)/(d-1) → 1/N as d = 2N → ∞ and p_ideal → 1
example : (2 - (1:ℝ)) / (8 - 1) = 1/7 := by norm_num

#check @perpSphere_inner_mul_inner
#check @isotropicError_bilinear_secondMoment
#check @isotropicError_succProb_oneStep

/--
info: 'IsotropicGrover.decoherent_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms decoherent_floor

/--
info: 'IsotropicGrover.perpSphere_inner_mul_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms perpSphere_inner_mul_inner

/--
info: 'IsotropicGrover.isotropicError_bilinear_secondMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isotropicError_bilinear_secondMoment

/--
info: 'IsotropicGrover.isotropicError_succProb_oneStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isotropicError_succProb_oneStep

end IsotropicGrover
