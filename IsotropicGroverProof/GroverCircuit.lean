-- IsotropicGroverProof/GroverCircuit.lean
-- M9: Grover circuit state vectors and specialization of isotropicGrover_main.
--
-- Formalizes:
-- 1. The target basis state |w⟩ and its success probability (1).
-- 2. The non-target orthogonal superposition |w^⟂⟩ and its orthogonality to |w⟩.
-- 3. The uniform superposition state |s⟩, proving ‖|s⟩‖ = 1 and succProb = 1/2^n,
--    and showing its expected success probability under isotropic noise is identically 1/2^n.
-- 4. The 2D Grover search plane spanned by |w⟩ and |w^⟂⟩, parameterized by angle α
--    or ideal success probability p_ideal ∈ [0, 1].
-- 5. Specialization of `isotropicGrover_main` to the Grover search plane and ideal output state.

import IsotropicGroverProof.MainTheorem

namespace IsotropicGrover

open Real MeasureTheory

/-! ## Index and standard basis lemmas -/

lemma succProbIdx0_inj {n : ℕ} {x y : Fin (2 ^ n)}
    (h : succProbIdx0 n x = succProbIdx0 n y) : x = y := by
  ext
  have : (succProbIdx0 n x).val = (succProbIdx0 n y).val := by rw [h]
  dsimp [succProbIdx0] at this
  omega

lemma succProbIdx0_ne_succProbIdx1 {n : ℕ} (x y : Fin (2 ^ n)) :
    succProbIdx0 n x ≠ succProbIdx1 n y := by
  intro h
  have : (succProbIdx0 n x).val = (succProbIdx1 n y).val := by rw [h]
  dsimp [succProbIdx0, succProbIdx1] at this
  omega

lemma inner_stdBasisVec (n : ℕ) (i j : Fin (d n)) :
    inner (𝕜 := ℝ) (stdBasisVec n i) (stdBasisVec n j) = if i = j then 1 else 0 := by
  have h := (orthonormal_iff_ite (𝕜 := ℝ)).mp
              (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (d n)))
  exact h i j

/-! ## Target basis state -/

/-- The target basis state vector |w⟩ in ℝ^d with amplitude 1 at real index 2w
    and 0 on all other indices. -/
noncomputable def targetBasisState (n : ℕ) (w : Fin (2 ^ n)) : E n :=
  stdBasisVec n (succProbIdx0 n w)

/-- The target basis state is a unit vector: ‖|w⟩‖ = 1. -/
lemma norm_targetBasisState (n : ℕ) (w : Fin (2 ^ n)) :
    ‖targetBasisState n w‖ = 1 :=
  stdBasisVec_norm n (succProbIdx0 n w)

/-- Inner product of |w⟩ with real component 2w is 1. -/
lemma inner_targetBasisState_idx0 (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetBasisState n w) (stdBasisVec n (succProbIdx0 n w)) = 1 := by
  unfold targetBasisState
  rw [inner_stdBasisVec]
  simp

/-- Inner product of |w⟩ with imaginary component 2w+1 is 0. -/
lemma inner_targetBasisState_idx1 (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetBasisState n w) (stdBasisVec n (succProbIdx1 n w)) = 0 := by
  unfold targetBasisState
  rw [inner_stdBasisVec]
  simp [succProbIdx0_ne_succProbIdx1]

/-- The ideal success probability of measuring outcome w on |w⟩ is 1. -/
lemma succProb_targetBasisState (n : ℕ) (w : Fin (2 ^ n)) :
    succProb n (targetBasisState n w) w = 1 := by
  unfold succProb
  rw [inner_targetBasisState_idx0, inner_targetBasisState_idx1]
  ring

/-! ## Orthogonal non-target state -/

/-- The normalized uniform superposition over all non-target states:
    |w^⟂⟩ = (1 / √(2^n - 1)) ∑_{x ≠ w} |x⟩. -/
noncomputable def targetPerpState (n : ℕ) (w : Fin (2 ^ n)) : E n :=
  (1 / Real.sqrt ((2 ^ n : ℝ) - 1)) •
    ∑ x : Fin (2 ^ n), (if x = w then (0 : ℝ) else 1) • stdBasisVec n (succProbIdx0 n x)

lemma inner_targetPerpState_idx0 (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetPerpState n w) (stdBasisVec n (succProbIdx0 n w)) = 0 := by
  unfold targetPerpState
  simp_rw [inner_smul_left, sum_inner]
  simp only [starRingEnd_apply, star_trivial]
  have h : (∑ x : Fin (2 ^ n),
      inner (𝕜 := ℝ) ((if x = w then (0 : ℝ) else 1) • stdBasisVec n (succProbIdx0 n x))
                     (stdBasisVec n (succProbIdx0 n w))) = 0 := by
    simp_rw [inner_smul_left, inner_stdBasisVec, starRingEnd_apply, star_trivial]
    have : ∀ x : Fin (2 ^ n),
        (if x = w then (0 : ℝ) else 1) *
          (if succProbIdx0 n x = succProbIdx0 n w then 1 else 0) = 0 := by
      intro x
      by_cases hx : x = w
      · subst hx; simp
      · have hne : succProbIdx0 n x ≠ succProbIdx0 n w := fun heq => hx (succProbIdx0_inj heq)
        simp [hx, hne]
    simp_rw [this]
    simp
  rw [h, mul_zero]

lemma inner_targetPerpState_idx1 (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetPerpState n w) (stdBasisVec n (succProbIdx1 n w)) = 0 := by
  unfold targetPerpState
  simp_rw [inner_smul_left, sum_inner]
  simp only [starRingEnd_apply, star_trivial]
  have h : (∑ x : Fin (2 ^ n),
      inner (𝕜 := ℝ) ((if x = w then (0 : ℝ) else 1) • stdBasisVec n (succProbIdx0 n x))
                     (stdBasisVec n (succProbIdx1 n w))) = 0 := by
    simp_rw [inner_smul_left, inner_stdBasisVec, starRingEnd_apply, star_trivial]
    have : ∀ x : Fin (2 ^ n),
        (if x = w then (0 : ℝ) else 1) *
          (if succProbIdx0 n x = succProbIdx1 n w then 1 else 0) = 0 := by
      intro x; simp [succProbIdx0_ne_succProbIdx1]
    simp_rw [this]
    simp
  rw [h, mul_zero]

/-- The target state |w⟩ and the non-target state |w^⟂⟩ are orthogonal. -/
lemma inner_targetBasisState_targetPerpState (n : ℕ) (w : Fin (2 ^ n)) :
    inner (𝕜 := ℝ) (targetBasisState n w) (targetPerpState n w) = 0 := by
  rw [real_inner_comm]
  exact inner_targetPerpState_idx0 n w

/-- Success probability of measuring outcome w on |w^⟂⟩ is 0. -/
lemma succProb_targetPerpState (n : ℕ) (w : Fin (2 ^ n)) :
    succProb n (targetPerpState n w) w = 0 := by
  unfold succProb
  rw [inner_targetPerpState_idx0, inner_targetPerpState_idx1]
  ring

/-- The non-target state |w^⟂⟩ is a unit vector when 1 < 2^n (i.e., n ≥ 1). -/
lemma norm_targetPerpState (n : ℕ) (w : Fin (2 ^ n)) (hn : 1 < 2 ^ n) :
    ‖targetPerpState n w‖ = 1 := by
  have h_inner : inner (𝕜 := ℝ) (targetPerpState n w) (targetPerpState n w) = 1 := by
    unfold targetPerpState
    simp_rw [inner_smul_left, inner_smul_right, sum_inner, inner_sum]
    simp only [starRingEnd_apply, star_trivial]
    have h_double : (∑ x : Fin (2 ^ n), ∑ y : Fin (2 ^ n),
        inner (𝕜 := ℝ) ((if x = w then (0 : ℝ) else 1) • stdBasisVec n (succProbIdx0 n x))
                       ((if y = w then (0 : ℝ) else 1) • stdBasisVec n (succProbIdx0 n y))) =
        (2 ^ n : ℝ) - 1 := by
      simp_rw [inner_smul_left, inner_smul_right, inner_stdBasisVec,
               starRingEnd_apply, star_trivial]
      have h_inner_sum : ∀ x : Fin (2 ^ n), (∑ y : Fin (2 ^ n),
          (if x = w then (0 : ℝ) else 1) *
            ((if y = w then (0 : ℝ) else 1) *
              (if succProbIdx0 n x = succProbIdx0 n y then 1 else 0))) =
          if x = w then 0 else 1 := by
        intro x
        by_cases hx : x = w
        · subst hx
          simp
        · simp only [hx, if_false, one_mul]
          have hy_eq : ∀ y : Fin (2 ^ n),
              (if y = w then (0 : ℝ) else 1) *
                (if succProbIdx0 n x = succProbIdx0 n y then 1 else 0) =
              if y = x then 1 else 0 := by
            intro y
            by_cases hyx : y = x
            · subst hyx
              simp [hx]
            · have h_ne_idx : succProbIdx0 n x ≠ succProbIdx0 n y :=
                fun heq => hyx (succProbIdx0_inj heq).symm
              simp [hyx, h_ne_idx]
          simp_rw [hy_eq]
          simp
      simp_rw [h_inner_sum]
      have : (∑ x : Fin (2 ^ n), (if x = w then (0 : ℝ) else 1)) = (2 ^ n : ℝ) - 1 := by
        rw [Finset.sum_ite]
        simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
        have h_filter : (Finset.univ.filter (fun x => ¬x = w)).card = 2 ^ n - 1 := by
          have h_comp : Finset.univ.filter (fun x => ¬x = w) = Finset.univ \ {w} := by
            ext; simp
          rw [h_comp, Finset.card_sdiff_of_subset
                (Finset.singleton_subset_iff.mpr (Finset.mem_univ w))]
          simp
        rw [h_filter]
        have h1 : 1 ≤ 2 ^ n := by omega
        rw [Nat.cast_sub h1]
        simp
      exact this
    rw [h_double]
    have h_pos : 0 < (2 ^ n : ℝ) - 1 := by
      have : (1 : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hn
      linarith
    have h_sqrt : (Real.sqrt ((2 ^ n : ℝ) - 1)) ^ 2 = (2 ^ n : ℝ) - 1 :=
      Real.sq_sqrt (by linarith)
    have h_ne : (2 ^ n : ℝ) - 1 ≠ 0 := by linarith
    calc
      (1 / Real.sqrt ((2 ^ n : ℝ) - 1)) *
        ((1 / Real.sqrt ((2 ^ n : ℝ) - 1)) * ((2 ^ n : ℝ) - 1))
        = (1 / (Real.sqrt ((2 ^ n : ℝ) - 1) ^ 2)) * ((2 ^ n : ℝ) - 1) := by ring
      _ = (1 / ((2 ^ n : ℝ) - 1)) * ((2 ^ n : ℝ) - 1) := by rw [h_sqrt]
      _ = 1 := one_div_mul_cancel h_ne
  have h_norm_sq : ‖targetPerpState n w‖ ^ 2 = 1 := by
    rw [← @real_inner_self_eq_norm_sq, h_inner]
  have h_nonneg : 0 ≤ ‖targetPerpState n w‖ := norm_nonneg _
  nlinarith

/-! ## Uniform superposition state -/

/-- The uniform superposition state vector |s⟩ = (1 / √(2^n)) ∑_x |x⟩ in ℝ^d,
    with amplitude 1 / √(2^n) on each even index 2x and 0 on 2x+1. -/
noncomputable def uniformSuperposition (n : ℕ) : E n :=
  (1 / Real.sqrt (2 ^ n)) • ∑ x : Fin (2 ^ n), stdBasisVec n (succProbIdx0 n x)

/-- The success probability of measuring any outcome w on the uniform superposition is 1 / 2^n. -/
lemma succProb_uniformSuperposition (n : ℕ) (w : Fin (2 ^ n)) :
    succProb n (uniformSuperposition n) w = 1 / (2 ^ n : ℝ) := by
  unfold succProb uniformSuperposition
  simp_rw [inner_smul_left, sum_inner]
  simp only [starRingEnd_apply, star_trivial]
  have h0 : (∑ x : Fin (2 ^ n),
      inner (𝕜 := ℝ) (stdBasisVec n (succProbIdx0 n x))
                     (stdBasisVec n (succProbIdx0 n w))) = 1 := by
    simp_rw [inner_stdBasisVec]
    have : ∀ x : Fin (2 ^ n),
        (if succProbIdx0 n x = succProbIdx0 n w then (1 : ℝ) else 0) =
          (if x = w then 1 else 0) := by
      intro x
      by_cases h : x = w
      · subst h; simp
      · have hne : succProbIdx0 n x ≠ succProbIdx0 n w := fun heq => h (succProbIdx0_inj heq)
        simp [h, hne]
    simp_rw [this]
    simp
  have h1 : (∑ x : Fin (2 ^ n),
      inner (𝕜 := ℝ) (stdBasisVec n (succProbIdx0 n x))
                     (stdBasisVec n (succProbIdx1 n w))) = 0 := by
    simp_rw [inner_stdBasisVec]
    have : ∀ x : Fin (2 ^ n),
        (if succProbIdx0 n x = succProbIdx1 n w then (1 : ℝ) else 0) = 0 := by
      intro x; simp [succProbIdx0_ne_succProbIdx1]
    simp_rw [this]
    simp
  rw [h0, h1]
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have hsqrt : Real.sqrt ((2 : ℝ) ^ n) ^ 2 = (2 : ℝ) ^ n := Real.sq_sqrt hpos
  calc
    (1 / Real.sqrt (2 ^ n) * 1) ^ 2 + (1 / Real.sqrt (2 ^ n) * 0) ^ 2
      = (1 / Real.sqrt (2 ^ n)) ^ 2 := by ring
    _ = 1 / (Real.sqrt (2 ^ n) ^ 2) := by rw [one_div_pow]
    _ = 1 / (2 ^ n : ℝ) := by rw [hsqrt]

/-- The uniform superposition state is a unit vector: ‖|s⟩‖ = 1. -/
lemma norm_uniformSuperposition (n : ℕ) :
    ‖uniformSuperposition n‖ = 1 := by
  have h_sum := sum_succProb_eq_norm_sq n (uniformSuperposition n)
  simp_rw [succProb_uniformSuperposition] at h_sum
  have h_card : (∑ _w : Fin (2 ^ n), (1 : ℝ) / (2 ^ n : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
    have h_mul := mul_one_div_cancel (G₀ := ℝ) hne
    exact nsmul_eq_mul (2 ^ n) (1 / (2 ^ n : ℝ)) ▸ (by
      push_cast
      exact h_mul)
  rw [h_card] at h_sum
  have h_nonneg : 0 ≤ ‖uniformSuperposition n‖ := norm_nonneg _
  nlinarith

/-- For the uniform superposition |s⟩ (prior to Grover iterations), the expected success
    probability under isotropic noise is identically 1 / 2^n for ANY gate count G and parameter σ.
    This establishes the baseline: without Grover rotations, isotropic noise leaves the success
    probability unchanged at the random guessing floor. -/
theorem isotropicGrover_uniformSuperposition (n : ℕ) (G : ℕ) (hG : 0 < G)
    (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (w : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, succProb n (isotropicError (uniformSuperposition n) e₂ θ) w
          ∂(perpSphereMeasure (uniformSuperposition n))
      ∂(composedMeasure (d n) G σ) =
    1 / (2 ^ n : ℝ) := by
  rw [isotropicGrover_main G hG σ hσ (uniformSuperposition n) (norm_uniformSuperposition n) w]
  rw [succProb_uniformSuperposition]
  ring

/-! ## Grover state in the 2D search plane -/

/-- A general state in the 2D Grover search plane spanned by |w⟩ and |w^⟂⟩,
    parameterized by angle α: |ψ(α)⟩ = sin(α)|w⟩ + cos(α)|w^⟂⟩. -/
noncomputable def groverState2D (n : ℕ) (w : Fin (2 ^ n)) (α : ℝ) : E n :=
  Real.sin α • targetBasisState n w + Real.cos α • targetPerpState n w

/-- Any Grover state |ψ(α)⟩ in the 2D search plane is a unit vector when 1 < 2^n. -/
lemma norm_groverState2D (n : ℕ) (w : Fin (2 ^ n)) (α : ℝ) (hn : 1 < 2 ^ n) :
    ‖groverState2D n w α‖ = 1 := by
  have h_inner : inner (𝕜 := ℝ) (groverState2D n w α) (groverState2D n w α) = 1 := by
    unfold groverState2D
    simp_rw [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    rw [inner_targetBasisState_targetPerpState]
    have h_perp_basis : inner (𝕜 := ℝ) (targetPerpState n w) (targetBasisState n w) = 0 := by
      rw [real_inner_comm, inner_targetBasisState_targetPerpState]
    rw [h_perp_basis]
    have h_norm_basis : inner (𝕜 := ℝ) (targetBasisState n w) (targetBasisState n w) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_targetBasisState, one_pow]
    have h_norm_perp : inner (𝕜 := ℝ) (targetPerpState n w) (targetPerpState n w) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_targetPerpState n w hn, one_pow]
    rw [h_norm_basis, h_norm_perp]
    have := Real.sin_sq_add_cos_sq α
    linarith
  have h_norm_sq : ‖groverState2D n w α‖ ^ 2 = 1 := by
    rw [← @real_inner_self_eq_norm_sq, h_inner]
  have h_nonneg : 0 ≤ ‖groverState2D n w α‖ := norm_nonneg _
  nlinarith

/-- The ideal success probability of measuring outcome w on |ψ(α)⟩ is sin²(α). -/
lemma succProb_groverState2D (n : ℕ) (w : Fin (2 ^ n)) (α : ℝ) :
    succProb n (groverState2D n w α) w = Real.sin α ^ 2 := by
  unfold succProb groverState2D
  simp_rw [inner_add_left, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  rw [inner_targetBasisState_idx0, inner_targetBasisState_idx1]
  rw [inner_targetPerpState_idx0, inner_targetPerpState_idx1]
  ring

/-- The expected success probability of any state in the 2D Grover search plane under
    isotropic noise is σ^(2G) * sin²(α) + (1 - σ^(2G)) / 2^n. -/
theorem isotropicGrover_groverState2D (n : ℕ) (G : ℕ) (hG : 0 < G) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (w : Fin (2 ^ n)) (α : ℝ) (hn : 1 < 2 ^ n) :
    ∫ θ, ∫ e₂, succProb n (isotropicError (groverState2D n w α) e₂ θ) w
          ∂(perpSphereMeasure (groverState2D n w α))
      ∂(composedMeasure (d n) G σ) =
    σ ^ (2 * G) * Real.sin α ^ 2 + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) := by
  rw [isotropicGrover_main G hG σ hσ (groverState2D n w α) (norm_groverState2D n w α hn) w]
  rw [succProb_groverState2D]

/-! ## Grover state parameterized directly by ideal success probability p_ideal -/

/-- A Grover state in the 2D search plane with specified ideal success probability p_ideal ∈ [0, 1]:
    |ψ(p_ideal)⟩ = √p_ideal |w⟩ + √(1 - p_ideal) |w^⟂⟩. -/
noncomputable def groverState2D_prob (n : ℕ) (w : Fin (2 ^ n)) (p_ideal : ℝ) : E n :=
  Real.sqrt p_ideal • targetBasisState n w + Real.sqrt (1 - p_ideal) • targetPerpState n w

/-- The state |ψ(p_ideal)⟩ is a unit vector for any p_ideal ∈ [0, 1] when 1 < 2^n. -/
lemma norm_groverState2D_prob (n : ℕ) (w : Fin (2 ^ n)) (p_ideal : ℝ)
    (hp : p_ideal ∈ Set.Icc (0 : ℝ) 1) (hn : 1 < 2 ^ n) :
    ‖groverState2D_prob n w p_ideal‖ = 1 := by
  have h_inner :
      inner (𝕜 := ℝ) (groverState2D_prob n w p_ideal) (groverState2D_prob n w p_ideal) = 1 := by
    unfold groverState2D_prob
    simp_rw [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    rw [inner_targetBasisState_targetPerpState]
    have h_perp_basis : inner (𝕜 := ℝ) (targetPerpState n w) (targetBasisState n w) = 0 := by
      rw [real_inner_comm, inner_targetBasisState_targetPerpState]
    rw [h_perp_basis]
    have h_norm_basis : inner (𝕜 := ℝ) (targetBasisState n w) (targetBasisState n w) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_targetBasisState, one_pow]
    have h_norm_perp : inner (𝕜 := ℝ) (targetPerpState n w) (targetPerpState n w) = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_targetPerpState n w hn, one_pow]
    rw [h_norm_basis, h_norm_perp]
    have hp0 : 0 ≤ p_ideal := hp.1
    have hp1 : 0 ≤ 1 - p_ideal := sub_nonneg.mpr hp.2
    have h_sq1 : (Real.sqrt p_ideal) ^ 2 = p_ideal := Real.sq_sqrt hp0
    have h_sq2 : (Real.sqrt (1 - p_ideal)) ^ 2 = 1 - p_ideal := Real.sq_sqrt hp1
    calc
      Real.sqrt p_ideal * (Real.sqrt p_ideal * 1) +
        Real.sqrt p_ideal * (Real.sqrt (1 - p_ideal) * 0) +
        (Real.sqrt (1 - p_ideal) * (Real.sqrt p_ideal * 0) +
          Real.sqrt (1 - p_ideal) * (Real.sqrt (1 - p_ideal) * 1))
        = (Real.sqrt p_ideal) ^ 2 + (Real.sqrt (1 - p_ideal)) ^ 2 := by ring
      _ = p_ideal + (1 - p_ideal) := by rw [h_sq1, h_sq2]
      _ = 1 := by ring
  have h_norm_sq : ‖groverState2D_prob n w p_ideal‖ ^ 2 = 1 := by
    rw [← @real_inner_self_eq_norm_sq, h_inner]
  have h_nonneg : 0 ≤ ‖groverState2D_prob n w p_ideal‖ := norm_nonneg _
  nlinarith

/-- The ideal success probability of measuring outcome w on |ψ(p_ideal)⟩ is exactly p_ideal. -/
lemma succProb_groverState2D_prob (n : ℕ) (w : Fin (2 ^ n)) (p_ideal : ℝ) (hp : 0 ≤ p_ideal) :
    succProb n (groverState2D_prob n w p_ideal) w = p_ideal := by
  unfold succProb groverState2D_prob
  simp_rw [inner_add_left, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  rw [inner_targetBasisState_idx0, inner_targetBasisState_idx1]
  rw [inner_targetPerpState_idx0, inner_targetPerpState_idx1]
  have : (Real.sqrt p_ideal * 1 + Real.sqrt (1 - p_ideal) * 0) ^ 2 +
         (Real.sqrt p_ideal * 0 + Real.sqrt (1 - p_ideal) * 0) ^ 2 =
         (Real.sqrt p_ideal) ^ 2 := by ring
  rw [this, Real.sq_sqrt hp]

/-- The expected success probability of |ψ(p_ideal)⟩ under isotropic noise is exactly
    σ^(2G) * p_ideal + (1 - σ^(2G)) / 2^n. -/
theorem isotropicGrover_groverState2D_prob (n : ℕ) (G : ℕ) (hG : 0 < G)
    (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (w : Fin (2 ^ n)) (p_ideal : ℝ)
    (hp : p_ideal ∈ Set.Icc (0 : ℝ) 1) (hn : 1 < 2 ^ n) :
    ∫ θ, ∫ e₂, succProb n (isotropicError (groverState2D_prob n w p_ideal) e₂ θ) w
          ∂(perpSphereMeasure (groverState2D_prob n w p_ideal))
      ∂(composedMeasure (d n) G σ) =
    σ ^ (2 * G) * p_ideal + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) := by
  rw [isotropicGrover_main G hG σ hσ (groverState2D_prob n w p_ideal)
        (norm_groverState2D_prob n w p_ideal hp hn) w]
  rw [succProb_groverState2D_prob n w p_ideal hp.1]

/-! ## Ideal Grover output state -/

/-- For the ideal Grover output state (where p_ideal = 1, e.g. at the target state |w⟩),
    the expected success probability under isotropic noise simplifies to
    σ^(2G) + (1 - σ^(2G)) / 2^n. -/
theorem isotropicGrover_targetBasisState (n : ℕ) (G : ℕ) (hG : 0 < G)
    (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (w : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, succProb n (isotropicError (targetBasisState n w) e₂ θ) w
          ∂(perpSphereMeasure (targetBasisState n w))
      ∂(composedMeasure (d n) G σ) =
    σ ^ (2 * G) + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) := by
  rw [isotropicGrover_main G hG σ hσ (targetBasisState n w) (norm_targetBasisState n w) w]
  rw [succProb_targetBasisState]
  ring

end IsotropicGrover
