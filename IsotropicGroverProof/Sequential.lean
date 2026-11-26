-- IsotropicGroverProof/Sequential.lean
-- Sequential Markov error accumulation: formalizing the G-gate induction
-- from english-proof.md §6.
--
-- This resolves Issues #6 and #7:
--   - Replaces the heuristic single-effective-error shortcut with an explicit
--     Markov chain on the fidelity f_k = E[(Ψ_k · Φ)²].
--   - Solves the linear recurrence f_{k+1} = λ f_k + (1-λ)(1-f_k)/(d-1)
--     in closed form: f_k = ((d-1)σ^{2k} + 1) / d for all k ≥ 0.
--   - Connects the Markov chain induction to the mixture formula without
--     requiring spherical convolution theorems or rotational commutativity.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import IsotropicGroverProof.Defs
import IsotropicGroverProof.Composition
import IsotropicGroverProof.Gegenbauer
import IsotropicGroverProof.SecondMoment

/-!
# Sequential Markov Chain Error Accumulation

Formalizes the `G`-gate fidelity recurrence `f_{k+1} = λ f_k + (1 - λ)(1 - f_k)/(d - 1)`
in closed form `f_k = ((d - 1) σ^{2k} + 1) / d`, and proves the multi-gate pure-state Markov
trajectory expectation theorems (`noisyTrajectory_bilinear`,
`noisyTrajectory_fidelity_eq_sequentialFidelity`, and `noisyTrajectory_succProb`) over arbitrary
lists of interleaved linear isometries `List (E n ≃ₗᵢ[ℝ] E n)` for all `σ ∈ [0, 1]`.
-/

namespace IsotropicGrover

open Real MeasureTheory Metric InnerProductSpace Filter Topology

/-! ## Markov chain step transition on fidelity -/

/-- The single-step transition parameter λ = ((d - 1) * σ² + 1) / d
    representing the expectation E[cos²θ_{k+1} | Ψ_k] under the Poisson kernel. -/
noncomputable def stepLambda (d : ℕ) (σ : ℝ) : ℝ :=
  ((d - 1 : ℝ) * σ ^ 2 + 1) / d

/-- The Markov step transition operator on state fidelity f = E[(Ψ_k · Φ)²]:
    T(f) = λ * f + (1 - λ) * (1 - f) / (d - 1).
    This arises from expanding (Ψ_{k+1} · Φ)² when Ψ_{k+1} = cos θ Ψ_k + sin θ e_{2,k+1}
    with e_{2,k+1} uniform on the sphere orthogonal to Ψ_k. -/
noncomputable def stepTransition (d : ℕ) (σ : ℝ) (f : ℝ) : ℝ :=
  stepLambda d σ * f + (1 - stepLambda d σ) * (1 - f) / (d - 1)

/-- Sequential fidelity after k gates under independent isotropic perturbations:
    f₀ = 1 (pure initial state Φ),
    f_{k+1} = T(f_k). -/
noncomputable def sequentialFidelity (d : ℕ) (σ : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => stepTransition d σ (sequentialFidelity d σ k)

/-! ## Contraction and closed-form induction -/

/-- The step transition contracts toward the uniform floor 1/d with factor σ²:
    T(f) - 1/d = σ² * (f - 1/d). -/
theorem stepTransition_sub_inv_d (d : ℕ) (σ f : ℝ) (hd : 2 ≤ d) :
    stepTransition d σ f - 1 / (d : ℝ) = σ ^ 2 * (f - 1 / (d : ℝ)) := by
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hd1_ne : (d : ℝ) - 1 ≠ 0 := by
    have : 1 < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
    linarith
  simp only [stepTransition, stepLambda]
  field_simp
  ring

/-- Closed-form solution of the Markov chain recurrence:
    f_k = ((d - 1) * σ^{2k} + 1) / d for all k ≥ 0. -/
theorem sequentialFidelity_eq (d : ℕ) (σ : ℝ) (k : ℕ) (hd : 2 ≤ d) :
    sequentialFidelity d σ k = ((d - 1 : ℝ) * σ ^ (2 * k) + 1) / d := by
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
  have hd1_ne : (d : ℝ) - 1 ≠ 0 := by
    have : 1 < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
    linarith
  induction k with
  | zero =>
    simp only [sequentialFidelity]
    field_simp
    ring
  | succ k ih =>
    simp only [sequentialFidelity]
    have hstep := stepTransition_sub_inv_d d σ (sequentialFidelity d σ k) hd
    have hT : stepTransition d σ (sequentialFidelity d σ k) =
        1 / (d : ℝ) + σ ^ 2 * (sequentialFidelity d σ k - 1 / (d : ℝ)) := by
      linarith
    rw [hT, ih]
    have hpow : σ ^ (2 * (k + 1)) = σ ^ 2 * σ ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
    rw [hpow]
    field_simp
    ring

/-! ## Equivalence with single-step effective formula f₂ -/

/-- The sequential fidelity after G gates equals the second moment f₂ d G σ
    derived under the composed measure parameter σ^G. -/
theorem sequentialFidelity_eq_f₂ (d G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hd : 2 ≤ d) (hG : 0 < G) :
    sequentialFidelity d σ G = f₂ d G σ := by
  rw [sequentialFidelity_eq d σ G hd]
  rw [f₂_formula d G σ hσ hd hG]

/-! ## The sequential mixture formula -/

/-- The mixture formula derived directly from the sequential fidelity:
    f_G * p + (1 - f_G) * (2 - p) / (d - 1) = σ^{2G} * p + (1 - σ^{2G}) / 2^n.
    All finite-dimension factors (d and d - 1) cancel algebraically. -/
theorem sequential_mixture_formula (p : ℝ) (n G : ℕ) (σ : ℝ) :
    sequentialFidelity (d n) σ G * p +
      (1 - sequentialFidelity (d n) σ G) * (2 - p) / ((d n : ℝ) - 1) =
    σ ^ (2 * G) * p + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) := by
  have hd2 := two_le_d n
  rw [sequentialFidelity_eq (d n) σ G hd2]
  have hd_ne : (d n : ℝ) ≠ 0 := by positivity
  have hd1_ne : (d n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (d n : ℝ) := by exact_mod_cast (by omega : 1 < d n)
    linarith
  have hN_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hd_eq : (d n : ℝ) = 2 * 2 ^ n := by simp only [d]; push_cast; ring
  field_simp [hd_ne, hd1_ne, hN_ne]
  rw [hd_eq]
  ring

/-! ## Multi-gate sequential noisy trajectory over interleaved isometries -/

section NoisyTrajectory

variable {n : ℕ}

/-- Ideal noiseless state after applying a sequence of isometric gates `gates` to `Φ₀`. -/
def idealGateTrajectory (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) : E n :=
  gates.foldl (fun v U => U v) Φ₀

@[simp]
lemma idealGateTrajectory_nil (Φ₀ : E n) :
    idealGateTrajectory ([] : List (E n ≃ₗᵢ[ℝ] E n)) Φ₀ = Φ₀ := rfl

@[simp]
lemma idealGateTrajectory_cons (U : E n ≃ₗᵢ[ℝ] E n) (rest : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) :
    idealGateTrajectory (U :: rest) Φ₀ = idealGateTrajectory rest (U Φ₀) := rfl

@[simp]
lemma idealGateTrajectory_append (g₁ g₂ : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) :
    idealGateTrajectory (g₁ ++ g₂) Φ₀ = idealGateTrajectory g₂ (idealGateTrajectory g₁ Φ₀) :=
  List.foldl_append

/-- Composite linear isometry equivalence corresponding to `idealGateTrajectory gates`. -/
noncomputable def idealGateIso (gates : List (E n ≃ₗᵢ[ℝ] E n)) : E n ≃ₗᵢ[ℝ] E n :=
  gates.foldl (fun W U => W.trans U) (LinearIsometryEquiv.refl ℝ (E n))

private lemma foldl_trans_apply (gates : List (E n ≃ₗᵢ[ℝ] E n))
    (W : E n ≃ₗᵢ[ℝ] E n) (Φ₀ : E n) :
    (gates.foldl (fun W' U => W'.trans U) W) Φ₀ = idealGateTrajectory gates (W Φ₀) := by
  induction gates generalizing W Φ₀ with
  | nil => rfl
  | cons U rest ih => exact ih (W.trans U) Φ₀

@[simp]
lemma idealGateIso_apply (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) :
    idealGateIso gates Φ₀ = idealGateTrajectory gates Φ₀ :=
  foldl_trans_apply gates (LinearIsometryEquiv.refl ℝ (E n)) Φ₀

@[simp]
lemma norm_idealGateTrajectory (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) :
    ‖idealGateTrajectory gates Φ₀‖ = ‖Φ₀‖ := by
  rw [← idealGateIso_apply]
  exact (idealGateIso gates).norm_map Φ₀

/-- Expected value of an observable `f : E n → ℝ` along the multi-gate pure-state Markov
    trajectory `Ψ_{k+1} = cos θ_{k+1} (U_{k+1} Ψ_k) + sin θ_{k+1} e_{2,k+1}` starting from `Φ₀`
    with per-gate fidelity parameter `σ`. -/
noncomputable def noisyTrajectoryExpectation (n : ℕ) (σ : ℝ) :
    List (E n ≃ₗᵢ[ℝ] E n) → E n → (E n → ℝ) → ℝ
  | [] => fun Φ₀ f => f Φ₀
  | U :: rest => fun Φ₀ f =>
      ∫ θ, ∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ) f
            ∂(perpSphereMeasure (U Φ₀)) ∂(poissonAngleMeasure (d n) σ)

@[simp]
lemma noisyTrajectoryExpectation_nil (n : ℕ) (σ : ℝ) (Φ₀ : E n) (f : E n → ℝ) :
    noisyTrajectoryExpectation n σ [] Φ₀ f = f Φ₀ := rfl

@[simp]
lemma noisyTrajectoryExpectation_cons (n : ℕ) (σ : ℝ) (U : E n ≃ₗᵢ[ℝ] E n)
    (rest : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (f : E n → ℝ) :
    noisyTrajectoryExpectation n σ (U :: rest) Φ₀ f =
    ∫ θ, ∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ) f
          ∂(perpSphereMeasure (U Φ₀)) ∂(poissonAngleMeasure (d n) σ) := rfl

/-- When `‖Φ₀‖ = 1`, `noisyTrajectoryExpectation` evaluates `f` almost surely only on unit
    vectors `{Ψ : E n | ‖Ψ‖ = 1}`, so any two observables agreeing on the unit sphere have
    identical expectations. -/
theorem noisyTrajectory_congr_unitSphere (σ : ℝ)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1)
    {f₁ f₂ : E n → ℝ} (h : ∀ Ψ : E n, ‖Ψ‖ = 1 → f₁ Ψ = f₂ Ψ) :
    noisyTrajectoryExpectation n σ gates Φ₀ f₁ =
    noisyTrajectoryExpectation n σ gates Φ₀ f₂ := by
  induction gates generalizing Φ₀ with
  | nil => exact h Φ₀ hΦ₀
  | cons U rest ih =>
    simp only [noisyTrajectoryExpectation]
    have hU : ‖U Φ₀‖ = 1 := by rw [U.norm_map]; exact hΦ₀
    congr 1; ext θ
    apply integral_congr_ae
    filter_upwards [perpSphereMeasure_norm_ae (U Φ₀)] with e₂ ⟨he₂_perp, he₂_norm⟩
    exact ih (isotropicError (U Φ₀) e₂ θ)
      (isotropicError_norm (U Φ₀) e₂ θ hU he₂_norm ((mem_V_perp_iff (U Φ₀) e₂).mp he₂_perp))

/-! ### Continuity and linearity helpers on the unit sphere -/

/-- Radial-bump extension of a function on `Metric.sphere (0 : E n) 1` to a globally
    continuous, globally bounded function on `E n` agreeing with `g` on the unit sphere. -/
private noncomputable def extendFromSphere (g : E n → ℝ) (x : E n) : ℝ :=
  max 0 (min 1 (2 * ‖x‖ - 1)) * g (‖x‖⁻¹ • x)

private lemma extendFromSphere_eq_on_sphere (g : E n → ℝ) {x : E n} (hx : ‖x‖ = 1) :
    extendFromSphere g x = g x := by
  simp only [extendFromSphere, hx, inv_one, one_smul]
  norm_num

private lemma extendFromSphere_zero_of_norm_le (g : E n → ℝ) {x : E n} (hx : ‖x‖ ≤ 1 / 2) :
    extendFromSphere g x = 0 := by
  have hle : min 1 (2 * ‖x‖ - 1) ≤ 0 := min_le_of_right_le (by linarith)
  simp [extendFromSphere, max_eq_left hle]

private lemma extendFromSphere_continuous {g : E n → ℝ}
    (hg : ContinuousOn g (Metric.sphere (0 : E n) 1)) :
    Continuous (extendFromSphere g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hnhds : {y : E n | ‖y‖ < 1 / 2} ∈ 𝓝 (0 : E n) :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
    refine (continuousAt_const : ContinuousAt (fun _ : E n => (0 : ℝ)) 0).congr ?_
    filter_upwards [hnhds] with y hy
    exact (extendFromSphere_zero_of_norm_le g (le_of_lt hy)).symm
  · have hopen : IsOpen {y : E n | y ≠ 0} := isOpen_ne
    have hproj_cont : ContinuousOn (fun y : E n => ‖y‖⁻¹ • y) {y : E n | y ≠ 0} := by
      have hinv : ContinuousOn (fun y : E n => ‖y‖⁻¹) {y : E n | y ≠ 0} :=
        ContinuousOn.inv₀ continuous_norm.continuousOn (fun y hy => norm_ne_zero_iff.mpr hy)
      exact hinv.smul continuousOn_id
    have hproj_maps : Set.MapsTo (fun y : E n => ‖y‖⁻¹ • y)
        {y : E n | y ≠ 0} (Metric.sphere (0 : E n) 1) := by
      intro y hy
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
    have hcontOn : ContinuousOn (extendFromSphere g) {y : E n | y ≠ 0} := by
      refine ContinuousOn.mul ?_ (hg.comp hproj_cont hproj_maps)
      exact (continuous_const.max (continuous_const.min
        ((continuous_const.mul continuous_norm).sub continuous_const))).continuousOn
    exact hcontOn.continuousAt (hopen.mem_nhds hx)

private lemma extendFromSphere_bounded {g : E n → ℝ}
    (hg : ContinuousOn g (Metric.sphere (0 : E n) 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E n, ‖extendFromSphere g x‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : E n) 1).exists_bound_of_continuousOn hg
  refine ⟨max 0 M, le_max_left 0 M, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    rw [extendFromSphere_zero_of_norm_le g (by norm_num), norm_zero]
    exact le_max_left 0 M
  · have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E n) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have hbump_nn : 0 ≤ max (0 : ℝ) (min 1 (2 * ‖x‖ - 1)) := le_max_left _ _
    have hbump_le : max (0 : ℝ) (min 1 (2 * ‖x‖ - 1)) ≤ 1 :=
      max_le (by norm_num) (min_le_left _ _)
    rw [extendFromSphere, norm_mul, Real.norm_of_nonneg hbump_nn]
    calc max 0 (min 1 (2 * ‖x‖ - 1)) * ‖g (‖x‖⁻¹ • x)‖
        ≤ 1 * max 0 M := mul_le_mul hbump_le
          ((hM _ hmem).trans (le_max_right 0 M)) (norm_nonneg _) zero_le_one
      _ = max 0 M := one_mul _

/-- Involutive linear isometry `(2 ⟪w, x⟫ / ‖w‖²) • w - x` for `w ≠ 0`; when `w = Ψ₀ + Ψ`
    for unit vectors `Ψ₀, Ψ` with `Ψ₀ + Ψ ≠ 0`, this maps `Ψ₀ ↦ Ψ` continuously in `Ψ`. -/
private noncomputable def rotTo (w x : E n) : E n :=
  (2 * ⟪w, x⟫_ℝ / ‖w‖ ^ 2) • w - x

private lemma rotTo_involutive {w : E n} (hw : w ≠ 0) (x : E n) :
    rotTo w (rotTo w x) = x := by
  have hw_sq : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hinner : ⟪w, rotTo w x⟫_ℝ = ⟪w, x⟫_ℝ := by
    rw [rotTo, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
        div_mul_cancel₀ _ hw_sq]
    ring
  rw [rotTo, hinner, rotTo, sub_sub_cancel]

private lemma rotTo_norm {w : E n} (hw : w ≠ 0) (x : E n) :
    ‖rotTo w x‖ = ‖x‖ := by
  have hw_sq : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hsq : ‖rotTo w x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, rotTo, inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_smul_left, real_inner_smul_left, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq w, real_inner_self_eq_norm_sq x, real_inner_comm x w]
    field_simp [hw_sq]
    ring
  nlinarith [norm_nonneg (rotTo w x), norm_nonneg x, sq_nonneg (‖rotTo w x‖ - ‖x‖)]

private noncomputable def rotToEquiv (w : E n) (hw : w ≠ 0) : E n ≃ₗᵢ[ℝ] E n where
  toFun := rotTo w
  invFun := rotTo w
  map_add' x y := by
    simp only [rotTo, inner_add_right]
    rw [show 2 * (⟪w, x⟫_ℝ + ⟪w, y⟫_ℝ) / ‖w‖ ^ 2 =
        2 * ⟪w, x⟫_ℝ / ‖w‖ ^ 2 + 2 * ⟪w, y⟫_ℝ / ‖w‖ ^ 2 by ring, add_smul]
    abel
  map_smul' c x := by
    simp only [rotTo, inner_smul_right, RingHom.id_apply]
    rw [show 2 * (c * ⟪w, x⟫_ℝ) / ‖w‖ ^ 2 = c * (2 * ⟪w, x⟫_ℝ / ‖w‖ ^ 2) by ring,
        ← smul_smul, smul_sub]
  left_inv := rotTo_involutive hw
  right_inv := rotTo_involutive hw
  norm_map' := rotTo_norm hw

private lemma rotTo_unit_sum {Ψ₀ Ψ : E n} (hΨ₀ : ‖Ψ₀‖ = 1) (hΨ : ‖Ψ‖ = 1)
    (hw : Ψ₀ + Ψ ≠ 0) :
    rotTo (Ψ₀ + Ψ) Ψ₀ = Ψ := by
  have hw_sq : ‖Ψ₀ + Ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hnum : 2 * ⟪Ψ₀ + Ψ, Ψ₀⟫_ℝ = ‖Ψ₀ + Ψ‖ ^ 2 := by
    rw [norm_add_sq_real, inner_add_left, real_inner_self_eq_norm_sq, hΨ₀, hΨ,
        real_inner_comm Ψ Ψ₀]
    ring
  rw [rotTo, hnum, div_self hw_sq, one_smul, add_sub_cancel_left]

lemma ae_isotropicError_mem_sphere {Ψ : E n} (hΨ : ‖Ψ‖ = 1) (θ : ℝ) :
    ∀ᵐ e₂ ∂(perpSphereMeasure Ψ), ‖isotropicError Ψ e₂ θ‖ = 1 := by
  filter_upwards [perpSphereMeasure_norm_ae Ψ] with e₂ ⟨he₂_perp, he₂_norm⟩
  exact isotropicError_norm Ψ e₂ θ hΨ he₂_norm ((mem_V_perp_iff Ψ e₂).mp he₂_perp)

lemma integrable_perpSphere_of_continuousOn {Ψ : E n} (hΨ : ‖Ψ‖ = 1) (θ : ℝ)
    {g : E n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : E n) 1)) :
    Integrable (fun e₂ => g (isotropicError Ψ e₂ θ)) (perpSphereMeasure Ψ) := by
  obtain ⟨C, _, hC⟩ := extendFromSphere_bounded hg
  have hg_cont : Continuous (fun e₂ => extendFromSphere g (isotropicError Ψ e₂ θ)) :=
    (extendFromSphere_continuous hg).comp (by unfold isotropicError; fun_prop)
  have hint_ext : Integrable (fun e₂ => extendFromSphere g (isotropicError Ψ e₂ θ))
      (perpSphereMeasure Ψ) :=
    Integrable.mono' (integrable_const C) hg_cont.aestronglyMeasurable
      (ae_of_all _ fun e₂ => hC _)
  refine hint_ext.congr ?_
  filter_upwards [ae_isotropicError_mem_sphere hΨ θ] with e₂ he₂
  exact extendFromSphere_eq_on_sphere g he₂

private lemma continuous_inner_integral_of_continuousOn {Ψ : E n} (hΨ : ‖Ψ‖ = 1)
    {g : E n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : E n) 1)) :
    Continuous (fun θ => ∫ e₂, g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ)) := by
  obtain ⟨C, _, hC⟩ := extendFromSphere_bounded hg
  have heq : (fun θ => ∫ e₂, g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ)) =
      (fun θ => ∫ e₂, extendFromSphere g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ)) := by
    ext θ
    apply integral_congr_ae
    filter_upwards [ae_isotropicError_mem_sphere hΨ θ] with e₂ he₂
    exact (extendFromSphere_eq_on_sphere g he₂).symm
  rw [heq, continuous_iff_continuousAt]
  intro θ₀
  have hcont_θ : ∀ e₂ : E n,
      Continuous (fun θ => extendFromSphere g (isotropicError Ψ e₂ θ)) := fun e₂ =>
    (extendFromSphere_continuous hg).comp (by unfold isotropicError; fun_prop)
  have hcont_e₂ : ∀ θ : ℝ,
      Continuous (fun e₂ => extendFromSphere g (isotropicError Ψ e₂ θ)) := fun θ =>
    (extendFromSphere_continuous hg).comp (by unfold isotropicError; fun_prop)
  exact tendsto_integral_filter_of_norm_le_const
    (Eventually.of_forall fun θ => (hcont_e₂ θ).aestronglyMeasurable)
    ⟨C, Eventually.of_forall fun θ => ae_of_all _ fun e₂ => hC _⟩
    (ae_of_all _ fun e₂ => (hcont_θ e₂).continuousAt)

private lemma norm_inner_integral_le_of_continuousOn {Ψ : E n} (hΨ : ‖Ψ‖ = 1)
    {g : E n → ℝ} {C : ℝ}
    (hC : ∀ x : E n, ‖extendFromSphere g x‖ ≤ C) (θ : ℝ) :
    ‖∫ e₂, g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ)‖ ≤ C := by
  have heq : ∫ e₂, g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ) =
      ∫ e₂, extendFromSphere g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ) := by
    apply integral_congr_ae
    filter_upwards [ae_isotropicError_mem_sphere hΨ θ] with e₂ he₂
    exact (extendFromSphere_eq_on_sphere g he₂).symm
  rw [heq]
  calc ‖∫ e₂, extendFromSphere g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ)‖
      ≤ C * (perpSphereMeasure Ψ).real Set.univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ fun e₂ => hC _)
    _ = C := by simp [Measure.real]

lemma integrable_outer_integral_of_continuousOn (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    {Ψ : E n} (hΨ : ‖Ψ‖ = 1) {g : E n → ℝ}
    (hg : ContinuousOn g (Metric.sphere (0 : E n) 1)) :
    Integrable (fun θ => ∫ e₂, g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ))
      (poissonAngleMeasure (d n) σ) := by
  have := poissonAngleMeasure_d_isProbMeasure n σ hσ
  obtain ⟨C, _, hC⟩ := extendFromSphere_bounded hg
  exact Integrable.mono' (integrable_const C)
    (continuous_inner_integral_of_continuousOn hΨ hg).aestronglyMeasurable
    (ae_of_all _ fun θ => norm_inner_integral_le_of_continuousOn hΨ hC θ)

private lemma continuousAt_rotTo_add {Ψ₀ : E n} (hsum_ne : Ψ₀ + Ψ₀ ≠ 0) (e₂ : E n) :
    ContinuousAt (fun Ψ : E n => rotTo (Ψ₀ + Ψ) e₂) Ψ₀ := by
  unfold rotTo
  have hw0_sq : ‖Ψ₀ + Ψ₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hsum_ne)
  fun_prop (disch := exact hw0_sq)

private lemma continuousAt_isotropicError_rotTo {Ψ₀ : E n} (hsum_ne : Ψ₀ + Ψ₀ ≠ 0)
    (e₂ : E n) (θ : ℝ) :
    ContinuousAt (fun Ψ : E n => isotropicError Ψ (rotTo (Ψ₀ + Ψ) e₂) θ) Ψ₀ := by
  have hrot := continuousAt_rotTo_add hsum_ne e₂
  unfold isotropicError
  fun_prop

private lemma continuousOn_oneStep_unitSphere (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    {g : E n → ℝ} (hg : ContinuousOn g (Metric.sphere (0 : E n) 1)) :
    ContinuousOn
      (fun Ψ => ∫ θ, ∫ e₂, g (isotropicError Ψ e₂ θ)
        ∂(perpSphereMeasure Ψ) ∂(poissonAngleMeasure (d n) σ))
      (Metric.sphere (0 : E n) 1) := by
  have := poissonAngleMeasure_d_isProbMeasure n σ hσ
  obtain ⟨C, _, hC⟩ := extendFromSphere_bounded hg
  have hg_ext_cont : Continuous (extendFromSphere g) := extendFromSphere_continuous hg
  intro Ψ₀ hΨ₀_mem
  have hΨ₀ : ‖Ψ₀‖ = 1 := mem_sphere_zero_iff_norm.mp hΨ₀_mem
  have hsum_ne : Ψ₀ + Ψ₀ ≠ 0 := by
    intro h0
    have : ‖Ψ₀ + Ψ₀‖ = 0 := by rw [h0, norm_zero]
    rw [← two_smul ℝ Ψ₀, norm_smul, Real.norm_ofNat, hΨ₀, mul_one] at this
    norm_num at this
  have hev_sphere : ∀ᶠ Ψ in 𝓝[Metric.sphere (0 : E n) 1] Ψ₀,
      Ψ ∈ Metric.sphere (0 : E n) 1 := self_mem_nhdsWithin
  have hev_ne : ∀ᶠ Ψ in 𝓝[Metric.sphere (0 : E n) 1] Ψ₀, Ψ₀ + Ψ ≠ 0 := by
    have hcont_add : Continuous (fun Ψ : E n => Ψ₀ + Ψ) := continuous_const.add continuous_id
    exact (hcont_add.continuousAt.eventually
      (isOpen_ne.mem_nhds hsum_ne)).filter_mono nhdsWithin_le_nhds
  -- Rewrite inner integral via `rotToEquiv (Ψ₀ + Ψ)` for `Ψ ∈ sphere` with `Ψ₀ + Ψ ≠ 0`
  have hinner_rot : ∀ {Ψ : E n}, ‖Ψ‖ = 1 → Ψ₀ + Ψ ≠ 0 → ∀ θ : ℝ,
      ∫ e₂, g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ) =
      ∫ e₂, extendFromSphere g (isotropicError Ψ (rotTo (Ψ₀ + Ψ) e₂) θ)
        ∂(perpSphereMeasure Ψ₀) := by
    intro Ψ hΨ hw θ
    have hext : ∫ e₂, g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ) =
        ∫ e₂, extendFromSphere g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ) := by
      apply integral_congr_ae
      filter_upwards [ae_isotropicError_mem_sphere hΨ θ] with e₂ he₂
      exact (extendFromSphere_eq_on_sphere g he₂).symm
    let L := rotToEquiv (Ψ₀ + Ψ) hw
    have hLΨ₀ : L Ψ₀ = Ψ := rotTo_unit_sum hΨ₀ hΨ hw
    have hmap : perpSphereMeasure Ψ = Measure.map L (perpSphereMeasure Ψ₀) := by
      rw [← hLΨ₀, perpSphereMeasure_map_isometry Ψ₀ L]
    have hcont_e₂ : Continuous (fun e₂ => extendFromSphere g (isotropicError Ψ e₂ θ)) :=
      hg_ext_cont.comp (by unfold isotropicError; fun_prop)
    rw [hext, hmap, integral_map L.continuous.aemeasurable hcont_e₂.aestronglyMeasurable]
    rfl
  -- Pointwise convergence in `θ` of the inner integral as `Ψ → Ψ₀` on the sphere
  have hinner_tendsto : ∀ θ : ℝ,
      Tendsto (fun Ψ => ∫ e₂, g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ))
        (𝓝[Metric.sphere (0 : E n) 1] Ψ₀)
        (𝓝 (∫ e₂, g (isotropicError Ψ₀ e₂ θ) ∂(perpSphereMeasure Ψ₀))) := by
    intro θ
    rw [hinner_rot hΨ₀ hsum_ne θ]
    have hev_eq : (fun Ψ => ∫ e₂, g (isotropicError Ψ e₂ θ) ∂(perpSphereMeasure Ψ))
        =ᶠ[𝓝[Metric.sphere (0 : E n) 1] Ψ₀]
        (fun Ψ => ∫ e₂, extendFromSphere g (isotropicError Ψ (rotTo (Ψ₀ + Ψ) e₂) θ)
          ∂(perpSphereMeasure Ψ₀)) := by
      filter_upwards [hev_sphere, hev_ne] with Ψ hΨ_mem hw
      exact hinner_rot (mem_sphere_zero_iff_norm.mp hΨ_mem) hw θ
    refine Tendsto.congr' hev_eq.symm ?_
    refine tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
    · filter_upwards [hev_ne] with Ψ hw
      have hcont_rot : Continuous (rotTo (Ψ₀ + Ψ)) := (rotToEquiv (Ψ₀ + Ψ) hw).continuous
      exact (hg_ext_cont.comp (by unfold isotropicError; fun_prop)).aestronglyMeasurable
    · exact ⟨C, Eventually.of_forall fun _ => ae_of_all _ fun _ => hC _⟩
    · refine ae_of_all _ fun e₂ => ?_
      exact (hg_ext_cont.continuousAt.comp
        (continuousAt_isotropicError_rotTo hsum_ne e₂ θ)).mono_left nhdsWithin_le_nhds
  -- Dominated convergence for the outer integral over `poissonAngleMeasure (d n) σ`
  refine tendsto_integral_filter_of_norm_le_const ?_ ?_ (ae_of_all _ hinner_tendsto)
  · filter_upwards [hev_sphere] with Ψ hΨ_mem
    exact (continuous_inner_integral_of_continuousOn
      (mem_sphere_zero_iff_norm.mp hΨ_mem) hg).aestronglyMeasurable
  · refine ⟨C, ?_⟩
    filter_upwards [hev_sphere] with Ψ hΨ_mem
    exact ae_of_all _ fun θ =>
      norm_inner_integral_le_of_continuousOn
        (mem_sphere_zero_iff_norm.mp hΨ_mem) hC θ

/-- `noisyTrajectoryExpectation` preserves `ContinuousOn` on the unit sphere
    `Metric.sphere (0 : E n) 1` for any gate list and `σ ∈ [0, 1]`. -/
theorem noisyTrajectoryExpectation_continuousOn_unitSphere (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) {f : E n → ℝ}
    (hf : ContinuousOn f (Metric.sphere (0 : E n) 1)) :
    ContinuousOn (fun Φ₀ => noisyTrajectoryExpectation n σ gates Φ₀ f)
      (Metric.sphere (0 : E n) 1) := by
  induction gates with
  | nil => exact hf
  | cons U rest ih =>
    have hstep := continuousOn_oneStep_unitSphere σ hσ ih
    have hU_maps : Set.MapsTo (U : E n → E n)
        (Metric.sphere (0 : E n) 1) (Metric.sphere (0 : E n) 1) := by
      intro x hx
      rw [mem_sphere_zero_iff_norm] at hx ⊢
      rw [U.norm_map, hx]
    exact hstep.comp U.continuous.continuousOn hU_maps

/-! ### Linearity of `noisyTrajectoryExpectation` -/

/-- Expectation of a constant observable along the noisy trajectory equals that constant. -/
theorem noisyTrajectoryExpectation_const (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (c : ℝ) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun _ => c) = c := by
  have := poissonAngleMeasure_d_isProbMeasure n σ hσ
  induction gates generalizing Φ₀ with
  | nil => rfl
  | cons U rest ih =>
    simp only [noisyTrajectoryExpectation]
    simp_rw [ih]
    simp

/-- Scalar multiplication pulls out of `noisyTrajectoryExpectation`. -/
theorem noisyTrajectoryExpectation_const_mul (σ : ℝ)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (c : ℝ) (f : E n → ℝ) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => c * f Ψ) =
    c * noisyTrajectoryExpectation n σ gates Φ₀ f := by
  induction gates generalizing Φ₀ with
  | nil => rfl
  | cons U rest ih =>
    simp only [noisyTrajectoryExpectation]
    simp_rw [ih, integral_const_mul]

/-- Negation pulls out of `noisyTrajectoryExpectation`. -/
theorem noisyTrajectoryExpectation_neg (σ : ℝ)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (f : E n → ℝ) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => -f Ψ) =
    -noisyTrajectoryExpectation n σ gates Φ₀ f := by
  simpa using noisyTrajectoryExpectation_const_mul σ gates Φ₀ (-1) f

/-- Additivity of `noisyTrajectoryExpectation` for functions continuous on the unit sphere. -/
theorem noisyTrajectoryExpectation_add_of_continuousOn (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1)
    {f g : E n → ℝ}
    (hf : ContinuousOn f (Metric.sphere (0 : E n) 1))
    (hg : ContinuousOn g (Metric.sphere (0 : E n) 1)) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => f Ψ + g Ψ) =
    noisyTrajectoryExpectation n σ gates Φ₀ f +
    noisyTrajectoryExpectation n σ gates Φ₀ g := by
  induction gates generalizing Φ₀ with
  | nil => rfl
  | cons U rest ih =>
    simp only [noisyTrajectoryExpectation]
    have hU : ‖U Φ₀‖ = 1 := by rw [U.norm_map]; exact hΦ₀
    have hf_rest := noisyTrajectoryExpectation_continuousOn_unitSphere σ hσ rest hf
    have hg_rest := noisyTrajectoryExpectation_continuousOn_unitSphere σ hσ rest hg
    have hinner_eq : ∀ θ : ℝ,
        ∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ)
          (fun Ψ => f Ψ + g Ψ) ∂(perpSphereMeasure (U Φ₀)) =
        (∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ) f
          ∂(perpSphereMeasure (U Φ₀))) +
        (∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ) g
          ∂(perpSphereMeasure (U Φ₀))) := by
      intro θ
      have hae : ∀ᵐ e₂ ∂(perpSphereMeasure (U Φ₀)),
          noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ)
            (fun Ψ => f Ψ + g Ψ) =
          noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ) f +
          noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ) g := by
        filter_upwards [ae_isotropicError_mem_sphere hU θ] with e₂ he₂
        exact ih (isotropicError (U Φ₀) e₂ θ) he₂
      rw [integral_congr_ae hae]
      exact integral_add
        (integrable_perpSphere_of_continuousOn hU θ hf_rest)
        (integrable_perpSphere_of_continuousOn hU θ hg_rest)
    simp_rw [hinner_eq]
    exact integral_add
      (integrable_outer_integral_of_continuousOn σ hσ hU hf_rest)
      (integrable_outer_integral_of_continuousOn σ hσ hU hg_rest)

/-- Additivity of `noisyTrajectoryExpectation` for continuous observables `f, g : E n → ℝ`. -/
theorem noisyTrajectoryExpectation_add (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1)
    {f g : E n → ℝ} (hf : Continuous f) (hg : Continuous g) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => f Ψ + g Ψ) =
    noisyTrajectoryExpectation n σ gates Φ₀ f +
    noisyTrajectoryExpectation n σ gates Φ₀ g :=
  noisyTrajectoryExpectation_add_of_continuousOn σ hσ gates Φ₀ hΦ₀ hf.continuousOn hg.continuousOn

/-- Subtraction linearity of `noisyTrajectoryExpectation` for continuous observables
    `f, g : E n → ℝ`. -/
theorem noisyTrajectoryExpectation_sub (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1)
    {f g : E n → ℝ} (hf : Continuous f) (hg : Continuous g) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => f Ψ - g Ψ) =
    noisyTrajectoryExpectation n σ gates Φ₀ f -
    noisyTrajectoryExpectation n σ gates Φ₀ g := by
  have hsub : (fun Ψ : E n => f Ψ - g Ψ) = (fun Ψ => f Ψ + -g Ψ) := by
    ext Ψ; exact sub_eq_add_neg _ _
  have hg_neg : Continuous (fun Ψ : E n => -g Ψ) := Continuous.neg hg
  rw [hsub, noisyTrajectoryExpectation_add σ hσ gates Φ₀ hΦ₀ hf hg_neg,
      noisyTrajectoryExpectation_neg, sub_eq_add_neg]

/-! ### Multi-gate bilinear second-moment, fidelity, and success-probability theorems -/

/-- **Multi-gate bilinear expectation theorem** over an arbitrary list of interleaved
    isometric gates `gates` for all `σ ∈ [0, 1]` and unit initial states `‖Φ₀‖ = 1`. -/
theorem noisyTrajectory_bilinear (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1) (u v : E n) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => ⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) =
    σ ^ (2 * gates.length) *
      (⟪idealGateTrajectory gates Φ₀, u⟫_ℝ * ⟪idealGateTrajectory gates Φ₀, v⟫_ℝ) +
    (1 - σ ^ (2 * gates.length)) / (d n : ℝ) * ⟪u, v⟫_ℝ := by
  have := poissonAngleMeasure_d_isProbMeasure n σ hσ
  induction gates generalizing Φ₀ with
  | nil =>
    simp
  | cons U rest ih =>
    simp only [noisyTrajectoryExpectation]
    have hU : ‖U Φ₀‖ = 1 := by rw [U.norm_map]; exact hΦ₀
    let W := idealGateIso rest
    have hadj : ∀ (x y : E n), ⟪idealGateTrajectory rest x, y⟫_ℝ = ⟪x, W.symm y⟫_ℝ := by
      intro x y
      rw [← idealGateIso_apply, ← W.symm.inner_map_map (W x) y, W.symm_apply_apply]
    have hquad_cont : ContinuousOn (fun Ψ : E n => ⟪Ψ, W.symm u⟫_ℝ * ⟪Ψ, W.symm v⟫_ℝ)
        (Metric.sphere (0 : E n) 1) :=
      ((continuous_id.inner continuous_const).mul
        (continuous_id.inner continuous_const)).continuousOn
    have hinner_eq : ∀ θ : ℝ,
        ∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ)
          (fun Ψ => ⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) ∂(perpSphereMeasure (U Φ₀)) =
        σ ^ (2 * rest.length) *
          (∫ e₂, ⟪isotropicError (U Φ₀) e₂ θ, W.symm u⟫_ℝ *
            ⟪isotropicError (U Φ₀) e₂ θ, W.symm v⟫_ℝ ∂(perpSphereMeasure (U Φ₀))) +
        (1 - σ ^ (2 * rest.length)) / (d n : ℝ) * ⟪u, v⟫_ℝ := by
      intro θ
      have hae : ∀ᵐ e₂ ∂(perpSphereMeasure (U Φ₀)),
          noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ)
            (fun Ψ => ⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) =
          σ ^ (2 * rest.length) *
            (⟪isotropicError (U Φ₀) e₂ θ, W.symm u⟫_ℝ *
              ⟪isotropicError (U Φ₀) e₂ θ, W.symm v⟫_ℝ) +
          (1 - σ ^ (2 * rest.length)) / (d n : ℝ) * ⟪u, v⟫_ℝ := by
        filter_upwards [ae_isotropicError_mem_sphere hU θ] with e₂ he₂
        rw [ih (isotropicError (U Φ₀) e₂ θ) he₂, hadj, hadj]
      rw [integral_congr_ae hae]
      have hint1 := (integrable_perpSphere_of_continuousOn hU θ hquad_cont).const_mul
        (σ ^ (2 * rest.length))
      rw [integral_add hint1 (integrable_const _), integral_const_mul, integral_const]
      simp
    simp_rw [hinner_eq]
    have hout1 := (integrable_outer_integral_of_continuousOn σ hσ hU hquad_cont).const_mul
      (σ ^ (2 * rest.length))
    rw [integral_add hout1 (integrable_const _), integral_const_mul, integral_const,
        isotropicError_bilinear_secondMoment σ hσ (U Φ₀) hU (W.symm u) (W.symm v)]
    simp only [smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul,
               List.length_cons, idealGateTrajectory_cons]
    rw [W.symm.inner_map_map u v, ← hadj (U Φ₀) u, ← hadj (U Φ₀) v,
        show 2 * (rest.length + 1) = 2 * rest.length + 2 by omega, pow_add]
    have hd_ne : (d n : ℝ) ≠ 0 := by positivity
    field_simp [hd_ne]
    ring

/-- The expected squared overlap `E[⟪Ψ_G, Φ_G⟫²]` of the `G`-gate Markov trajectory with
    the ideal output `idealGateTrajectory gates Φ₀` equals
    `sequentialFidelity (d n) σ gates.length`. -/
theorem noisyTrajectory_fidelity_eq_sequentialFidelity (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1) :
    noisyTrajectoryExpectation n σ gates Φ₀
      (fun Ψ => ⟪Ψ, idealGateTrajectory gates Φ₀⟫_ℝ ^ 2) =
    sequentialFidelity (d n) σ gates.length := by
  set ΦG := idealGateTrajectory gates Φ₀
  have hΦG : ⟪ΦG, ΦG⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_idealGateTrajectory, hΦ₀, one_pow]
  simp_rw [sq]
  rw [noisyTrajectory_bilinear σ hσ gates Φ₀ hΦ₀ ΦG ΦG, hΦG,
      sequentialFidelity_eq (d n) σ gates.length (two_le_d n)]
  have hd_ne : (d n : ℝ) ≠ 0 := by positivity
  field_simp [hd_ne]
  ring

/-- **Multi-gate expected success probability theorem:** After any list `gates` of interleaved
    isometric gates (including `gates = []`) and for all `σ ∈ [0, 1]`, the expected measurement
    probability of outcome `w` along the pure-state Markov trajectory equals
    `σ ^ (2 * gates.length) * succProb n (idealGateTrajectory gates Φ₀) w +
      (1 - σ ^ (2 * gates.length)) / 2^n`. -/
theorem noisyTrajectory_succProb (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1)
    (gates : List (E n ≃ₗᵢ[ℝ] E n)) (Φ₀ : E n) (hΦ₀ : ‖Φ₀‖ = 1) (w : Fin (2 ^ n)) :
    noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => succProb n Ψ w) =
    σ ^ (2 * gates.length) * succProb n (idealGateTrajectory gates Φ₀) w +
      (1 - σ ^ (2 * gates.length)) / (2 ^ n : ℝ) := by
  set e₀ := stdBasisVec n (succProbIdx0 n w)
  set e₁ := stdBasisVec n (succProbIdx1 n w)
  have hcont₀ : Continuous (fun Ψ : E n => ⟪Ψ, e₀⟫_ℝ ^ 2) :=
    (continuous_id.inner continuous_const).pow 2
  have hcont₁ : Continuous (fun Ψ : E n => ⟪Ψ, e₁⟫_ℝ ^ 2) :=
    (continuous_id.inner continuous_const).pow 2
  simp only [succProb]
  rw [noisyTrajectoryExpectation_add σ hσ gates Φ₀ hΦ₀ hcont₀ hcont₁]
  simp_rw [sq]
  rw [noisyTrajectory_bilinear σ hσ gates Φ₀ hΦ₀ e₀ e₀,
      noisyTrajectory_bilinear σ hσ gates Φ₀ hΦ₀ e₁ e₁]
  have he₀ : ⟪e₀, e₀⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, stdBasisVec_norm, one_pow]
  have he₁ : ⟪e₁, e₁⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, stdBasisVec_norm, one_pow]
  have hd_eq : (d n : ℝ) = 2 * (2 ^ n : ℝ) := by simp only [d]; push_cast; ring
  have hN_ne : (2 ^ n : ℝ) ≠ 0 := by positivity
  rw [he₀, he₁, hd_eq]
  field_simp [hN_ne]
  ring

end NoisyTrajectory

/-! ## TDD spot checks -/

-- Contraction base check: at f = 1, T(1) = λ
example (d : ℕ) (σ : ℝ) (_hd : 2 ≤ d) :
    stepTransition d σ 1 = stepLambda d σ := by
  simp only [stepTransition, sub_self, mul_zero, zero_div, add_zero, mul_one]

-- At k = 0, fidelity is identically 1
example (d : ℕ) (σ : ℝ) : sequentialFidelity d σ 0 = 1 := rfl

-- At k = 1, fidelity equals stepLambda
example (d : ℕ) (σ : ℝ) : sequentialFidelity d σ 1 = stepLambda d σ := by
  simp [sequentialFidelity, stepTransition]

#check @idealGateTrajectory
#check @noisyTrajectoryExpectation
#check @noisyTrajectory_congr_unitSphere
#check @noisyTrajectoryExpectation_const
#check @noisyTrajectoryExpectation_const_mul
#check @noisyTrajectoryExpectation_add
#check @noisyTrajectoryExpectation_sub
#check @noisyTrajectory_bilinear
#check @noisyTrajectory_fidelity_eq_sequentialFidelity
#check @noisyTrajectory_succProb

/--
info: 'IsotropicGrover.noisyTrajectory_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyTrajectory_bilinear

/--
info: 'IsotropicGrover.noisyTrajectory_fidelity_eq_sequentialFidelity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms noisyTrajectory_fidelity_eq_sequentialFidelity

/--
info: 'IsotropicGrover.noisyTrajectory_succProb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms noisyTrajectory_succProb

end IsotropicGrover
