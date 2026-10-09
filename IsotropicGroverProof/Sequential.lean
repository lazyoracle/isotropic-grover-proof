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
import IsotropicGroverProof.Defs
import IsotropicGroverProof.Composition
import IsotropicGroverProof.Gegenbauer

namespace IsotropicGrover

open Real MeasureTheory

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
  have hd2 : 2 ≤ d n := by simp only [d]; have := @Nat.one_le_two_pow n; omega
  rw [sequentialFidelity_eq (d n) σ G hd2]
  have hd_ne : (d n : ℝ) ≠ 0 := by positivity
  have hd1_ne : (d n : ℝ) - 1 ≠ 0 := by
    have : 1 < (d n : ℝ) := by
      have : 1 < d n := by simp only [d]; have := @Nat.one_le_two_pow n; omega
      exact_mod_cast this
    linarith
  have hN_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hd_eq : (d n : ℝ) = 2 * 2 ^ n := by simp only [d]; push_cast; ring
  field_simp [hd_ne, hd1_ne, hN_ne]
  rw [hd_eq]
  ring

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

end IsotropicGrover
