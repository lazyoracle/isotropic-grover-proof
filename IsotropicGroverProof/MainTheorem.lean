-- IsotropicGroverProof/MainTheorem.lean
-- M7: The main theorem — combining M4 (expanded E[p_e]), M5 (decoherent floor),
--     and M6 (f₂ formula) to prove:
--     E[p_e] = σ^{2G} · p_ideal + (1 - σ^{2G}) / N
--
-- SORRY BUDGET: 0
--   All sorrys are in dependencies (CrossTerm M4, SecondMoment M5, Gegenbauer M6).
--   The algebra here (ring/field_simp) closes without sorrys once
--   the dependency theorems have their correct statements.
--
-- KEY VERIFICATION: The `ring` call at the end is the integration test —
-- if any intermediate theorem has the wrong real-arithmetic statement, this will fail.

import IsotropicGroverProof.SecondMoment
import IsotropicGroverProof.Gegenbauer

namespace IsotropicGrover

open Real MeasureTheory

variable {n : ℕ}

/-! ## Main theorem -/

/-- **The σ^{2G} mixture formula.**
    The expected success probability of Grover's algorithm on n qubits, subject to
    G(n) independent isotropic errors with per-gate fidelity σ ∈ (0,1), is:

        E[p_e] = σ^{2G} · p_ideal + (1 - σ^{2G}) / N

    where N = 2^n is the database size, p_ideal = succProb n Φ w is the ideal
    Grover success probability, and G = G(n) is the gate count at optimal iteration.

    The formula interpolates between perfect Grover (σ^{2G} = 1) and uniform
    random guessing (σ^{2G} = 0). No approximations are made — all finite-d
    corrections cancel exactly in the algebra below. -/
theorem isotropicGrover_main (G : ℕ) (hG : 0 < G) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) (hn : 2 ≤ n) :
    -- Expected noisy success probability
    ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
          ∂(perpSphereMeasure Φ)
      ∂(composedMeasure (d n) G σ) =
    -- The σ^{2G} mixture formula
    σ ^ (2 * G) * succProb n Φ w + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) := by
  -- d n = 2 * 2^n ≥ 2 since n ≥ 2
  have hd2 : 2 ≤ d n := by simp only [d]; have := @Nat.one_le_two_pow n; omega
  -- d n ≥ 3 for Gegenbauer parameter (follows from n ≥ 2 giving d n ≥ 8)
  have hd3 : 3 ≤ d n := by
    simp only [d]
    have h : 4 ≤ 2^n := by
      calc 4 = 2^2 := by norm_num
           _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  rw [expanded_E_pe G hG σ hσ Φ hΦ w]
  rw [decoherent_floor Φ hΦ w hd2]
  rw [f₂_formula (d n) G σ hσ hd3 hG]
  -- Pure algebra: d n = 2 * 2^n and the identity checks out
  have hd_ne : (d n : ℝ) ≠ 0 := by positivity
  have hd1_ne : (d n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (d n : ℝ) := by
      have : 1 < d n := by simp only [d]; have := @Nat.one_le_two_pow n; omega
      exact_mod_cast this
    linarith
  have hN_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hd_eq : (d n : ℝ) = 2 * 2^n := by simp only [d]; push_cast; ring
  field_simp [hd_ne, hd1_ne, hN_ne]
  rw [hd_eq]
  ring

/-! ## TDD spot-checks — algebra verification -/

-- The algebraic identity at the heart of the proof (no sorrys needed here):
-- f₂ · p + (1-f₂) · (2-p)/(d-1) = σ^{2G} · p + (1-σ^{2G})/N
-- when f₂ = ((d-1)σ^{2G}+1)/d and d = 2N.
example (p σ2G : ℝ) (N : ℕ) (hN : 0 < N) : -- d = 2N
    let d : ℝ := 2 * N
    let f₂ : ℝ := ((d - 1) * σ2G + 1) / d
    f₂ * p + (1 - f₂) * (2 - p) / (d - 1) =
    σ2G * p + (1 - σ2G) / N := by
  simp only []
  have hd_ne : (2 : ℝ) * N ≠ 0 := by positivity
  have hd1_ne : (2 : ℝ) * N - 1 ≠ 0 := by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  field_simp [hd_ne, hd1_ne]
  ring

end IsotropicGrover
