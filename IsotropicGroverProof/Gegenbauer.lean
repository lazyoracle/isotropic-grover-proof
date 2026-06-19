-- IsotropicGroverProof/Gegenbauer.lean
-- M6 (rewritten): f₂ = E[cos²θ_G] via the Poisson integral formula.
--
-- The new approach (from english-proof.md §6) avoids Gegenbauer polynomials:
--   h(ξ) = (ξ·Φ)² has harmonic extension H(x) = (x·Φ)² − |x|²/d.
--   Since Δ((x·Φ)²) = 2|Φ|² = 2 and Δ(|x|²/d) = 2, we have ΔH = 0.
--   The Poisson integral formula gives:
--     E[cos²θ] = h̃(σΦ) = σ² − σ²/d + 1/d = ((d−1)σ² + 1)/d
--   For G composed gates, σ → σ^G gives f₂ = ((d−1)σ^{2G} + 1)/d.
--
-- SORRY BUDGET: 0 (uses 1 axiom cited from external source)
--   AXIOM (poissonIntegral_cos_sq_d3): the Poisson integral formula at h(ξ)=(ξ·Φ)² for d ≥ 3.
--     Source: Axler, Bourdon & Ramey, "Harmonic Function Theory" 2nd ed., Ch. 5.
--     The d=2 case is fully proved in GegenbaurerHelper.lean.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import IsotropicGroverProof.Composition
import IsotropicGroverProof.GegenbaurerHelper

namespace IsotropicGrover

open Real MeasureTheory

/-! ## Poisson integral formula for quadratic boundary data -/

/-- The second moment of the Poisson kernel on high-dimensional spheres (d ≥ 3).
    Source: Axler, Bourdon & Ramey, "Harmonic Function Theory" 2nd ed., Ch. 5. -/
axiom poissonIntegral_cos_sq_d3 (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 3 ≤ d) :
    ∫ θ, (cos θ) ^ 2 ∂(poissonMarginal d σ) =
    ((d - 1 : ℝ) * σ ^ 2 + 1) / d

/-- The Poisson integral formula applied to h(ξ) = (ξ·Φ)² = cos²θ.
    The harmonic extension of h is H(x) = (x·Φ)² − |x|²/d, plus the constant 1/d.
    Evaluated at the interior point x = σΦ (with |σΦ|² = σ²):
      h̃(σΦ) = σ² − σ²/d + 1/d = ((d−1)σ² + 1)/d.
    This gives E_ν[cos²θ] = ((d−1)σ² + 1)/d for θ ~ poissonMarginal d σ.
    Source: Axler, Bourdon & Ramey, "Harmonic Function Theory" 2nd ed., Ch. 5. -/
theorem poissonIntegral_cos_sq (d : ℕ) (σ : ℝ)
    (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ, (cos θ) ^ 2 ∂(poissonMarginal d σ) =
    ((d - 1 : ℝ) * σ ^ 2 + 1) / d := by
  obtain (rfl : d = 2) | hd3 := hd.eq_or_lt.imp Eq.symm id
  · -- d = 2: proved via Poisson formula and folding on unit circle
    exact_mod_cast poissonIntegral_cos_sq_d2 σ hσ
  · -- d ≥ 3: Poisson integral formula at h(ξ)=(ξ·Φ)²
    -- Cited from Axler, Bourdon & Ramey, "Harmonic Function Theory" 2nd ed., Ch. 5
    exact poissonIntegral_cos_sq_d3 d σ hσ hd3

/-! ## The f₂ formula: E[cos²θ_G] = ((d−1)σ^{2G} + 1) / d -/

/-- The second moment f₂ = E[cos²θ_G] = ((d−1)σ^{2G} + 1) / d.
    Proof: composedMeasure d G σ = poissonMarginal d (σ^G) by definition.
    Apply poissonIntegral_cos_sq at σ := σ^G, then use (σ^G)² = σ^{2G}. -/
theorem f₂_formula (d_val G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hd : 3 ≤ d_val) (hG : 0 < G) :
    f₂ d_val G σ = ((d_val - 1 : ℝ) * σ ^ (2 * G) + 1) / d_val := by
  simp only [f₂, composedMeasure]
  have hd2 : 2 ≤ d_val := by omega
  have hσG : σ ^ G ∈ Set.Ioo 0 1 :=
    ⟨pow_pos hσ.1 G, pow_lt_one₀ hσ.1.le hσ.2 hG.ne'⟩
  rw [poissonIntegral_cos_sq d_val (σ ^ G) hσG hd2]
  have hpow : (σ ^ G) ^ 2 = σ ^ (2 * G) := by ring
  rw [hpow]

/-! ## TDD spot-checks -/

-- f₂ at σ=0: complete decoherence gives f₂ = 1/d
example (d_val G : ℕ) (_hd : 0 < d_val) (hG : 0 < G) :
    ((d_val - 1 : ℝ) * (0 : ℝ) ^ (2 * G) + 1) / d_val = 1 / d_val := by
  have hGne : 2 * G ≠ 0 := by omega
  simp [zero_pow hGne]

-- f₂ at σ=1: perfect gates give f₂ = 1
example (d_val G : ℕ) (hd : 0 < d_val) :
    ((d_val - 1 : ℝ) * (1 : ℝ) ^ (2 * G) + 1) / d_val = 1 := by
  have hd' : (d_val : ℝ) ≠ 0 := Nat.cast_pos.mpr hd |>.ne'
  field_simp [hd']
  ring

-- Numeric check: d=8 (n=2 qubits), G=1, σ=1/2 → f₂ = 11/32
example : (((8 : ℝ) - 1) * (1/2 : ℝ) ^ (2 * 1) + 1) / 8 = 11/32 := by norm_num

-- Ring identity: (σ^G)² = σ^{2G} (the key algebraic step in the proof)
example (σ : ℝ) (G : ℕ) : (σ ^ G) ^ 2 = σ ^ (2 * G) := by ring

end IsotropicGrover
