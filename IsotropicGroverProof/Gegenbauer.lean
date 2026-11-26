-- IsotropicGroverProof/Gegenbauer.lean
-- Second moment f₂ = E[cos² θ_G] = ((d - 1)σ^{2G} + 1) / d via harmonic-extension
-- polynomial identities and the 1D FTC recurrence from IsotropicError.lean.
--
-- Harmonic-extension geometry:
--   Boundary data on S^{d-1}: h(ξ) = (ξ · Φ)² = cos²θ (where ‖Φ‖ = 1).
--   Harmonic extension on B^d: H(x) = (x · Φ)² − ‖x‖²/d + 1/d.
--     Since Δ((x · Φ)²) = 2‖Φ‖² = 2 and Δ(‖x‖²/d) = 2d/d = 2, we have ΔH = 0 on B^d.
--     On the boundary S^{d-1} (where ‖ξ‖ = 1):
--       H(ξ) = (ξ · Φ)² − 1/d + 1/d = (ξ · Φ)² = h(ξ).
--   By the Poisson representation formula for harmonic functions on Euclidean balls
--   (Axler, Bourdon & Ramey, "Harmonic Function Theory", 2nd ed., 2001, Ch. 5):
--     H(x) = ∫_{S^{d-1}} P(x, ξ) h(ξ) dσ(ξ).
--   Evaluating at the interior point x = σΦ (with ‖x‖² = σ² and x · Φ = σ):
--     H(σΦ) = σ² − σ²/d + 1/d = ((d − 1)σ² + 1) / d.
--   Formally, `poissonIntegral_cos_sq` is proved directly for all `d ≥ 2` from
--   `integral_poissonMarginal_eq` and `halfcircle_cos_sq_eq` in `IsotropicError.lean`,
--   with `poissonIntegral_cos_sq_d2`, `poissonIntegral_cos_sq_d3`, and `f₂_formula` as
--   immediate corollaries.

import IsotropicGroverProof.Composition

/-!
# Second Moment `f₂` via Harmonic Extension and Poisson Integral

Evaluates `f₂ = E[cos² θ_G] = ((d - 1) σ^{2G} + 1) / d`.
-/

namespace IsotropicGrover

open Real MeasureTheory

/-! ## Harmonic polynomial decomposition: verified algebraic lemmas -/

/-- Algebraic cancellation in the Laplacian of the harmonic extension:
    Δ((x · Φ)²) − Δ(‖x‖²/d) = 2‖Φ‖² − 2d/d = 2 − 2 = 0 for any d ≠ 0. -/
lemma laplacian_trace_cancellation (d : ℝ) (hd : d ≠ 0) :
    (2 : ℝ) - (2 * d) / d = 0 := by
  rw [mul_div_cancel_right₀ 2 hd, sub_self]

/-- Boundary matching of the harmonic extension H(x) = (x · Φ)² − ‖x‖²/d + 1/d:
    on the unit sphere S^{d-1} where ‖ξ‖² = 1,
    H(ξ) = (ξ · Φ)² − 1/d + 1/d = (ξ · Φ)². -/
lemma harmonicExtension_boundary (d : ℝ) (dot : ℝ) :
    dot ^ 2 - (1 : ℝ) / d + 1 / d = dot ^ 2 := by
  ring

/-- Radial evaluation of the harmonic extension at x = σΦ (with ‖Φ‖ = 1, so ‖x‖ = σ):
    H(σΦ) = σ² − σ²/d + 1/d = ((d − 1) * σ² + 1) / d for any d ≠ 0. -/
lemma harmonicExtension_eval (d σ : ℝ) (hd : d ≠ 0) :
    σ ^ 2 - σ ^ 2 / d + 1 / d = ((d - 1) * σ ^ 2 + 1) / d := by
  field_simp [hd]

/-- Boundary limit of the second moment at σ = 1 (perfect gate fidelity):
    ((d − 1) * 1² + 1) / d = 1 for any d ≠ 0. -/
lemma poissonIntegral_val_sigma_one (d : ℝ) (hd : d ≠ 0) :
    ((d - 1 : ℝ) * (1 : ℝ) ^ 2 + 1) / d = 1 := by
  field_simp [hd]
  ring

/-- Center limit of the second moment at σ = 0 (complete decoherence / uniform Haar state):
    ((d − 1) * 0² + 1) / d = 1 / d for any d. -/
lemma poissonIntegral_val_sigma_zero (d : ℝ) :
    ((d - 1 : ℝ) * (0 : ℝ) ^ 2 + 1) / d = 1 / d := by
  ring

/-! ## Poisson integral formula for quadratic boundary data -/

/-- The second moment of the Poisson marginal for all dimensions `d ≥ 2`:
    `E_ν[cos² θ] = ((d - 1) σ² + 1) / d` for `θ ~ poissonMarginal d σ`.

    Geometrically, this corresponds to evaluating the harmonic extension
    `H(x) = (x · Φ)² - ‖x‖² / d + 1 / d` of `h(ξ) = (ξ · Φ)² = cos² θ` at the interior
    point `x = σ Φ` on the Euclidean ball `B^d` (Axler, Bourdon & Ramey,
    *Harmonic Function Theory*, 2nd ed., Ch. 5).
    Formally, it follows directly for all `d ≥ 2` from the generic marginal reduction
    `integral_poissonMarginal_eq` and the 1D FTC recurrence `halfcircle_cos_sq_eq`
    proved in `IsotropicError.lean`. -/
theorem poissonIntegral_cos_sq (d : ℕ) (σ : ℝ)
    (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) :
    ∫ θ, (cos θ) ^ 2 ∂(poissonMarginal d σ) =
    ((d - 1 : ℝ) * σ ^ 2 + 1) / d := by
  rw [integral_poissonMarginal_eq d σ hσ hd, halfcircle_cos_sq_eq d σ hσ hd,
      ← poissonNormConst_eq_intervalIntegral]
  exact mul_div_cancel_right₀ _ (poissonNormConst_pos d σ hσ hd).ne'

/-- Specialization of `poissonIntegral_cos_sq` to `d = 2`:
    `E[cos² θ] = ((2 - 1) σ² + 1) / 2`. -/
theorem poissonIntegral_cos_sq_d2 (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) :
    ∫ θ, (cos θ) ^ 2 ∂(poissonMarginal 2 σ) =
    ((2 - 1 : ℝ) * σ ^ 2 + 1) / 2 := by
  exact_mod_cast poissonIntegral_cos_sq 2 σ hσ (by norm_num)

/-- Specialization of `poissonIntegral_cos_sq` to `d ≥ 3` (retained for backwards
    compatibility as a theorem with zero custom axioms). -/
theorem poissonIntegral_cos_sq_d3 (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 3 ≤ d) :
    ∫ θ, (cos θ) ^ 2 ∂(poissonMarginal d σ) =
    ((d - 1 : ℝ) * σ ^ 2 + 1) / d :=
  poissonIntegral_cos_sq d σ hσ (by omega)

/-! ## The f₂ formula: E[cos²θ_G] = ((d−1)σ^{2G} + 1) / d -/

/-- The second moment f₂ = E[cos²θ_G] = ((d−1)σ^{2G} + 1) / d.
    Proof: composedMeasure d G σ = poissonMarginal d (σ^G) by definition.
    Apply poissonIntegral_cos_sq at σ := σ^G, then use (σ^G)² = σ^{2G}. -/
theorem f₂_formula (d_val G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (hd : 2 ≤ d_val) (hG : 0 < G) :
    f₂ d_val G σ = ((d_val - 1 : ℝ) * σ ^ (2 * G) + 1) / d_val := by
  rw [f₂, composedMeasure, poissonIntegral_cos_sq d_val (σ ^ G) (pow_mem_Ioo_zero_one hσ hG) hd,
      show (σ ^ G) ^ 2 = σ ^ (2 * G) by ring]

/-- Specialization of `f₂_formula` to `d = 2` (retained for backwards compatibility). -/
theorem f₂_formula_d2 (G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hG : 0 < G) :
    f₂ 2 G σ = ((2 - 1 : ℝ) * σ ^ (2 * G) + 1) / 2 := by
  exact_mod_cast f₂_formula 2 G σ hσ (by norm_num) hG

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

-- Numeric check: d=3 (minimal d ≥ 3 sphere), G=1, σ=1/2 → f₂ = 1/2
example : (((3 : ℝ) - 1) * (1/2 : ℝ) ^ (2 * 1) + 1) / 3 = 1/2 := by norm_num

-- Numeric check: d=4 (n=1 qubit, 2*2¹=4), G=1, σ=1/2 → f₂ = 7/16
example : (((4 : ℝ) - 1) * (1/2 : ℝ) ^ (2 * 1) + 1) / 4 = 7/16 := by norm_num

-- Numeric check: d=8 (n=2 qubits), G=1, σ=1/2 → f₂ = 11/32
example : (((8 : ℝ) - 1) * (1/2 : ℝ) ^ (2 * 1) + 1) / 8 = 11/32 := by norm_num

-- Numeric check: d=16 (n=3 qubits), G=1, σ=1/2 → f₂ = 19/64
example : (((16 : ℝ) - 1) * (1/2 : ℝ) ^ (2 * 1) + 1) / 16 = 19/64 := by norm_num

-- Numeric check: d=32 (n=4 qubits), G=1, σ=1/2 → f₂ = 35/128
example : (((32 : ℝ) - 1) * (1/2 : ℝ) ^ (2 * 1) + 1) / 32 = 35/128 := by norm_num

-- Numeric check: d=64 (n=5 qubits), G=1, σ=1/2 → f₂ = 67/256
example : (((64 : ℝ) - 1) * (1/2 : ℝ) ^ (2 * 1) + 1) / 64 = 67/256 := by norm_num

-- Ring identity: (σ^G)² = σ^{2G} (the key algebraic step in the proof)
example (σ : ℝ) (G : ℕ) : (σ ^ G) ^ 2 = σ ^ (2 * G) := by ring

/--
info: 'IsotropicGrover.poissonIntegral_cos_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms poissonIntegral_cos_sq

/--
info: 'IsotropicGrover.poissonIntegral_cos_sq_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms poissonIntegral_cos_sq_d3

/--
info: 'IsotropicGrover.f₂_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms f₂_formula

end IsotropicGrover
