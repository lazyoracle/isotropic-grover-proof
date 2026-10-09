-- IsotropicGroverProof/Gegenbauer.lean
-- M6: f₂ = E[cos²θ_G] via the Poisson integral formula and harmonic extension.
--
-- Approach (from english-proof.md §6):
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
--   By rotational symmetry around Φ, the surface integral against the Poisson kernel
--   reduces to the 1D marginal measure:
--     ∫ θ, cos²θ ∂(poissonMarginal d σ) = ((d − 1)σ² + 1) / d.
--   For G composed gates, substituting σ → σ^G gives f₂ = ((d − 1)σ^{2G} + 1) / d.
--
-- AXIOM STATUS & MATHLIB BOUNDARY:
--   - For d = 2: 100% formally verified without axioms in `GegenbaurerHelper.lean`
--     using Mathlib's complex Poisson integral formula on the unit disc
--     (`Mathlib.Analysis.Complex.Poisson`).
--   - For d ≥ 3: Axiomatized via `poissonIntegral_cos_sq_d3`. Mathlib currently lacks
--     the general Poisson representation formula and spherical harmonic decomposition
--     for Euclidean balls in ℝ^d (d ≥ 3). The axiom isolates this analytic boundary,
--     accompanied below by Lean-verified algebraic lemmas for the decomposition.
--   - Running `#print axioms isotropicGrover_main` confirms `poissonIntegral_cos_sq_d3`
--     is the sole non-foundational axiom in the entire project.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import IsotropicGroverProof.Composition
import IsotropicGroverProof.GegenbaurerHelper

namespace IsotropicGrover

open Real MeasureTheory

/-! ## Harmonic polynomial decomposition: verified algebraic lemmas -/

/-- Algebraic cancellation in the Laplacian of the harmonic extension:
    Δ((x · Φ)²) − Δ(‖x‖²/d) = 2‖Φ‖² − 2d/d = 2 − 2 = 0 for any d ≠ 0. -/
lemma laplacian_trace_cancellation (d : ℝ) (hd : d ≠ 0) :
    (2 : ℝ) - (2 * d) / d = 0 := by
  field_simp [hd]
  try ring

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
  try ring

/-- Boundary limit of the second moment at σ = 1 (perfect gate fidelity):
    ((d − 1) * 1² + 1) / d = 1 for any d ≠ 0. -/
lemma poissonIntegral_val_sigma_one (d : ℝ) (hd : d ≠ 0) :
    ((d - 1 : ℝ) * (1 : ℝ) ^ 2 + 1) / d = 1 := by
  field_simp [hd]
  try ring

/-- Center limit of the second moment at σ = 0 (complete decoherence / uniform Haar state):
    ((d − 1) * 0² + 1) / d = 1 / d for any d. -/
lemma poissonIntegral_val_sigma_zero (d : ℝ) :
    ((d - 1 : ℝ) * (0 : ℝ) ^ 2 + 1) / d = 1 / d := by
  ring

/-! ## Poisson integral formula for quadratic boundary data -/

/-- The second moment of the Poisson kernel on high-dimensional spheres (d ≥ 3).

    **Mathematical Derivation (Harmonic Extension):**
    1. Boundary data: On the unit sphere S^{d-1} ⊂ ℝ^d, let h(ξ) = (ξ · Φ)² = cos²θ,
       where ‖Φ‖ = 1.
    2. Harmonic polynomial extension: In the interior ball B^d, consider
       H(x) = (x · Φ)² − ‖x‖²/d + 1/d.
       - The Laplacian is ΔH = Δ((x · Φ)²) − Δ(‖x‖²/d) + Δ(1/d) = 2‖Φ‖² − 2d/d + 0 = 0.
       - On the boundary S^{d-1} (where ‖ξ‖ = 1), H(ξ) = (ξ · Φ)² − 1/d + 1/d = h(ξ).
    3. Poisson representation theorem (Axler, Bourdon & Ramey, "Harmonic Function Theory",
       2nd ed., Springer GTM 137, 2001, Ch. 5, Theorems 5.5 and 5.14):
       Every harmonic function continuous on the closed ball B^d satisfies
       H(x) = ∫_{S^{d-1}} P(x, ξ) h(ξ) dσ(ξ).
    4. Interior evaluation: At the point x = σΦ (with σ ∈ (0, 1)):
       H(σΦ) = (σΦ · Φ)² − ‖σΦ‖²/d + 1/d = σ² − σ²/d + 1/d = ((d − 1)σ² + 1) / d.
    5. Marginalization: By rotational symmetry around Φ, the sphere integral reduces to the
       1D polar marginal measure `poissonMarginal d σ`:
       ∫ θ, (cos θ)² ∂(poissonMarginal d σ) = ((d − 1)σ² + 1) / d.

    **Why Mathlib requires an axiom for d ≥ 3:**
    Mathlib contains the Poisson representation formula on the unit disc in ℂ
    (`Mathlib.Analysis.Complex.Poisson`), which is used to fully prove the d = 2 case
    in `GegenbaurerHelper.lean` with 0 non-foundational axioms.
    However, general d-dimensional spherical harmonics and the Poisson representation formula
    for Euclidean balls in ℝ^d (d ≥ 3) are not yet formalized in Mathlib.
    This axiom isolates that external mathematical fact. -/
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
    (hd : 2 ≤ d_val) (hG : 0 < G) :
    f₂ d_val G σ = ((d_val - 1 : ℝ) * σ ^ (2 * G) + 1) / d_val := by
  simp only [f₂, composedMeasure]
  have hσG : σ ^ G ∈ Set.Ioo 0 1 :=
    ⟨pow_pos hσ.1 G, pow_lt_one₀ hσ.1.le hσ.2 hG.ne'⟩
  rw [poissonIntegral_cos_sq d_val (σ ^ G) hσG hd]
  have hpow : (σ ^ G) ^ 2 = σ ^ (2 * G) := by ring
  rw [hpow]

/-- The second moment f₂ for d = 2, proved directly using `poissonIntegral_cos_sq_d2`
    without invoking the d ≥ 3 Poisson integral formula axiom. -/
theorem f₂_formula_d2 (G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hG : 0 < G) :
    f₂ 2 G σ = ((2 - 1 : ℝ) * σ ^ (2 * G) + 1) / 2 := by
  simp only [f₂, composedMeasure]
  have hσG : σ ^ G ∈ Set.Ioo 0 1 :=
    ⟨pow_pos hσ.1 G, pow_lt_one₀ hσ.1.le hσ.2 hG.ne'⟩
  rw [poissonIntegral_cos_sq_d2 (σ ^ G) hσG]
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

end IsotropicGrover
