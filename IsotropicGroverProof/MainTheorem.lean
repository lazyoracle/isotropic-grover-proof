-- IsotropicGroverProof/MainTheorem.lean
-- Effective-measure mixture theorem isotropicGrover_main: combines expanded_E_pe,
-- decoherent_floor, and f₂_formula to establish
--   E[p_e] = σ^{2G} · p_ideal + (1 - σ^{2G}) / 2^n
-- for any unit state Φ ∈ E n, gate count G > 0, and σ ∈ (0, 1).
-- Gate-by-gate pure-state trajectories, CPTPMap channels, and syntactic Circuit n
-- generalizations across σ ∈ [0, 1] and all G : ℕ are proved in Sequential.lean,
-- QuantumChannel.lean, and GroverCircuit.lean.

import IsotropicGroverProof.SecondMoment
import IsotropicGroverProof.Gegenbauer

/-!
# Main Mixture Theorem for Isotropic Grover Errors

Combines the expanded expectation, decoherent floor, and second-moment formula to prove
`E[p_e] = σ^{2G} · p_ideal + (1 - σ^{2G}) / 2^n`.
-/

namespace IsotropicGrover

open Real MeasureTheory

variable {n : ℕ}

/-! ## Main theorem

`isotropicGrover_main` establishes the exact `σ^{2G}` mixture formula under the effective
measure `composedMeasure (d n) G σ` for any unit vector `Φ ∈ E n`, gate count `G > 0`, and
`σ ∈ (0, 1)`, relying on the spherical symmetry of the isotropic error measure.

Downstream modules extend and specialize this result:
- `IsotropicGroverProof.Sequential` generalizes the mixture formula to gate-by-gate pure-state
  Markov trajectories (`noisyTrajectory_succProb`) across all `σ ∈ [0, 1]` and `G : ℕ`.
- `IsotropicGroverProof.QuantumChannel` bridges isotropic sphere perturbations to `QuantumInfo`
  `CPTPMap` depolarizing channels and `QuantumComputation` syntactic `Circuit.size`
  (`noisyCircuit_bornProb`).
- `IsotropicGroverProof.GroverCircuit` specializes both `isotropicGrover_main` and the
  `QuantumInfo` / `QuantumComputation` channel theorems to Grover's algorithm (`Grover.p_succ`),
  covering `uniformSuperposition`, `groverState2D`, `groverState2D_prob`, `targetBasisState`,
  canonical macro-gate sequences, and concrete 1- and 2-qubit primitive-gate circuits.
-/

/-- **The σ^{2G} mixture formula.**
    The expected success probability on n qubits subject to G independent isotropic
    errors with per-gate fidelity parameter σ ∈ (0,1) is:

        E[p_e] = σ^{2G} · p_ideal + (1 - σ^{2G}) / N

    where N = 2^n is the database size, p_ideal = succProb n Φ w is the ideal
    success probability of the unit vector Φ, and G is the gate count.

    This theorem serves as the geometric invariant engine: its general unit-vector
    invariance specializes directly to Grover's algorithm components via `GroverCircuit.lean`.
    The formula interpolates between perfect fidelity (σ^{2G} = 1) and uniform
    random guessing (σ^{2G} = 0). No approximations are made — all finite-d
    corrections cancel exactly in the algebra below. -/
theorem isotropicGrover_main (G : ℕ) (hG : 0 < G) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (Φ : E n) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ n)) :
    ∫ θ, ∫ e₂, succProb n (isotropicError Φ e₂ θ) w
          ∂(perpSphereMeasure Φ)
      ∂(composedMeasure (d n) G σ) =
    σ ^ (2 * G) * succProb n Φ w + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ) := by
  have hd2 := two_le_d n
  rw [expanded_E_pe G hG σ hσ Φ hΦ w,
      decoherent_floor Φ hΦ w hd2,
      f₂_formula (d n) G σ hσ hd2 hG]
  have hd_ne := cast_d_ne_zero n
  have hd1_ne := cast_d_sub_one_ne_zero n
  have hN_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp [hd_ne, hd1_ne, hN_ne]
  rw [cast_d n]
  ring

/-- Specialization of `isotropicGrover_main` to `n = 0` (`d = 2`, retained for backwards
    compatibility). -/
theorem isotropicGrover_n0 (G : ℕ) (hG : 0 < G) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1)
    (Φ : E 0) (hΦ : ‖Φ‖ = 1) (w : Fin (2 ^ 0)) :
    ∫ θ, ∫ e₂, succProb 0 (isotropicError Φ e₂ θ) w
          ∂(perpSphereMeasure Φ)
      ∂(composedMeasure (d 0) G σ) =
    σ ^ (2 * G) * succProb 0 Φ w + (1 - σ ^ (2 * G)) / (2 ^ 0 : ℝ) :=
  isotropicGrover_main G hG σ hσ Φ hΦ w

/-! ## Verification spot-checks -/

-- Exact algebraic cancellation of finite-d factors:
-- f₂ · p + (1 - f₂) · (2 - p) / (d - 1) = σ^{2G} · p + (1 - σ^{2G}) / N
-- when f₂ = ((d - 1)σ^{2G} + 1) / d and d = 2N.
example (p σ2G : ℝ) (N : ℕ) (hN : 0 < N) :
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

#check @isotropicGrover_main
#check @isotropicGrover_n0

/--
info: 'IsotropicGrover.isotropicGrover_main' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isotropicGrover_main

/--
info: 'IsotropicGrover.isotropicGrover_n0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isotropicGrover_n0

end IsotropicGrover
