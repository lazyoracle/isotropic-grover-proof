-- IsotropicGroverProof/Basic.lean
-- Barrel re-export file importing all 11 submodules in dependency order.

import IsotropicGroverProof.Defs
import IsotropicGroverProof.IsotropicError
import IsotropicGroverProof.Composition
import IsotropicGroverProof.CrossTerm
import IsotropicGroverProof.SecondMoment
import IsotropicGroverProof.Gegenbauer
import IsotropicGroverProof.Sequential
import IsotropicGroverProof.MainTheorem
import IsotropicGroverProof.LimitingCases
import IsotropicGroverProof.QuantumChannel
import IsotropicGroverProof.GroverCircuit

/-!
# Barrel Module for `IsotropicGroverProof`

Imports all 11 submodules in dependency order:
- `Defs`: real state space `E n`, unit sphere, standard basis vectors, dimension helpers, `succProb`
- `IsotropicError`: Poisson kernel marginal, closed-interval `poissonAngleMeasure`, 1D FTC moments
- `Composition`: effective `σ ^ G` perturbation measure `composedMeasure` and second moment `f₂`
- `CrossTerm`: equatorial sphere measure `perpSphereMeasure`, symmetries, and `expanded_E_pe`
- `SecondMoment`: equatorial second-moment operator, `decoherent_floor`, and bilinear expectations
- `Gegenbauer`: harmonic-extension identities and `poissonIntegral_cos_sq` / `f₂_formula`
- `Sequential`: `G`-gate fidelity recurrence and multi-gate pure-state Markov trajectories
- `MainTheorem`: effective-measure mixture theorem `isotropicGrover_main`
- `LimitingCases`: noiseless/decoherent limits, monotonicity, and `[0, 1]` continuity
- `QuantumChannel`: `QuantumInfo` `CPTPMap` depolarizing channel and `Circuit.size` bridge
- `GroverCircuit`: Grover search states, `Grover.p_succ` bridge, and 1- and 2-qubit circuits
-/
