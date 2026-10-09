# Design Document: Issue #11 - Document First Moment as Auxiliary and Remove Unused Axiom

## Context & Motivation

In `IsotropicGroverProof/IsotropicError.lean`, the first moment $E[\cos \theta] = \sigma$ was formalized using:
- `poissonMarginal_mean_cos_d3`: an axiom asserting $E[\cos \theta] = \sigma$ for $d \ge 3$ (cited from Axler, Bourdon & Ramey).
- `poissonMarginal_mean_cos`: a theorem for $d \ge 2$ combining the complex Poisson integral proof for $d = 2$ with the axiom for $d \ge 3$.

In `IsotropicGroverProof/Composition.lean`, this was extended to:
- `composedMeasure_mean_cos`: showing $E[\cos \theta_G] = \sigma^G$ for $d \ge 2$.

However:
- The main theorem `isotropicGrover_main` depends only on the second moment $F = E[\cos^2 \theta]$ (via `f₂_formula` and `expanded_E_pe`).
- `#print axioms isotropicGrover_main` confirms neither `poissonMarginal_mean_cos` nor `poissonMarginal_mean_cos_d3` is in the transitive dependency graph of `isotropicGrover_main`.
- English paper §2/§3 motivates the isotropic noise model by $E[\cos \theta] = \sigma$, making this a valuable auxiliary property for understanding and sanity checking, but an unnecessary axiom footprint if $d \ge 3$ relies on an unproven axiom.

## Proposed Changes

1. **Remove `poissonMarginal_mean_cos_d3` axiom**:
   - Delete `axiom poissonMarginal_mean_cos_d3` from `IsotropicGroverProof/IsotropicError.lean`.
   - Update file comments to reflect 0 sorries and 0 axioms in `IsotropicError.lean`.

2. **Retain $d = 2$ theorem as auxiliary property**:
   - Replace `poissonMarginal_mean_cos` with `poissonMarginal_mean_cos_d2`, retaining the fully verified complex Poisson integral proof without needing any axioms.
   - Add clear module and docstring documentation explaining that $E[\cos \theta] = \sigma$ is an auxiliary property not used by `isotropicGrover_main`.

3. **Update `IsotropicGroverProof/Composition.lean`**:
   - Update `composedMeasure_mean_cos` to `composedMeasure_mean_cos_d2` (or adjust docstrings accordingly).
   - Document that it is an auxiliary property showing $E[\cos \theta_G] = \sigma^G$ for $d = 2$, not required by `isotropicGrover_main`.
   - Update the TDD spot-check example to reference `composedMeasure_mean_cos_d2`.

4. **Verify Axiom Footprint and Build**:
   - Run `lake build` to confirm 0 errors, 0 warnings, 0 sorries.
   - Confirm only the intended single external axiom (`poissonIntegral_cos_sq_d3` in `Gegenbauer.lean`) remains in `isotropicGrover_main`.
