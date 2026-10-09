# Issue #10 Implementation Plan: Eliminate Dead d=2 Code

## Tasks

- [x] Task 1: Relax `f₂_formula` and add `f₂_formula_d2` in `IsotropicGroverProof/Gegenbauer.lean`
  - Change `(hd : 3 ≤ d_val)` to `(hd : 2 ≤ d_val)` in `f₂_formula`.
  - Add `f₂_formula_d2` evaluating $f_2(2, G, \sigma)$ via `poissonIntegral_cos_sq_d2`.
- [x] Task 2: Relax `isotropicGrover_main` and add `isotropicGrover_n0` in `IsotropicGroverProof/MainTheorem.lean`
  - Remove `(hn : 2 ≤ n)` from `isotropicGrover_main`.
  - Prove `2 ≤ d n` unconditionally and remove `hd3`.
  - Add `isotropicGrover_n0` specialized for $n = 0$ using `f₂_formula_d2`.
  - Add axiom check / spot check demonstrating zero reliance on `poissonIntegral_cos_sq_d3` for $n=0$.
- [x] Task 3: Update callers in `IsotropicGroverProof/LimitingCases.lean`
  - Remove `(hn : 2 ≤ n)` from `isotropicGrover_lhs_eq_mixtureProb`, `tendsto_expectedSuccProb_as_sigma_one`, `tendsto_expectedSuccProb_as_sigma_one_left`, `tendsto_expectedSuccProb_as_sigma_zero`, and `tendsto_expectedSuccProb_as_sigma_zero_right`.
- [x] Task 4: Build, verify axioms, test, and commit
  - Run `lake build` to ensure 0 errors, 0 warnings, 0 sorries.
  - Verify `#print axioms isotropicGrover_n0` only uses standard axioms.
  - Push branch, create PR, add review comment, squash merge, and close issue #10.
