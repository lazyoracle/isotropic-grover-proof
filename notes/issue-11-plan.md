# Implementation Plan: Issue #11

- [x] Step 1: Inspect issue #11, `IsotropicGroverProof/IsotropicError.lean`, and `IsotropicGroverProof/Composition.lean`.
- [x] Step 2: Create design document `docs/issue-11-design.md`.
- [x] Step 3: Create plan `docs/issue-11-plan.md`.
- [x] Step 4: Implement changes in `IsotropicGroverProof/IsotropicError.lean` and `IsotropicGroverProof/Composition.lean`.
  - Remove axiom `poissonMarginal_mean_cos_d3`.
  - Refactor `poissonMarginal_mean_cos` to `poissonMarginal_mean_cos_d2` (0 axioms, proved via complex Poisson).
  - Add docstrings clarifying that the first moment is an auxiliary property.
  - Refactor `composedMeasure_mean_cos` to `composedMeasure_mean_cos_d2` and update spot-check.
- [x] Step 5: Run `lake build` to verify clean build (0 errors, 0 warnings, 0 sorries).
- [x] Step 6: Verify axiom footprint of `isotropicGrover_main`.
- [x] Step 7: Check git diff.
- [ ] Step 8: Commit changes.
- [ ] Step 9: Push branch `issue-11`.
- [ ] Step 10: Create PR.
- [ ] Step 11: Add PR review comment.
- [ ] Step 12: Rebase on main if needed.
- [ ] Step 13: Squash and merge PR.
- [ ] Step 14: Verify issue #11 closed.
