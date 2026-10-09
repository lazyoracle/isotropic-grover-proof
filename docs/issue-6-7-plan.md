# Issue #6 & #7 Implementation Plan: Sequential Markov Error Induction

## Tasks

- [x] Task 1: Create `IsotropicGroverProof/Sequential.lean`
  - Define `stepLambda`, `stepTransition`, and `sequentialFidelity`.
  - Prove contraction lemma `stepTransition_sub_inv_d` (and optionally `stepTransition_eq`).
  - Prove `sequentialFidelity_eq` by induction on $k$.
  - Prove `sequentialFidelity_eq_f₂` connecting sequential Markov accumulation with `f₂`.
  - Prove `sequential_mixture_formula` deriving the exact mixture formula from sequential fidelity.
  - Add TDD spot checks and verify clean compilation.

- [x] Task 2: Update `IsotropicGroverProof/Composition.lean`
  - Document that `isotropicComposition` is a nominal placeholder / deprecated.
  - Reference `Sequential.lean` as the rigorous physical derivation of sequential error accumulation.

- [x] Task 3: Export `Sequential.lean`
  - Add `import IsotropicGroverProof.Sequential` to `IsotropicGroverProof/Basic.lean` and `IsotropicGroverProof.lean`.

- [x] Task 4: Verify build and git status
  - Run `lake build` to confirm 0 errors, 0 warnings, 0 sorries.
  - Inspect `git diff`.

- [x] Task 5: Commit, Push, PR, Review, and Merge
  - Commit changes with message `feat: formalize sequential Markov error induction (closes #6, closes #7)`.
  - Push branch `issue-6-7` to origin.
  - Create PR with title `[C1][C2] Formalize sequential Markov chain error induction`.
  - Post review comment on PR.
  - Fetch/rebase if needed, squash and merge with branch deletion.
  - Verify Issues #6 and #7 are closed.
