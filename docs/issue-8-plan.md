# Issue #8 Implementation Plan: Formalize Grover State Vectors and Circuit Connection

## Tasks

- [x] Task 1: Create `IsotropicGroverProof/GroverCircuit.lean`
  - Define `targetBasisState` and prove `norm_targetBasisState` and `succProb_targetBasisState`.
  - Define `targetPerpState` and prove `inner_targetBasisState_targetPerpState`, `succProb_targetPerpState`, and `norm_targetPerpState`.
  - Define `uniformSuperposition` and prove `succProb_uniformSuperposition`, `norm_uniformSuperposition`, and `isotropicGrover_uniformSuperposition`.
  - Define `groverState2D` and prove `norm_groverState2D`, `succProb_groverState2D`, and `isotropicGrover_groverState2D`.
  - Define `groverState2D_prob` and prove `norm_groverState2D_prob`, `succProb_groverState2D_prob`, and `isotropicGrover_groverState2D_prob`.
  - Prove `isotropicGrover_targetBasisState` for the ideal output state.

- [x] Task 2: Document connection in `IsotropicGroverProof/MainTheorem.lean`
  - Add module docstring and theorem docstring annotations clarifying that `isotropicGrover_main` acts as the general geometric invariant engine that specializes to Grover's algorithm via `GroverCircuit.lean`.

- [x] Task 3: Export in `Basic.lean` and `IsotropicGroverProof.lean`
  - Add `import IsotropicGroverProof.GroverCircuit` to `IsotropicGroverProof/Basic.lean` and `IsotropicGroverProof.lean`.

- [x] Task 4: Build and verify
  - Run `lake build` to ensure 0 errors, 0 warnings, 0 sorries.

- [x] Task 5: Review diff, commit, push, PR, review comment, and squash-merge
  - Review `git diff`.
  - Commit with message `feat: formalize Grover state vectors and circuit connection (closes #8)`.
  - Push branch `issue-8`.
  - Open PR with title and body.
  - Add review comment.
  - Squash and merge PR, deleting remote branch.
  - Verify issue #8 is closed.
