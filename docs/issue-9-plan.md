# Issue #9 Implementation Plan: Harmonic Extension Derivation and Documentation of d ≥ 3 Poisson Axiom

## Tasks

- [x] Task 1: Document harmonic extension derivation and add algebraic lemmas in `IsotropicGroverProof/Gegenbauer.lean`
  - Expand file docstring and docstring for `poissonIntegral_cos_sq_d3` with complete mathematical derivation:
    - Boundary data $h(\xi) = (\xi \cdot \Phi)^2 = \cos^2\theta$ on $S^{d-1}$.
    - Harmonic extension $H(\mathbf{x}) = (\mathbf{x} \cdot \Phi)^2 - |\mathbf{x}|^2/d + 1/d$ on $B^d$ satisfying $\Delta H = 0$ and $H|_{S^{d-1}} = h$.
    - Evaluation via Poisson representation formula at $\mathbf{x} = \sigma \Phi$ giving $H(\sigma \Phi) = \sigma^2 - \sigma^2/d + 1/d = ((d-1)\sigma^2 + 1)/d$.
    - Mathlib scope boundary discussion ($d = 2$ fully proved in `GegenbaurerHelper.lean` vs $d \ge 3$ awaiting Euclidean ball Poisson formula in Mathlib).
  - Add algebraic verification lemmas:
    - `laplacian_trace_cancellation`: trace cancellation $\Delta((\mathbf{x}\cdot\Phi)^2) - \Delta(|\mathbf{x}|^2/d) = 2 - 2d/d = 0$.
    - `harmonicExtension_boundary`: boundary matching $(\xi\cdot\Phi)^2 - 1/d + 1/d = (\xi\cdot\Phi)^2$.
    - `harmonicExtension_eval`: radial interior evaluation $\sigma^2 - \sigma^2/d + 1/d = ((d-1)\sigma^2 + 1)/d$.
    - `poissonIntegral_val_sigma_one`: boundary limit at $\sigma = 1$ equals 1.
    - `poissonIntegral_val_sigma_zero`: center limit at $\sigma = 0$ equals $1/d$.
  - Add TDD spot checks for $d = 3, 4, 8, 16, 32, 64$.

- [x] Task 2: Update `README.md` Axiom Footprint
  - Enhance Section "Axiom Footprint" with the mathematical basis, harmonic extension explanation, citation to Axler, Bourdon & Ramey (2001, Ch. 5), and Mathlib scope boundary.
  - Update issue list item 4 to reflect the thorough documentation and formal algebraic justification.

- [x] Task 3: Build and verify
  - Run `lake build` to confirm 0 errors, 0 warnings, 0 sorries.

- [x] Task 4: Review diff, commit, push, PR, review comment, and squash-merge
  - Review `git diff`.
  - Commit with message `docs: formalize harmonic derivation and document d >= 3 Poisson axiom (closes #9)`.
  - Push branch `issue-9`.
  - Create pull request with `gh pr create`.
  - Add review comment with `gh pr review --comment`.
  - Rebase if needed and squash-merge with `gh pr merge --squash --delete-branch`.
  - Verify issue #9 is closed.
