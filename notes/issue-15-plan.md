# Implementation Plan: Issue #15 Refactor Second-Moment Matrix Derivation in §5

## Task Breakdown
1. **Design**: Document two-constraint framing in `docs/issue-15-design.md` (completed).
2. **Implementation**: Edit `english-proof.md` §5 (lines 159–175) to replace the 3-constraint framing with the clean 2-constraint framing:
   - Constraint 1: Subspace symmetry (orthogonal invariance on $V_\perp$, fixing $M = c P_{V_\perp}$).
   - Constraint 2: Normalization ($\mathrm{tr}(M) = 1$, fixing $c = 1/(d-1)$).
3. **Verification**: Inspect git diff, verify formatting and prose flow.
4. **Git & PR workflow**:
   - Commit changes to branch `issue-15`.
   - Push branch to `origin/issue-15`.
   - Open PR referencing issue #15.
   - Post PR review comment.
   - Ensure branch is up to date with `main`, squash and merge PR.
   - Verify issue #15 is closed.
