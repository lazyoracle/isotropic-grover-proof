# Issue #13 Implementation Plan: Ground Multi-Gate Error Accumulation in §6 Markov Induction

## Step 1: Design Review
- Review requirements from Issue #13 and align with the design in `docs/issue-13-design.md`.
- Ensure all 3 remediation items are fully addressed:
  1. Two distinct perspectives (single-step effective ansatz vs. sequential Markov chain).
  2. Grounding the headline formula $\mathrm{E}[p_e]$ in the §6 induction (no dependence on global commutativity or spherical convolution).
  3. Explicit cross-references to §6, Issue #6, and Issue #7.

## Step 2: Edit `english-proof.md` §3
- Restructure §3 with clear, rigorous headings and explanations:
  - Background: Commuting errors vs. sequential action.
  - Perspective A: The single-step effective error representation (ansatz).
  - Perspective B: Sequential gate-level Markov chain evolution.
  - Key reconciliation: Why $\mathrm{E}[p_e]$ does not depend on global spherical convolution (grounding in §6 induction).
  - Formalization note: Connection to Lean models and issues #6 and #7.

## Step 3: Review Git Diff
- Check `git diff` to ensure precision, clarity, and consistency with subsequent sections (§4–§7).

## Step 4: Commit and Push
- Commit: `docs: clarify multi-gate error accumulation and ground in §6 Markov induction (closes #13)`
- Push branch `issue-13` to origin.

## Step 5: Pull Request and Review
- Create PR linking Issue #13.
- Submit PR review comment.
- Rebase on origin/main if needed.
- Squash and merge PR.
- Verify Issue #13 is closed.
