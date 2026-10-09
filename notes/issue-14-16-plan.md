# Issue #14 & #16 Plan: Clarify Derivation Scope, Assumptions, and Formal Verification Footprint

## Tasks
1. [x] Inspect issue descriptions and related tracking issues (#6, #7, #8, #9, #14, #16).
2. [x] Create design document `docs/issue-14-16-design.md`.
3. [x] Create plan document `docs/issue-14-16-plan.md`.
4. [x] Update `README.md`:
   - Clarify derivation goal vs downstream repetition overhead $k(n)$.
   - Clarify empirical $G(n)$ vs theoretical approximations.
   - Add honest verification scope statement for Lean formalization.
   - Disclose axiom footprint (`poissonIntegral_cos_sq_d3` and foundational axioms).
   - Disclose open gaps and add links to tracking issues #6, #7, #8, #9.
   - Qualify exactness claim under the model assumptions.
5. [x] Update `english-proof.md`:
   - Clarify derivation goal and downstream application steps.
   - Note empirical vs asymptotic gate count $G(n)$.
   - Qualify exactness claim to reflect model assumptions.
   - Note connection between sequential error dynamics / induction and effective parameter assumptions.
6. [x] Verify links, markdown formatting, and consistency.
7. [ ] Review git diff and commit changes.
8. [ ] Push branch, open PR, add review comment, and squash-merge.
