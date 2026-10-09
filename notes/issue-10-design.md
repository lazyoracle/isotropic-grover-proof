# Issue #10 Design Document: Eliminate dead d=2 code by relaxing n ≥ 2 in `isotropicGrover_main`

## Problem Context
In `IsotropicGroverProof/MainTheorem.lean`, `isotropicGrover_main` historically required `hn : 2 ≤ n`.
Since $d(n) = 2 \cdot 2^n$, $n \ge 2$ implied $d(n) \ge 8$.
In `IsotropicGroverProof/Gegenbauer.lean`, `poissonIntegral_cos_sq` splits on $d = 2$ (fully proved in `GegenbaurerHelper.lean`) vs $d \ge 3$ (axiomatized via `poissonIntegral_cos_sq_d3`).
Because $n \ge 2$ was required, the $d = 2$ branch was completely unreachable from `isotropicGrover_main`, leaving the ~300 lines of fully proved analytic work in `GegenbaurerHelper.lean` unused by the main theorem.
Moreover, $d(n) = 2 \cdot 2^n \ge 2$ holds for all $n \in \mathbb{N}$ (since $2^n \ge 1$), including $n = 0$ where $d = 2$.
Furthermore, `f₂_formula` only intrinsically requires $2 \le d$ because its proof delegates to `poissonIntegral_cos_sq` at dimension $d$.

## Goals
1. In `IsotropicGroverProof/Gegenbauer.lean`:
   - Relax `f₂_formula` hypothesis from `(hd : 3 ≤ d_val)` to `(hd : 2 ≤ d_val)`.
   - Provide `f₂_formula_d2` specialized for $d = 2$ calling `poissonIntegral_cos_sq_d2` directly, ensuring an axiom-free second-moment path for $d = 2$.
2. In `IsotropicGroverProof/MainTheorem.lean`:
   - Remove `(hn : 2 ≤ n)` from `isotropicGrover_main`, enabling it for all $n : \mathbb{N}$.
   - Prove $2 \le d(n)$ unconditionally for all $n$ via `Nat.one_le_two_pow`.
   - Provide `isotropicGrover_n0` for $n = 0$ ($d = 2$) and verify that its transitive axioms do not contain `poissonIntegral_cos_sq_d3`.
3. In `IsotropicGroverProof/LimitingCases.lean`:
   - Remove `(hn : 2 ≤ n)` from all callers:
     - `isotropicGrover_lhs_eq_mixtureProb`
     - `tendsto_expectedSuccProb_as_sigma_one`
     - `tendsto_expectedSuccProb_as_sigma_one_left`
     - `tendsto_expectedSuccProb_as_sigma_zero`
     - `tendsto_expectedSuccProb_as_sigma_zero_right`
4. Verify complete build without sorries or warnings and check axiom dependencies.
