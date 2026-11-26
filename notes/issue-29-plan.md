# Eliminate `poissonIntegral_cos_sq_d3` Axiom Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove `poissonIntegral_cos_sq` and `poissonMarginal_mean_cos` for all $d \ge 2$ via 1D calculus, delete `axiom poissonIntegral_cos_sq_d3` and the redundant `GegenbaurerHelper.lean`, and enforce zero custom axioms in CI.

**Architecture:** Establish a generic `withDensity` → `intervalIntegral` lemma in `IsotropicError.lean`, prove the 1D FTC recurrence identities (`F̃₀`, `G̃₀`, `G̃₁`) and the $d = 3$ base case (`H̃₃`), deduce both the first moment $\mathbb{E}[\cos\theta] = \sigma$ and second moment $\mathbb{E}[\cos^2\theta] = \frac{(d-1)\sigma^2+1}{d}$ for all $d \ge 2$ by two-step structural induction on $d$, remove `GegenbaurerHelper.lean`, and enable `axiom-audit: true` in CI.

**Tech Stack:** Lean 4 (`v4.35.0`), Mathlib (`intervalIntegral`, `HasDerivAt`), `leanprover/lean-action@v1` (`axiom-audit`).

**Spec:** `notes/issue-29-design.md`

## Global Constraints

- **Worktree isolation:** Work strictly inside `/home/anurag/isotropic-grover-proof/.claude/worktrees/issue-29`. Never modify `/home/anurag/isotropic-grover-proof` directly.
- **Lean binary path:** Always include `$HOME/.elan/bin` on `PATH` when invoking `lean` or `lake`.
- **Zero non-standard axioms & zero `sorry`s:** Every declaration in `IsotropicGroverProof` must depend exclusively on a subset of `[propext, Classical.choice, Quot.sound]`, with 0 `sorry`s and 0 warnings (`lake build --wfail`).
- **Backwards-compatible theorem names:** Preserve `poissonMarginal_mean_cos_d2`, `poissonIntegral_cos_sq`, `poissonIntegral_cos_sq_d2`, `poissonIntegral_cos_sq_d3` (now a `theorem`, not an `axiom`), `f₂_formula`, and `f₂_formula_d2` so downstream modules compile seamlessly.
- **Documentation directory:** Never create a top-level `docs/` directory.

## Review Focus

- `d = 2` exponent edge case in `sin θ ^ (d - 2)` derivative: when differentiating `sin θ ^ (d - 1)` for `d ≥ 2`, `d - 1 ≥ 1` so `HasDerivAt.pow` gives `((d - 1 : ℕ) : ℝ) * sin θ ^ (d - 2) * cos θ` cleanly even when `d = 2` (`d - 2 = 0`); verify `((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1` using `Nat.cast_sub (by omega : 1 ≤ d)`.
- `Real.rpow` derivative and exponent arithmetic on $D(\sigma, \theta) = 1 + \sigma^2 - 2\sigma\cos\theta$: always supply `(denom_pos σ θ hσ).ne'` (or `Or.inl (denom_pos σ θ hσ).ne'`) to `HasDerivAt.rpow_const`, and use `Real.rpow_neg (denom_pos σ θ hσ).le` / `Real.rpow_add (denom_pos σ θ hσ)` to relate `D ^ (-(d : ℝ) / 2 - 1)` to `/ D ^ (((d + 2 : ℕ) : ℝ) / 2)`.
- Endpoint square-root signs in $d = 3$ base case: for $\sigma \in (0, 1)$, $1 - \sigma > 0$ and $1 + \sigma > 0$, so `((1 - σ) ^ 2) ^ (1 / 2 : ℝ) = 1 - σ` and `((1 + σ) ^ 2) ^ (1 / 2 : ℝ) = 1 + σ` without absolute-value sign flips.
- Deleting `GegenbaurerHelper.lean`: ensure no module in `IsotropicGroverProof/` still imports `IsotropicGroverProof.GegenbaurerHelper` and remove stale `.olean`s if needed.
- `#guard_msgs in #print axioms` exact axiom list: confirm `isotropicGrover_main` prints `[propext, Classical.choice, Quot.sound]` with zero custom axioms.

---

### Task 1: Prove Generic `poissonMarginal` Expectation Reduction, $d = 3$ Base Case, and All-$d$ First & Second Moment Recurrences in `IsotropicError.lean`

**Files:**
- Modify: `IsotropicGroverProof/IsotropicError.lean`
- Modify: `IsotropicGroverProof/Composition.lean` (optional corollary `composedMeasure_mean_cos` for all $d \ge 2$)

**Interfaces:**
- Consumes: `poissonKernelDensity`, `poissonNormConst`, `poissonMarginal`, `halfcircle_cos_d2`, `halfcircle_norm_d2` in `IsotropicError.lean`
- Produces:
  - `lemma integral_poissonMarginal_eq (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) (f : ℝ → ℝ) : ∫ θ, f θ ∂(poissonMarginal d σ) = (∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * f θ) / poissonNormConst d σ`
  - `theorem poissonMarginal_mean_cos (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) : ∫ θ, cos θ ∂(poissonMarginal d σ) = σ`
  - `theorem halfcircle_cos_sq_eq (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) : ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ * cos θ ^ 2 = ((d - 1 : ℝ) * σ ^ 2 + 1) / d * ∫ θ in (0 : ℝ)..Real.pi, poissonKernelDensity d σ θ`

- [ ] **Step 1: Write failing `#check` / `#guard_msgs` tests for `poissonMarginal_mean_cos` and `halfcircle_cos_sq_eq` (RED)**

Add `#check @poissonMarginal_mean_cos` and `#check @halfcircle_cos_sq_eq` at the bottom of `IsotropicError.lean` and run `PATH="$HOME/.elan/bin:$PATH" lake build IsotropicGroverProof.IsotropicError` to confirm expected missing-declaration failure.

- [ ] **Step 2: Implement `integral_poissonMarginal_eq`, the 1D FTC identities (`F̃₀`, `G̃₀`, `G̃₁`, `H̃₃`), and two-step induction in `IsotropicError.lean` (GREEN)**

Import `Mathlib.Analysis.SpecialFunctions.Pow.Deriv` (and `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv` if needed).
1. Factor out `integral_poissonMarginal_eq` for all `d ≥ 2` and arbitrary `f : ℝ → ℝ`, and simplify `poissonMarginal_mean_cos_d2` to use it.
2. Prove the 3-term FTC identity from $\tilde{F}_0(\theta) = (1 - \sigma^2)\sin^{d-1}\theta \cdot D(\sigma, \theta)^{1 - (d : \mathbb{R}) / 2}$ via `intervalIntegral.integral_eq_sub_of_hasDerivAt`:
   `σ * d * I₂(d) = (d - 1) * (1 + σ ^ 2) * I₁(d) - (d - 2) * σ * I₀(d)`.
3. Prove the $d \mapsto d + 2$ step identities from $\tilde{G}_0(\theta) = (1 - \sigma^2)\sin^{d-1}\theta \cdot D(\sigma, \theta)^{-(d : \mathbb{R}) / 2}$ and $\tilde{G}_1(\theta) = (1 - \sigma^2)\cos\theta \sin^{d-1}\theta \cdot D(\sigma, \theta)^{-(d : \mathbb{R}) / 2}$, deducing `I₁(d) = σ * I₀(d) → I₁(d + 2) = σ * I₀(d + 2)`.
4. Prove the $d = 3$ base case `I₁(3) = σ * I₀(3)` from $\tilde{H}_3(\theta) = -(1 - \sigma^2) * ((1 - \sigma^2) * D(\sigma, \theta) ^ (-(1 : ℝ) / 2) + D(\sigma, \theta) ^ ((1 : ℝ) / 2)) / (2 * \sigma ^ 2)`.
5. Combine $d = 2$, $d = 3$, and $d \mapsto d + 2$ (`| 0 | 1 => omega | 2 => ... | 3 => ... | d + 4 => ...`) to prove `halfcircle_cos_eq`, `poissonMarginal_mean_cos`, and `halfcircle_cos_sq_eq` for all $d \ge 2$ (and add `composedMeasure_mean_cos` for all $d \ge 2$ in `Composition.lean`).

- [ ] **Step 3: Verify `IsotropicError` and `Composition` build with zero warnings and zero custom axioms**

Run: `PATH="$HOME/.elan/bin:$PATH" lake build IsotropicGroverProof.IsotropicError IsotropicGroverProof.Composition --wfail`
Expected: Exit code 0, zero warnings, `#guard_msgs in #print axioms poissonMarginal_mean_cos` shows only `[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 4: Commit**

```bash
git add notes/issue-29-design.md notes/issue-29-plan.md IsotropicGroverProof/IsotropicError.lean IsotropicGroverProof/Composition.lean
git commit -m "feat: prove all-dimension Poisson first and second moment recurrences via 1D FTC"
```

### Task 2: Replace `axiom poissonIntegral_cos_sq_d3` with Theorem, Delete `GegenbaurerHelper.lean`, and Enforce CI `axiom-audit`

**Files:**
- Delete: `IsotropicGroverProof/GegenbaurerHelper.lean`
- Modify: `IsotropicGroverProof/Gegenbauer.lean`
- Modify: `IsotropicGroverProof/MainTheorem.lean`
- Modify: `.github/workflows/lean_action_ci.yml`

**Interfaces:**
- Consumes: `integral_poissonMarginal_eq` and `halfcircle_cos_sq_eq` from Task 1.
- Produces: Zero-custom-axiom `poissonIntegral_cos_sq`, `poissonIntegral_cos_sq_d3`, `poissonIntegral_cos_sq_d2`, `isotropicGrover_main`, and CI `axiom-audit: true`.

- [ ] **Step 1: Update `#guard_msgs in #print axioms isotropicGrover_main` in `MainTheorem.lean` to reject `poissonIntegral_cos_sq_d3` (RED)**

Change the expected `#guard_msgs` docstring in `IsotropicGroverProof/MainTheorem.lean:129-136` to `[propext, Classical.choice, Quot.sound]` and run `PATH="$HOME/.elan/bin:$PATH" lake build IsotropicGroverProof.MainTheorem` to observe the RED failure showing `poissonIntegral_cos_sq_d3` is still present.

- [ ] **Step 2: Prove `poissonIntegral_cos_sq` and `poissonIntegral_cos_sq_d3` in `Gegenbauer.lean` and delete `GegenbaurerHelper.lean` (GREEN)**

1. Remove `import IsotropicGroverProof.GegenbaurerHelper` from `Gegenbauer.lean` and delete `IsotropicGroverProof/GegenbaurerHelper.lean` (`git rm IsotropicGroverProof/GegenbaurerHelper.lean`).
2. Prove `theorem poissonIntegral_cos_sq` directly for all `d ≥ 2` from `integral_poissonMarginal_eq` + `halfcircle_cos_sq_eq` + `(poissonNormConst_pos ...).ne'`, and derive `theorem poissonIntegral_cos_sq_d2` and `theorem poissonIntegral_cos_sq_d3` as 1-line corollaries (removing `axiom poissonIntegral_cos_sq_d3` completely!). Update comments/docstrings in `Gegenbauer.lean` and `MainTheorem.lean` accurately.
3. Add `#guard_msgs in #print axioms` guards in `MainTheorem.lean` and `GroverCircuit.lean` confirming `[propext, Classical.choice, Quot.sound]` on `isotropicGrover_main` and `isotropicGrover_groverState2D`.
4. In `.github/workflows/lean_action_ci.yml`, add `axiom-audit: true` and `axiom-audit-root: 'IsotropicGroverProof'` to the `Build project` `leanprover/lean-action@v1` step.

- [ ] **Step 3: Run full `lake build --wfail` and verify zero custom axioms across the repo**

Run:
```bash
grep -rn '\baxiom\b' IsotropicGroverProof/ || true
PATH="$HOME/.elan/bin:$PATH" lake build --wfail
```
Expected: Zero `axiom` declarations in `IsotropicGroverProof/`, `lake build --wfail` exits 0 with 0 errors and 0 warnings.

- [ ] **Step 4: Commit**

```bash
git add -A IsotropicGroverProof .github/workflows/lean_action_ci.yml
git commit -m "feat: eliminate poissonIntegral_cos_sq_d3 axiom, remove GegenbaurerHelper, and enable CI axiom-audit"
```
