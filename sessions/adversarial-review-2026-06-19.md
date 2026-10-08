# Adversarial Peer Review — Isotropic Grover Proof

**Date:** 2026-06-19
**Reviewer role:** Critical peer reviewer (adversarial), checking both `english-proof.md` and the Lean formalization
**Toolchain checked:** `leanprover/lean4:v4.29.0-rc6` + `mathlib v4.29.0-rc6`
**Build:** `lake build` succeeds; **0 sorries**; `#print axioms isotropicGrover_main` →
`[propext, Classical.choice, poissonIntegral_cos_sq_d3, Quot.sound]`

---

## Verdict up front

The repository compiles, has **zero `sorry`s**, and the final theorem has a clean axiom
footprint. But "sorry-free" is doing misleading work here. The machine-checked theorem
`isotropicGrover_main` is **true and internally consistent**, yet it **does not prove what
the README and `english-proof.md` claim it proves**.

The two genuinely hard, load-bearing steps of the physics — the multi-gate composition (§3)
and the structural form of the noisy Grover state — are **assumed by definition**, one of
them behind a **vacuous `:= rfl` "theorem"**. The mathematical content that *is* formalized
(cross-term cancellation, second-moment matrix, decoherent floor, final algebra, d=2 Poisson
integral) is high quality. **The gap is one of scope and faithfulness, not arithmetic.**

### Evidence gathered

- Built the project and ran `#print axioms isotropicGrover_main`. Only one non-foundational
  axiom appears: `poissonIntegral_cos_sq_d3`. Crucially, **`isotropicComposition` and
  `poissonMarginal_mean_cos_d3` do NOT appear** — they are unused by the main result.
- Numerically verified the axiomatized value `∫ cos²θ ∂(poissonMarginal d σ) =
  ((d-1)σ²+1)/d` against the project's *own* `poissonKernelDensity` definition for
  d ∈ {2,3,4,8}, σ ∈ {0.3,0.5,0.9}. It matches to ~1e-5 in every case. The axiom is correct;
  it is simply axiomatized rather than proved.

---

## CRITICAL ISSUES

### C1. The composition law (§3) is not proved — it is a tautology plus a definition

`Composition.lean:20-26`:

```lean
theorem isotropicComposition (d : ℕ) (σ₁ σ₂ : ℝ) ... :
    poissonMarginal d (σ₁ * σ₂) = poissonMarginal d (σ₁ * σ₂) := rfl
```

This "theorem" states `X = X`. It says **nothing** about convolution, composition, or σ^G.
The in-source comment admits it: *"Formal statement of the convolution identity is deferred
to a future session."* It is a placeholder dressed up with a citation to Lacalle & Pozo
Coronado.

The actual reduction is then smuggled in as a **definition** (`Composition.lean:33`):

```lean
noncomputable def composedMeasure (d G : ℕ) (σ : ℝ) : Measure ℝ := poissonMarginal d (σ ^ G)
```

So "G independent gate errors collapse to a single effective error with parameter σ^G" — the
entire point of §3, the step that links per-gate fidelity to circuit-level fidelity — is
**asserted by fiat**, never derived. `#print axioms` confirms `isotropicComposition` is
**never even used**. The central physical claim is absent from the verified content.

### C2. The theorem models a *single* effective error, not G sequential gate errors

The LHS of `isotropicGrover_main` (`MainTheorem.lean:40-43`) integrates over **one** angle
`θ ~ composedMeasure` and **one** direction `e₂ ~ perpSphereMeasure`, i.e. the single-rotation
model `Ψ = cosθ·Φ + sinθ·e₂`. There is no representation anywhere of sequential gate
application, the oracle, the diffusion operator, or the fact (English §6) that the k-th error
rotates around the *current* state `Ψ_k`, not around `Φ`.

Worse, the English §6 gives a genuinely rigorous **induction**
(`f_{k+1} = λ·f_k + (1-λ)(1-f_k)/(d-1)`) that does *not* depend on the §3 composition
hand-wave — it needs only single-step facts the Lean *does* prove (the decoherent floor and
the per-step `E[cos²θ]=λ`). The Lean **discards this induction** and instead computes the
second moment of a single `poissonMarginal d (σ^G)`, which is the correct object *only if*
composition holds. So the Lean formalization is **strictly weaker and less faithful than the
English §6 it claims to implement**. (The numbers agree:
`∫cos²θ ∂poissonMarginal d (σ^G) = ((d-1)(σ^G)²+1)/d = ((d-1)σ^{2G}+1)/d`, matching §6's `F`
— but only because composition is assumed to make these the same object.)

### C3. "Grover" does not appear in the formal statement at all

In `isotropicGrover_main`, `G : ℕ` is **arbitrary**, `Φ : E n` is an **arbitrary** unit
vector, and `p_ideal := succProb n Φ w` is just two squared coordinates of that arbitrary `Φ`.
Nothing constrains `Φ` to be the Grover output state, or `G` to be "gate count at optimal
iterations." The verified statement is really:

> *For the isotropic-error model applied to **any** unit vector Φ, the model's expected
> success probability equals σ^{2G}·p_ideal + (1−σ^{2G})/N.*

That is a fact about the error model's algebra instantiated at an arbitrary state. All
Grover-specific content lives in prose, not in the proof.

---

## MAJOR ISSUES

### M1. The sole non-foundational axiom is the entire d≥3 second moment

Everything rests on `poissonIntegral_cos_sq_d3` (`Gegenbauer.lean:28`). It is **correct**
(verified numerically against the project's own density), and it is legitimately citable
(Poisson integral formula / harmonic extension, Axler–Bourdon–Ramey, Ch. 5). Two caveats a
referee must flag:

- It axiomatizes a **concrete integral identity over the project's own
  `poissonKernelDensity` definition**, not an abstract textbook lemma. A wrong exponent in
  `poissonKernelDensity` (`IsotropicError.lean:36`) would make it silently false, and nothing
  in the build would catch it.
- The d=2 case *was* proved (~300 lines in `GegenbaurerHelper.lean`), which is strong evidence
  the d≥3 case is provable with more Mathlib work. It was simply not done.

### M2. The fully-*proved* d=2 case is dead code w.r.t. the main theorem

`isotropicGrover_main` requires `hn : 2 ≤ n`, forcing `d n ≥ 8`. So `poissonIntegral_cos_sq`
(`Gegenbauer.lean:38`) **always** takes the `d ≥ 3` axiom branch; the d=2 branch — the one
large body of genuinely-proved analytic work in `GegenbaurerHelper.lean` plus the d=2 half of
`IsotropicError.lean` — is **never reached** by the main result. The headline theorem's
second moment therefore rests **100% on the axiom**, not on any proved instance. (Also: `n=1`
gives `d=4 ≥ 3` and would already satisfy the axiom, so the `2 ≤ n` bound looks arbitrary.)

### M3. `E[cosθ] = σ` and its whole proof are decorative

`poissonMarginal_mean_cos` (`IsotropicError.lean:318`), its full d=2 complex-Poisson proof,
and the axiom `poissonMarginal_mean_cos_d3` are **not used** by `isotropicGrover_main` (absent
from `#print axioms`). The main theorem needs only the *second* moment. English §2/§3 present
`E[cosθ]=σ` as load-bearing; in the formalization it is dead weight. Fine logically, but the
asymmetry should be stated honestly.

### M4. The `LimitingCases` theorems are disconnected from the main result

`tendsto_ideal_as_fidelity_one` / `tendsto_random_as_fidelity_zero` (`LimitingCases.lean`) are
continuity facts about the **abstract** function `mixtureProb p N f = f·p + (1-f)/N`. They
never reference `isotropicGrover_main` or its measures, and are trivially true for *any*
`p, N`. They say nothing about Grover or the error model; presenting them as "limiting cases
of the result" (§8) is generous.

---

## ENGLISH-PROOF ISSUES

### E1. §3 hand-waves the hardest step
"Because every individual error is isotropic… the accumulated rotation direction is also
isotropic," and "e₂ is uniform in V⊥ and independent of θ_G, exactly as for a single gate."
Each error rotates around the *current* `Ψ_k`, not `Φ`; that the composite is *exactly* a
single uniform rotation of `Φ` with a convolved angle is a non-trivial probabilistic claim,
asserted with a citation rather than argued. This is precisely the claim the Lean fails to
formalize (C1/C2).

### E2. The "Goal" exceeds what is derived or formalized
The stated goal (lines 5–9) includes the repetition overhead `k(n)` and the `a·b^n + c`
exponential fit. Neither is in the English derivation (which stops at `E[p_e]`) nor in Lean.
Also, "G(n) … taken directly from simulation data" means the headline `E[p_e]` is **not** a
closed form in `n` alone — it depends on an empirical input. The README's "exact… no
approximations… all finite-size corrections cancel" is true only *within the model's algebra*,
conditional on the (unproven) composition and the (axiomatized) second moment.

### E3. Minor: §5 redundancy
"It is pinned down by three constraints" — constraint 1 (Range) is then said to "also follow
from constraint 2." Harmless, but the three-constraint framing is really two. (The
corresponding Lean proof `secondMoment_eq_scalar_perp` is correct and is one of the best parts
of the repo.)

---

## WHAT IS GENUINELY GOOD (credit where due)

These are real, non-trivial, fully-proved (no axiom, no sorry):

- **`secondMoment_eq_scalar_perp`** (`SecondMoment.lean:44`) — the Schur/reflection argument
  that `E[e₂e₂ᵀ] = c·P_perp`, via Householder reflections inside `V⊥`
  (`CrossTerm.lean:594-809`). Substantial and clean.
- **`perpSphereMeasure_neg_invariant`** + the Haar→sphere isometry-invariance machinery
  (`CrossTerm.lean:160-367`). Genuinely hard measure-theory plumbing, done properly.
- **`decoherent_floor`** (`SecondMoment.lean:380`) and the cross-term vanishing
  (`CrossTerm.lean:432-515`).
- **`poissonIntegral_cos_sq_d2`** via Mathlib's complex Poisson formula
  (`GegenbaurerHelper.lean`) — a real proof, even if unreachable from the main theorem (M2).
- The final algebra (`MainTheorem.lean:54-68`) with an independent TDD algebra check
  (`:75-86`). The boxed identity is verified.

---

## Summary table

| Claim in README / English proof | Status in Lean |
|---|---|
| G errors → effective σ^G (§3) | **Assumed** (definition + vacuous `rfl` theorem) — not proved, not even used |
| Noisy state = cosθ·Φ + sinθ·e₂, e₂ uniform ⊥ Φ | **Modeling assumption** (definitions), not derived |
| `E[cosθ] = σ` (§2) | Proved d=2; axiom d≥3; **unused** by main theorem |
| Cross term vanishes (§4) | ✅ Fully proved |
| Decoherent floor (2−p)/(d−1) (§5) | ✅ Fully proved |
| Second moment F (§6) | English: rigorous induction. Lean: **axiom** (d≥3) via single-error shortcut, *not* the induction |
| Final algebra → σ^{2G}·p + (1−σ^{2G})/N (§7) | ✅ Fully proved |
| About "Grover's algorithm" specifically | ❌ Φ, G arbitrary; no Grover structure formalized |

---

## Honest one-line description of what is actually verified

> *Given the isotropic single-error model with angle distribution `poissonMarginal d (σ^G)`
> and the axiomatized d≥3 second-moment identity, the model's expected success probability for
> an arbitrary unit-vector state equals σ^{2G}·p_ideal + (1−σ^{2G})/N.*

## Recommendations to close the gap

To actually formalize the paper's claim, at minimum:

1. Replace the `rfl` stub `isotropicComposition` with a real statement and proof (or an
   honestly-labeled axiom) of the composition/convolution law.
2. Formalize the §6 induction over G gates instead of the `σ^G` definitional shortcut — it
   relies only on single-step results that are already proved (decoherent floor + per-step
   `E[cos²θ]=λ`), so this is tractable without new axioms.
3. Either prove `poissonIntegral_cos_sq_d3` (the d=2 proof shows the path) or prominently
   document it as the single load-bearing assumption of the entire result.
4. Tie `Φ`/`G` to the actual Grover circuit, or restate the README/abstract to scope the claim
   to "the isotropic error model applied to an arbitrary state."
5. Update the `sessions/` logs and README: "0 sorries / fully verified / exact" is presented
   without surfacing C1–C3. **The most serious problem is that the documentation overstates
   the verification.**

---

*Reviewer note:* No source files were modified during this review. A temporary `AxiomCheck.lean`
used to obtain the `#print axioms` trace was removed afterward.
