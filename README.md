# isotropic-grover-proof

This is an attempt to formalise a proof for studying the impact of Isotropic Errors on Grover's Algorithm using Lean 4, Mathlib and agentic AI tools. 

## Goal

The primary goal of this derivation is a closed-form expression for $\mathrm{E}[p_e]$, the **expected success probability** of a quantum state (such as the output of Grover's algorithm on $n$ qubits) when subject to $G$ gates with isotropic error of per-gate fidelity parameter $\sigma \in (0,1)$:

$$\boxed{\mathrm{E}[p_e] = \sigma^{2G} \cdot p_\mathrm{ideal} + \frac{1-\sigma^{2G}}{N},}$$

where $N = 2^n$ is the database size and $p_\mathrm{ideal}$ is the ideal success probability.

### Downstream Applications and Gate Count
- **Repetition Overhead $k(n)$:** Once $\mathrm{E}[p_e]$ is obtained, the repetition overhead required to achieve ideal success probability across independent trials,
  $$k(n) = \frac{\log(1-p_\mathrm{ideal})}{\log(1-\mathrm{E}[p_e])},$$
  can be computed and fit as an exponential in $n$ ($a \cdot b^n + c$). Both the definition of $k(n)$ and the exponential fitting are downstream application steps that build upon the mixture formula rather than being part of the core derivation or formalization.
- **Gate Count $G(n)$:** In empirical studies, $G(n)$ is typically taken directly from simulation data (transpiled gate counts at optimal Grover iterations). Analytically, one may substitute theoretical approximations such as $G(n) \sim \frac{\pi}{4}\sqrt{N}$ (or gate-decomposed counts proportional to $\frac{\pi}{4}\sqrt{2^n}$), but the derivation itself takes gate count $G$ as an external parameter.
- **Exactness:** The cancellation of intermediate dimension-dependent factors ($d, d-1$) is exact within the algebraic framework of the isotropic error model. However, this exactness is conditional on the underlying physical and mathematical assumptions (isotropic error commutation, Poisson marginal angle distribution, and uniform equatorial perturbation).

More details on the mathematical steps are available in [english-proof.md](english-proof.md).

## Formal Verification Scope & Axiom Footprint

### Verified Scope in Lean 4
The theorem proved in `IsotropicGroverProof/MainTheorem.lean` (`isotropicGrover_main`) establishes the following:
> *Given the isotropic single-error model with angle distribution `poissonMarginal d (σ^G)` and the axiomatized $d \ge 3$ second-moment identity, the model's expected success probability for an arbitrary unit-vector state equals $\sigma^{2G} \cdot p_\mathrm{ideal} + (1 - \sigma^{2G}) / N$.*

### Axiom Footprint
Running `#print axioms isotropicGrover_main` shows:
- **Standard foundational axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Analytic axiom:** `poissonIntegral_cos_sq_d3` (the second moment of the Poisson marginal on spheres for dimension $d \ge 3$, cited from Axler, Bourdon & Ramey, *Harmonic Function Theory*, Ch. 5; the $d = 2$ case is fully proved in `GegenbaurerHelper.lean` via Mathlib's complex Poisson formula).

### Open Gaps & Tracking Issues
While the Lean code compiles without `sorry`s, the formalization currently models a single-step geometric identity on an arbitrary unit vector rather than a fully verified, end-to-end quantum circuit execution. The open gaps are tracked in the following issues:
1. **Composition Law ([#6](https://github.com/lazyoracle/isotropic-grover-proof/issues/6)):** The theorem `isotropicComposition` in `Composition.lean` is currently a placeholder `rfl` tautology, and multi-gate noise is defined directly as `composedMeasure d G σ := poissonMarginal d (σ ^ G)`. The formal convolution of independent error rotations remains to be proved.
2. **Sequential Error Dynamics vs. Single Effective Error ([#7](https://github.com/lazyoracle/isotropic-grover-proof/issues/7)):** The formal theorem models a single effective rotation around an arbitrary initial state $\Phi$ rather than modeling $G$ sequential gate applications rotating around intermediate noisy states $\Psi_k$. The step-by-step induction from `english-proof.md` §6 is not yet formalized in Lean.
3. **Arbitrary State vs. Formalized Grover Circuit ([#8](https://github.com/lazyoracle/isotropic-grover-proof/issues/8)):** `isotropicGrover_main` proves a geometric property of an arbitrary unit vector $\Phi \in \mathbb{R}^{2N}$ and arbitrary integer $G > 0$. The Grover algorithm itself (uniform superposition preparation, oracle, and diffusion operators) is not yet formalized.
4. **Analytic Second-Moment Identity for $d \ge 3$ ([#9](https://github.com/lazyoracle/isotropic-grover-proof/issues/9)):** The Poisson second-moment integral identity for $d \ge 3$ is axiomatized (`poissonIntegral_cos_sq_d3`) rather than proved from first principles in Lean.

## Repository structure

- The english language proof is in `english-proof.md`
- AI session logs are in `sessions/`
- The main Lean submodules are under `IsotropicGroverProof` 
```
  Basic.lean             — barrel re-export, imports all modules below in dependency order
  Defs.lean              — M1: Core types, stdBasisVec, succProb, Parseval identity
  IsotropicError.lean    — M2: Poisson kernel marginal, isotropicError state
  Composition.lean       — M3: Composition axiom, composedMeasure
  CrossTerm.lean         — M4: perpSphereMeasure, cross-term cancellation
  SecondMoment.lean      — M5: P_perp, second moment = (1/(d-1))·P_perp, decoherent floor
  GegenbaurerHelper.lean — d=2 helper for M6: poissonIntegral_cos_sq_d2, via Mathlib's complex Poisson formula
  Gegenbauer.lean        — M6: f₂ = E[cos²θ_G] via the Poisson integral formula / harmonic extension (matches english-proof.md §6); d=2 proved, d≥3 via axiom from Axler, Bourdon & Ramey
  MainTheorem.lean       — M7: isotropicGrover_main (the final theorem)
  LimitingCases.lean     — M8: Limiting corollaries (σ→1 and σ→0)
```
