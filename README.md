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
Running `#print axioms isotropicGrover_main` confirms that the proof rests exclusively on standard Lean foundational axioms plus a single analytic axiom:
- **Standard foundational axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Analytic axiom:** `poissonIntegral_cos_sq_d3` (the second moment of the Poisson marginal on spheres for dimension $d \ge 3$):
  $$\int_0^\pi \cos^2\theta \, \partial(\mathrm{poissonMarginal}\, d\, \sigma) = \frac{(d - 1)\sigma^2 + 1}{d}.$$

#### Mathematical Derivation (Harmonic Extension)
This identity is derived via harmonic polynomial extension on the Euclidean unit ball $B^d \subset \mathbb{R}^d$ (Axler, Bourdon & Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137, 2001, Ch. 5, Theorems 5.5 & 5.14):
1. **Boundary data:** For a fixed unit vector $\Phi \in \mathbb{R}^d$ ($|\Phi| = 1$), the boundary data on the unit sphere $S^{d-1}$ is $h(\xi) = (\xi \cdot \Phi)^2 = \cos^2\theta$.
2. **Harmonic extension:** In the interior ball $B^d$, consider $H(\mathbf{x}) = (\mathbf{x} \cdot \Phi)^2 - |\mathbf{x}|^2/d + 1/d$.
   - The Laplacian satisfies $\Delta H = \Delta((\mathbf{x}\cdot\Phi)^2) - \Delta(|\mathbf{x}|^2/d) + \Delta(1/d) = 2|\Phi|^2 - 2d/d + 0 = 0$, so $H$ is harmonic on $B^d$.
   - On the boundary $S^{d-1}$ where $|\xi| = 1$, $H(\xi) = (\xi\cdot\Phi)^2 - 1/d + 1/d = (\xi\cdot\Phi)^2 = h(\xi)$.
3. **Poisson representation formula:** Any harmonic function continuous on $\overline{B}^d$ satisfies:
   $$H(\mathbf{x}) = \int_{S^{d-1}} P(\mathbf{x}, \xi) h(\xi) \, d\sigma_{S^{d-1}}(\xi)$$
   where $P(\mathbf{x}, \xi) = \frac{1 - |\mathbf{x}|^2}{|\mathbf{x} - \xi|^d}$ is the Poisson kernel for the Euclidean ball.
4. **Interior radial evaluation:** At $\mathbf{x} = \sigma \Phi$ with per-gate fidelity $\sigma \in (0, 1)$:
   $$H(\sigma \Phi) = (\sigma\Phi\cdot\Phi)^2 - \frac{|\sigma\Phi|^2}{d} + \frac{1}{d} = \sigma^2 - \frac{\sigma^2}{d} + \frac{1}{d} = \frac{(d - 1)\sigma^2 + 1}{d}.$$
5. **Marginalization:** By rotational symmetry around the axis $\Phi$, the sphere integral against the Poisson kernel centered at $\sigma\Phi$ reduces to the 1D marginal measure `poissonMarginal d σ`:
   $$\int_0^\pi \cos^2\theta \, \partial(\mathrm{poissonMarginal}\, d\, \sigma) = H(\sigma\Phi) = \frac{(d - 1)\sigma^2 + 1}{d}.$$

#### Mathlib Scope Boundary & Lean Verification
- **Dimension $d = 2$ (100% verified):** For $d = 2$, the unit sphere $S^1 \cong \mathbb{T} \subset \mathbb{C}$ allows harmonic functions to be treated as real parts of holomorphic functions. Mathlib provides `circleAverage_poissonKernel_of_diffContOnCl` (`Mathlib.Analysis.Complex.Poisson`), allowing the $d = 2$ theorem `poissonIntegral_cos_sq_d2` to be fully proved without any non-foundational axioms in `GegenbaurerHelper.lean`.
- **Dimensions $d \ge 3$ (Mathlib boundary):** Mathlib currently lacks spherical harmonics ($L^2(S^{d-1}) = \bigoplus_k \mathcal{H}_k$), the Laplace-Beltrami operator, and the Poisson representation formula for Euclidean balls in $\mathbb{R}^d$ ($d \ge 3$). Axiomatizing `poissonIntegral_cos_sq_d3` precisely marks this analytic boundary.
- **Formally verified algebraic properties:** In `IsotropicGroverProof/Gegenbauer.lean`, Lean-verified lemmas validate the algebraic backbone of this derivation:
  - `laplacian_trace_cancellation`: validates $2 - 2d/d = 0$ for $d \neq 0$.
  - `harmonicExtension_boundary`: validates $(\xi\cdot\Phi)^2 - 1/d + 1/d = (\xi\cdot\Phi)^2$.
  - `harmonicExtension_eval`: validates $\sigma^2 - \sigma^2/d + 1/d = ((d - 1)\sigma^2 + 1)/d$.
  - `poissonIntegral_val_sigma_one` and `poissonIntegral_val_sigma_zero`: validate the noiseless limit $\sigma = 1 \implies 1$ and complete decoherence floor $\sigma = 0 \implies 1/d$.
  - TDD numeric sanity checks for $d = 3, 4, 8, 16, 32, 64$.

### Open Gaps & Tracking Issues
While the Lean code compiles without `sorry`s, the formalization currently models a single-step geometric identity on an arbitrary unit vector rather than a fully verified, end-to-end quantum circuit execution. The open gaps are tracked in the following issues:
1. **Composition Law ([#6](https://github.com/lazyoracle/isotropic-grover-proof/issues/6)):** The theorem `isotropicComposition` in `Composition.lean` is currently a placeholder `rfl` tautology, and multi-gate noise is defined directly as `composedMeasure d G σ := poissonMarginal d (σ ^ G)`. The formal convolution of independent error rotations remains to be proved.
2. **Sequential Error Dynamics vs. Single Effective Error ([#7](https://github.com/lazyoracle/isotropic-grover-proof/issues/7)):** The formal theorem models a single effective rotation around an arbitrary initial state $\Phi$ rather than modeling $G$ sequential gate applications rotating around intermediate noisy states $\Psi_k$. The step-by-step induction from `english-proof.md` §6 is not yet formalized in Lean.
3. **Arbitrary State vs. Formalized Grover Circuit ([#8](https://github.com/lazyoracle/isotropic-grover-proof/issues/8)):** `isotropicGrover_main` proves a geometric property of an arbitrary unit vector $\Phi \in \mathbb{R}^{2N}$ and arbitrary integer $G > 0$. The Grover algorithm itself (uniform superposition preparation, oracle, and diffusion operators) is not yet formalized.
4. **Analytic Second-Moment Identity for $d \ge 3$ ([#9](https://github.com/lazyoracle/isotropic-grover-proof/issues/9)):** The Poisson second-moment integral identity for $d \ge 3$ is axiomatized (`poissonIntegral_cos_sq_d3`) due to the absence of high-dimensional Euclidean ball Poisson representation theory in Mathlib. Its harmonic polynomial extension derivation ($H(\mathbf{x}) = (\mathbf{x}\cdot\Phi)^2 - |\mathbf{x}|^2/d + 1/d$) and algebraic decomposition are formally documented and verified in `Gegenbauer.lean`.

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
  Sequential.lean        — Step-by-step Markov error induction matching §6
  GroverCircuit.lean     — Grover circuit states and specialization of the main geometric theorem
```
