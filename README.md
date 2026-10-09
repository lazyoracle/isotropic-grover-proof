# isotropic-grover-proof

This repository formalises the mathematical proof studying the impact of isotropic errors on Grover's Algorithm using Lean 4, Mathlib, and agentic AI tools.

## Goal

The primary goal of this derivation is a closed-form expression for $\mathrm{E}[p_e]$, the **expected success probability** of a quantum state (such as the output of Grover's algorithm on $n$ qubits) when subject to $G$ gates with isotropic error of per-gate fidelity parameter $\sigma \in (0,1)$:

$$\boxed{\mathrm{E}[p_e] = \sigma^{2G} \cdot p_\mathrm{ideal} + \frac{1-\sigma^{2G}}{N},}$$

where $N = 2^n$ is the database size and $p_\mathrm{ideal}$ is the ideal success probability.

### Downstream Applications and Gate Count
- **Repetition Overhead $k(n)$:** Once $\mathrm{E}[p_e]$ is obtained, the repetition overhead required to achieve ideal success probability across independent trials,
  $$k(n) = \frac{\log(1-p_\mathrm{ideal})}{\log(1-\mathrm{E}[p_e])},$$
  can be computed and fit as an exponential in $n$ ($a \cdot b^n + c$). Both the definition of $k(n)$ and the exponential fitting are downstream application steps that build upon the mixture formula rather than being part of the core derivation or formalization.
- **Gate Count $G(n)$:** In empirical studies, $G(n)$ is typically taken directly from simulation data (transpiled gate counts at optimal Grover iterations). Analytically, one may substitute theoretical approximations such as $G(n) \sim \frac{\pi}{4}\sqrt{N}$ (or gate-decomposed counts proportional to $\frac{\pi}{4}\sqrt{2^n}$), but the derivation itself takes gate count $G$ as an external parameter.
- **Exactness:** The cancellation of intermediate dimension-dependent factors ($d, d-1$) is exact within the algebraic framework of the isotropic error model. However, this exactness is conditional on the underlying physical and mathematical assumptions (isotropic error commutation or sequential Markov evolution, Poisson marginal angle distribution, and uniform equatorial perturbation).

More details on the mathematical steps are available in [english-proof.md](english-proof.md).

---

## Formal Verification Scope & Proved Theorems

The codebase machine-checks the mathematical derivation in Lean 4 across several key modules:

### 1. Main Geometric Invariant Theorem (`MainTheorem.lean`)
- **`isotropicGrover_main`**: Holds for all $n \in \mathbb{N}$ (arbitrary number of qubits, with ambient real dimension $d = 2 \cdot 2^n$). For an arbitrary unit-vector state $\Phi \in \mathcal{S}^{d-1}$ and gate count $G > 0$, the nested integral of the noisy success probability over the perturbation angle and equatorial noise direction evaluates to:
  $$\int_0^\pi \int_{\mathcal{S}^{d-2}(V_\perp)} \mathrm{succProb}\, n \, (\mathrm{isotropicError}\, \Phi\, e_2\, \theta)\, w \, \partial(\mathrm{perpSphereMeasure}\, \Phi) \, \partial(\mathrm{composedMeasure}\, d\, G\, \sigma) = \sigma^{2G} \cdot \mathrm{succProb}\, n \, \Phi \, w + \frac{1 - \sigma^{2G}}{2^n}.$$
- **`isotropicGrover_n0`**: For $n = 0$ ($d = 2$), the theorem is proved with **zero non-foundational axioms** (`[propext, Classical.choice, Quot.sound]`), using the fully machine-checked complex Poisson integral formula on the unit circle in `GegenbaurerHelper.lean`.

### 2. Sequential Markov Chain Error Induction (`Sequential.lean`)
To model microscopic quantum circuit error accumulation where each gate error rotates around the *perturbed* current state $\Psi_k$ rather than the initial state $\Phi$, `Sequential.lean` formalizes the Markov chain induction from §6 of `english-proof.md`:
- **State fidelity recurrence:**
  $$f_0 = 1, \qquad f_{k+1} = \lambda f_k + (1-\lambda)\frac{1-f_k}{d-1}, \quad \text{where } \lambda = \frac{(d-1)\sigma^2+1}{d}.$$
- **Contraction & closed form:** Proves geometric contraction $T(f) - 1/d = \sigma^2(f - 1/d)$ toward the decoherent floor $1/d$, and proves the exact closed form by induction on $k$ with zero non-foundational axioms:
  $$f_k = \frac{(d-1)\sigma^{2k}+1}{d}.$$
- **`sequential_mixture_formula`**: Proves that sequential gate error accumulation yields the exact same mixture formula:
  $$f_G \cdot p + (1 - f_G) \cdot \frac{2 - p}{d - 1} = \sigma^{2G} \cdot p + \frac{1 - \sigma^{2G}}{2^n}.$$

### 3. Grover Circuit Components & Search Plane (`GroverCircuit.lean`)
Connects the general unit-vector theorem to Grover's algorithm:
- Formalizes the uniform superposition state vector $|s\rangle \in E\, n$, target basis state $|w\rangle$, and orthogonal non-target state $|w^\perp\rangle$.
- Formalizes the 2D Grover search plane $\Phi(\alpha) = \cos\alpha |s_\perp\rangle + \sin\alpha |w\rangle$.
- **`isotropicGrover_groverState2D`**: Proves that states in the Grover plane yield expected success probability $\sigma^{2G} \sin^2\alpha + (1 - \sigma^{2G})/2^n$.
- **`isotropicGrover_uniformSuperposition`**: Proves that before Grover iterations, the uniform superposition state has expected success probability identically equal to $1/2^n$ under isotropic noise for any gate count $G$ and fidelity $\sigma$.

### 4. Limiting Cases & Asymptotics (`LimitingCases.lean`)
- Connects `mixtureProb` directly to the LHS and RHS of `isotropicGrover_main`.
- Proves continuity of the expected success probability in $\sigma$, and verifies the limiting behavior:
  - $\sigma \to 1$ converges to $p_\mathrm{ideal}$ (`tendsto_expectedSuccProb_as_sigma_one`).
  - $\sigma \to 0$ converges to random guessing $1/2^n$ (`tendsto_expectedSuccProb_as_sigma_zero`).

---

## Axiom Footprint

Running `#print axioms isotropicGrover_main` confirms that the proof rests exclusively on standard Lean foundational axioms plus a single analytic axiom:
- **Standard foundational axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Analytic axiom:** `poissonIntegral_cos_sq_d3` (the second moment of the Poisson marginal on spheres for dimension $d \ge 3$):
  $$\int_0^\pi \cos^2\theta \, \partial(\mathrm{poissonMarginal}\, d\, \sigma) = \frac{(d - 1)\sigma^2 + 1}{d}.$$

*(Note: For $n = 0$, `isotropicGrover_n0`, `sequentialFidelity_eq`, and `sequential_mixture_formula` use 0 non-foundational axioms.)*

### Mathematical Derivation (Harmonic Extension)
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

### Mathlib Scope Boundary & Lean Verification
- **Dimension $d = 2$ (100% verified):** For $d = 2$, the unit sphere $S^1 \cong \mathbb{T} \subset \mathbb{C}$ allows harmonic functions to be treated as real parts of holomorphic functions. Mathlib provides `circleAverage_poissonKernel_of_diffContOnCl` (`Mathlib.Analysis.Complex.Poisson`), allowing the $d = 2$ theorem `poissonIntegral_cos_sq_d2` to be fully proved without any non-foundational axioms in `GegenbaurerHelper.lean`.
- **Dimensions $d \ge 3$ (Mathlib boundary):** Mathlib currently lacks spherical harmonics ($L^2(S^{d-1}) = \bigoplus_k \mathcal{H}_k$), the Laplace-Beltrami operator, and the Poisson representation formula for Euclidean balls in $\mathbb{R}^d$ ($d \ge 3$). Axiomatizing `poissonIntegral_cos_sq_d3` precisely marks this analytic boundary.
- **Formally verified algebraic properties:** In `IsotropicGroverProof/Gegenbauer.lean`, Lean-verified lemmas validate the algebraic backbone of this derivation:
  - `laplacian_trace_cancellation`: validates $2 - 2d/d = 0$ for $d \neq 0$.
  - `harmonicExtension_boundary`: validates $(\xi\cdot\Phi)^2 - 1/d + 1/d = (\xi\cdot\Phi)^2$.
  - `harmonicExtension_eval`: validates $\sigma^2 - \sigma^2/d + 1/d = ((d - 1)\sigma^2 + 1)/d$.
  - `poissonIntegral_val_sigma_one` and `poissonIntegral_val_sigma_zero`: validate the noiseless limit $\sigma = 1 \implies 1$ and complete decoherence floor $\sigma = 0 \implies 1/d$.
  - TDD numeric sanity checks for $d = 3, 4, 8, 16, 32, 64$.

---

## Repository Structure

- `english-proof.md`: Complete mathematical derivation in English prose.
- `notes/`: Design specifications, architectural decisions, and task implementation plans.
- `sessions/`: AI conversation logs and adversarial proof review notes.
- `IsotropicGroverProof/`: Lean 4 formalization modules:
  ```
  Basic.lean             — Barrel re-export importing all submodules in dependency order
  Defs.lean              — M1: Ambient space ℝ^d, basis vectors, succProb, Parseval sum identity
  IsotropicError.lean    — M2: Poisson kernel marginal density and isotropic error perturbed state
  Composition.lean       — M3: Composed measure definition and sequential induction references
  CrossTerm.lean         — M4: Equatorial sphere measure, odd symmetry, cross-term vanishing
  SecondMoment.lean      — M5: Subspace projection P_perp, second moment E[e₂e₂ᵀ] = P_perp/(d-1), decoherent floor
  GegenbaurerHelper.lean — Analytic proof of d=2 Poisson integral formula via Mathlib complex analysis
  Gegenbauer.lean        — M6: Poisson integral second moment f₂, harmonic polynomial algebraic verification
  MainTheorem.lean       — M7: isotropicGrover_main (for all n) and isotropicGrover_n0 (0 axioms)
  LimitingCases.lean     — M8: Mixture prob connection and continuous parameter limits (σ→1, σ→0)
  Sequential.lean        — Gate-level Markov error induction and sequential mixture theorem (0 axioms)
  GroverCircuit.lean     — Grover state vectors, 2D search plane, and Grover specialization
  ```

---

## Building and Checking

To compile the formalization and verify all proofs:

```bash
lake build
```
