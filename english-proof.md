### Derivation of the $\sigma^{2G(n)}$ model

#### Goal

The mathematical derivation in this document establishes a closed-form expression for $\mathrm{E}[p_e]$, the **expected success probability** of a quantum state (such as the output state of Grover's algorithm on $n$ qubits) when every gate is subject to an isotropic error with per-gate fidelity parameter $\sigma \in (0,1)$ across $G$ gate operations:

$$\boxed{\mathrm{E}[p_e] = \sigma^{2G} \cdot p_\mathrm{ideal} + \frac{1-\sigma^{2G}}{N},}$$

where $N = 2^n$ is the database size and $p_\mathrm{ideal}$ is the ideal success probability.

**Downstream Application (Repetition Overhead):**
Once the expected success probability $\mathrm{E}[p_e]$ is derived, the repetition overhead required for $k$ independent runs to collectively succeed with probability $p_\mathrm{ideal}$,
$$k(n) = \frac{\log(1-p_\mathrm{ideal})}{\log(1-\mathrm{E}[p_e])},$$
can be calculated and fit as an exponential in $n$ of the form $a\cdot b^n + c$ (derived from $(1-\mathrm{E}[p_e])^k = 1-p_\mathrm{ideal}$, solved for $k$). Note that computing $k(n)$ and fitting an exponential are downstream application steps that build on the mixture model rather than parts of the core derivation.

**Role of Gate Count $G(n)$:**
The gate count $G$ is treated as an externally specified parameter. In empirical/simulation studies, $G = G(n)$ is typically taken directly from transpiled circuit simulation data at optimal Grover iterations. In theoretical analyses, one can substitute asymptotic approximations such as $G(n) \sim \frac{\pi}{4}\sqrt{N}$ (or gate-decomposed counts proportional to $\frac{\pi}{4}\sqrt{2^n}$). The derivation does not produce a closed-form expression for $G(n)$ in terms of $n$ alone.

**Exactness and Assumptions:**
The formula is **exact** within the algebraic framework of the isotropic error model: all intermediate dimension-dependent factors cancel, as shown below. However, this exactness is conditional on the underlying model assumptions: unitary error commutation, the Poisson marginal angle distribution, and independent uniform equatorial perturbations. (See also tracking issues [#6](https://github.com/lazyoracle/isotropic-grover-proof/issues/6), [#7](https://github.com/lazyoracle/isotropic-grover-proof/issues/7), [#8](https://github.com/lazyoracle/isotropic-grover-proof/issues/8), and [#9](https://github.com/lazyoracle/isotropic-grover-proof/issues/9) for formalization status).

The derivation proceeds in six steps:

1. Represent the quantum state as a real vector on a hypersphere.
2. Define the isotropic error model and the distribution of the perturbation angle.
3. Collapse all $G(n)$ per-gate errors to a single effective error.
4. Expand $\mathrm{E}[p_e]$ and show the cross term vanishes.
5. Compute the "decoherent floor" $\mathrm{E}[(\mathbf{e}_2\cdot\hat{u}_{2w})^2+(\mathbf{e}_2\cdot\hat{u}_{2w+1})^2]$.
6. Compute the second moment $F = \mathrm{E}[\cos^2\!\theta_G]$ via harmonic extension and induction.

---

#### §1 — The real representation of quantum states

An $n$-qubit state has $N = 2^n$ complex amplitudes:

$$|\psi\rangle = \sum_{x=0}^{N-1} a_x |x\rangle, \qquad a_x \in \mathbb{C}, \qquad \sum_{x=0}^{N-1} |a_x|^2 = 1.$$

Write each amplitude in terms of its real and imaginary parts:

$$a_x = \alpha_{2x} + i\,\alpha_{2x+1}, \qquad \alpha_{2x},\,\alpha_{2x+1} \in \mathbb{R}.$$

Stacking all $2N$ real numbers gives a real vector of length $d = 2N = 2^{n+1}$:

$$\mathbf{v} = (\alpha_0,\,\alpha_1,\,\alpha_2,\,\alpha_3,\,\ldots,\,\alpha_{2N-2},\,\alpha_{2N-1}) \in \mathbb{R}^d.$$

The normalization condition $\sum_{x}|a_x|^2 = 1$ becomes $|\mathbf{v}|^2 = 1$, so $\mathbf{v}$ lives on the unit hypersphere:

$$\mathbf{v} \in S^{d-1} \subset \mathbb{R}^d, \qquad d = 2N = 2^{n+1}.$$

**Success probability in the real representation.** The probability of measuring outcome $|w\rangle$ is $p = |\langle w|\psi\rangle|^2 = |a_w|^2 = \alpha_{2w}^2 + \alpha_{2w+1}^2$. In terms of the real vector, this is a sum of squares of exactly two components: the component along $\hat{u}_{2w} = \mathbf{e}_{2w}$ (real part of amplitude $w$) and the component along $\hat{u}_{2w+1} = \mathbf{e}_{2w+1}$ (imaginary part):

$$p = (\mathbf{v}\cdot\hat{u}_{2w})^2 + (\mathbf{v}\cdot\hat{u}_{2w+1})^2.$$

For the ideal Grover final state $\Phi \in S^{d-1}$, the ideal success probability is therefore

$$p_\mathrm{ideal} = \Phi_{2w}^2 + \Phi_{2w+1}^2 = (\Phi\cdot\hat{u}_{2w})^2 + (\Phi\cdot\hat{u}_{2w+1})^2.$$

---

#### §2 — The isotropic error model

**Definition.** A single isotropic error with parameter $\sigma \in (0,1)$ acts on a state $\Phi \in S^{d-1}$ by producing an output state $\Psi$ distributed according to the Poisson kernel $P(\sigma\Phi,\cdot)$ on $S^{d-1}$ [[Lacalle & Pozo Coronado (2019)](#references)]. Equivalently, $\Psi$ can be written as

$$\Psi = \cos\theta\;\Phi + \sin\theta\;\mathbf{e}_2.$$

The two random quantities on the right are:

- $\theta \in [0,\pi]$: a random angle whose density is proportional to $g(\theta;\sigma)$ as derived below.
- $\mathbf{e}_2$: a random unit vector drawn **uniformly** from $V_\perp = \{\mathbf{v}\in\mathbb{R}^d : \mathbf{v}\cdot\Phi = 0\}$, the $(d-1)$-dimensional subspace orthogonal to $\Phi$.
- $\theta$ and $\mathbf{e}_2$ are **drawn independently** of each other.

Geometrically, $\Psi$ is $\Phi$ rotated by angle $\theta$ in a uniformly random direction in the equatorial hypersphere. Because $\mathbf{e}_2$ is isotropically distributed in $V_\perp$, no direction is preferred — the error has no axis, hence "isotropic."

**The angle distribution $g(\theta;\sigma)$.** The density is derived as the *marginal* of the **Poisson kernel** of the unit ball, as follows.

The Poisson kernel of the unit ball $B^d = \{\mathbf{y}\in\mathbb{R}^d : |\mathbf{y}|<1\}$ is the function

$$P(\mathbf{y},\xi) = \frac{1-|\mathbf{y}|^2}{|\mathbf{y}-\xi|^d}, \qquad \mathbf{y}\in B^d,\;\xi\in S^{d-1}.$$

It has a probabilistic interpretation: if a Brownian particle starts at interior point $\mathbf{y}$ and runs until it first hits the boundary $S^{d-1}$, then $P(\mathbf{y},\xi)/\int P$ is the probability density of the hitting point $\xi$. Now place the interior point along the first axis at distance $\sigma$ from the origin: $\mathbf{y} = \sigma\mathbf{e}_1$. By rotational symmetry, the distance from $\mathbf{y}$ to any boundary point $\xi$ depends only on the angle $\theta$ between $\mathbf{e}_1$ and $\xi$:

$$|\sigma\mathbf{e}_1 - \xi|^2 = \sigma^2 - 2\sigma(\mathbf{e}_1\cdot\xi) + 1 = 1+\sigma^2-2\sigma\cos\theta,$$

so $P(\sigma\mathbf{e}_1,\xi) = (1-\sigma^2)/(1+\sigma^2-2\sigma\cos\theta)^{d/2}$.

The Poisson kernel is now a distribution over all of $S^{d-1}$, but it only depends on $\xi$ through the single angle $\theta$. To obtain a 1D density over $\theta$ alone — the "marginal" — we integrate over all boundary points at each fixed $\theta$. For a given $\theta$, those points form a $(d-2)$-sphere (a "latitude circle" on $S^{d-1}$), whose surface area element is proportional to $\sin^{d-2}\theta\,d\theta$. Multiplying and normalizing gives the angle density used throughout this proof:

$$g(\theta;\sigma) \propto \frac{(1-\sigma^2)\sin^{d-2}\!\theta}{(1+\sigma^2-2\sigma\cos\theta)^{d/2}}.$$

Because $\Psi$ is distributed according to $P(\sigma\Phi,\cdot)$ on $S^{d-1}$, the Poisson integral formula applies directly to any expectation $\mathrm{E}[h(\Psi)]$.

**Why $\mathrm{E}[\cos\theta] = \sigma$.** Throughout this derivation, the expectation $\mathrm{E}[\cdot]$ is over the randomness of the error model (the angles $\theta$ and directions $\mathbf{e}_2$), not over measurement outcomes. The Poisson kernel has the following key property (the Poisson integral formula [[Axler, Bourdon & Ramey (2001)](#references), Ch. 5]): for any continuous $h$ on $S^{d-1}$,

$$\mathrm{E}[h(\Psi)] = \tilde{h}(\sigma\Phi),$$

where $\tilde{h}: B^d\to\mathbb{R}$ is the unique harmonic function on the open unit ball $B^d$ that extends $h$ continuously to the boundary $S^{d-1}$.

Take $h(\xi) = \xi\cdot\Phi$. The function $\tilde{h}(\mathbf{x}) = \mathbf{x}\cdot\Phi$ is already harmonic ($\Delta(\mathbf{x}\cdot\Phi) = 0$ since it is linear) and equals $h$ on $S^{d-1}$. Therefore:

$$\mathrm{E}[\cos\theta] = \tilde{h}(\sigma\Phi) = \sigma\Phi\cdot\Phi = \sigma.$$

The parameter $\sigma$ therefore measures the average amplitude overlap between the perturbed state $\Psi$ and the ideal state $\Phi$. When $\sigma=1$ there is no rotation (a perfect gate), and when $\sigma=0$ the final state is uniformly random.

---

#### §3 — $G(n)$ gate errors: effective ansatz vs. sequential Markov chain

**Commutativity with gates.** In quantum circuits, isotropic noise channels commute with unitary gates in distribution [[Lacalle & Pozo Coronado (2019)](#references)]:

$$U \circ E \stackrel{d}{=} E' \circ U,$$

where $E'$ has the same isotropic distribution as $E$. Because an isotropic error has no preferred axis, it perturbs the state across all equatorial directions with equal probability. In the physical literature, this property motivates commuting all per-gate errors past subsequent gates to the end of the circuit, just before measurement.

**Two distinct modeling perspectives.** When analyzing the accumulation of $G(n)$ gate errors across the circuit, two distinct mathematical perspectives must be distinguished:

1. **Perspective A: The single-step effective error representation (ansatz).**  
   One models the net cumulative error as a single effective isotropic perturbation acting directly on the ideal output state $\Phi$:
   $$\Psi = \cos\theta_G\;\Phi + \sin\theta_G\;\mathbf{e}_2,$$
   where $\mathbf{e}_2$ is uniformly distributed on the unit sphere of the orthogonal complement $V_\perp(\Phi) = \{\mathbf{v} \in \mathbb{R}^d : \mathbf{v}\cdot\Phi = 0\}$, and the effective noise angle $\theta_G$ is independent of $\mathbf{e}_2$ with parameter $\sigma_\mathrm{eff} = \sigma^{G(n)}$.
   
   *Strengths and limitations:* This ansatz provides an intuitive, analytically compact representation that mirrors the single-gate structural form (§2) and directly matches the definition `composedMeasure d G σ := poissonMarginal d (σ^G)` currently formalized in Lean. However, as a microscopic derivation, asserting that $G$ sequential rotations across dynamically perturbed intermediate states collapse identically into a single uniform rotation around $\Phi$ with independent angle $\theta_G$ relies on a spherical convolution property on $SO(d)$ / $S^{d-1}$ that previous literature asserted by citation rather than derived.

2. **Perspective B: Sequential gate-level Markov chain evolution.**  
   In physical quantum circuits, errors act sequentially. The $(k+1)$-th gate error perturbs the *already perturbed* state $\Psi_k$, rotating around $\Psi_k$ rather than the initial state $\Phi$:
   $$\Psi_0 = \Phi, \qquad \Psi_{k+1} = \cos\theta_{k+1}\,\Psi_k + \sin\theta_{k+1}\,\mathbf{e}_{2,k+1} \quad (k = 0, 1, \dots, G-1),$$
   where at each step $\theta_{k+1}$ is drawn from the per-gate distribution with parameter $\sigma$, and $\mathbf{e}_{2,k+1}$ is uniformly distributed on the equatorial unit sphere $V_\perp^{(\Psi_k)} = \{\mathbf{v} \in \mathbb{R}^d : \mathbf{v}\cdot\Psi_k = 0\}$, independent of $\theta_{k+1}$.
   
   In this sequential reality, the noise vector at step $k+1$ is orthogonal to $\Psi_k$, not to $\Phi$. As errors accumulate, the state $\Psi_k$ undergoes a Markov random walk on $S^{d-1}$, and the successive equatorial rotation planes tilt relative to $\Phi$.

**Why $\mathrm{E}[p_e]$ does not depend on global commutativity or spherical convolution.**  
Crucially, the headline formula for the expected success probability,
$$\mathrm{E}[p_e] = \sigma^{2G}\,p_\mathrm{ideal} + \frac{1-\sigma^{2G}}{N},$$
does **not** depend on whether the single-effective-error representation (Perspective A) holds as an exact distributional identity, nor does it require global spherical convolution or commutativity.

As derived in §4, the expected success probability depends solely on the second moment of the noisy state projection along the target state, namely $F = \mathrm{E}[(\Psi_G\cdot\Phi)^2]$. Under the sequential Markov dynamics of Perspective B, this second moment is computed rigorously in §6 via the exact one-step recurrence:
$$f_k = \mathrm{E}[(\Psi_k\cdot\Phi)^2], \qquad f_{k+1} = \lambda\,f_k + (1-\lambda)\,\frac{1-f_k}{d-1},$$
where $\lambda = \mathrm{E}[\cos^2\theta_{k+1}\mid\Psi_k] = \frac{(d-1)\sigma^2+1}{d}$.

This recurrence relies **only on single-step local properties** at each step $k$:
1. *Subspace symmetry around the current state $\Psi_k$*: $\mathrm{E}[\mathbf{e}_{2,k+1}\mid\Psi_k] = \mathbf{0}$ (causing cross terms to vanish) and $\mathrm{E}[(\mathbf{e}_{2,k+1}\cdot\Phi)^2\mid\Psi_k] = \frac{1 - (\Psi_k\cdot\Phi)^2}{d-1}$ (by equatorial uniformity in $V_\perp^{(\Psi_k)}$, derived in §5).
2. *Per-gate Poisson second moment*: $\mathrm{E}[\cos^2\theta_{k+1}\mid\Psi_k] = \lambda$, which is constant and strictly independent of $\Psi_k$.

Solving this recurrence with initial condition $f_0 = (\Phi\cdot\Phi)^2 = 1$ gives the exact closed form:
$$F = f_G = \frac{(d-1)\sigma^{2G}+1}{d},$$
proving the headline result without any global spherical convolution assumption. Similarly, the first moment $\mathrm{E}[\Psi_G\cdot\Phi] = \sigma^G$ follows by induction from the per-step expectation $\mathrm{E}[\Psi_{k+1}\cdot\Phi\mid\Psi_k] = \sigma\,(\Psi_k\cdot\Phi)$ via harmonic extension of the coordinate function (§2).

*(Note on formalization)*: The distinction between Perspectives A and B mirrors the gap between current Lean formalization and the full physical circuit model:
- Lean currently models Perspective A via `composedMeasure d G σ := poissonMarginal d (σ^G)` with a placeholder `isotropicComposition` theorem (`:= rfl`). Rigorously formalizing or axiomatizing this spherical convolution identity is tracked in [#6](https://github.com/lazyoracle/isotropic-grover-proof/issues/6).
- Rigorously formalizing Perspective B by defining the sequential state process $(\Psi_k)_{k=0}^G$ and proving the §6 induction directly in Lean is tracked in [#7](https://github.com/lazyoracle/isotropic-grover-proof/issues/7). Because the §6 induction relies only on single-step properties already formalized in Lean (subspace symmetry and per-step second moment), Perspective B offers a direct, mathematically verified path to circuit-level error accumulation without needing global spherical convolution.

---

#### §4 — Expanding $\mathrm{E}[p_e]$: the cross term

The noisy success probability is, from §1,

$$p_e = (\Psi\cdot\hat{u}_{2w})^2 + (\Psi\cdot\hat{u}_{2w+1})^2.$$

Both components have the same form, so we expand $(\Psi\cdot\hat{u})^2$ for a generic unit vector $\hat{u}$ and sum at the end. Substituting $\Psi = \cos\theta_G\,\Phi + \sin\theta_G\,\mathbf{e}_2$:

$$\Psi\cdot\hat{u} = \cos\theta_G\,(\Phi\cdot\hat{u}) + \sin\theta_G\,(\mathbf{e}_2\cdot\hat{u}).$$

Squaring (every term is real):

$$(\Psi\cdot\hat{u})^2 = \underbrace{\cos^2\!\theta_G\,(\Phi\cdot\hat{u})^2}_{\text{ideal term}} + \underbrace{\sin^2\!\theta_G\,(\mathbf{e}_2\cdot\hat{u})^2}_{\text{noise term}} + \underbrace{2\cos\theta_G\sin\theta_G\,(\Phi\cdot\hat{u})(\mathbf{e}_2\cdot\hat{u})}_{\text{cross term}}.$$

**Taking the expectation.**

*Cross term vanishes.* Condition on $\theta_G$ (a fixed realization of the accumulated rotation angle). Then $\mathbf{e}_2$ is the only random quantity, and $\mathrm{E}[\mathbf{e}_2\cdot\hat{u}] = \hat{u}\cdot\mathrm{E}[\mathbf{e}_2]$. Now $\mathrm{E}[\mathbf{e}_2] = \mathbf{0}$ because the uniform distribution on $V_\perp$ is symmetric under the antipodal map $\mathbf{e}_2\mapsto -\mathbf{e}_2$ (every point and its antipode are equally likely, so the distribution is preserved), which forces

$$\mathrm{E}[\mathbf{e}_2] = \mathrm{E}[-\mathbf{e}_2] = -\mathrm{E}[\mathbf{e}_2] \implies \mathrm{E}[\mathbf{e}_2] = \mathbf{0}.$$

Therefore the cross term contributes zero to the expectation.

*Remaining terms.* Under Perspective A, by the independence of $\theta_G$ and $\mathbf{e}_2$ (stated in §3), the expectation of their product factors:

$$\mathrm{E}\!\left[\cos^2\!\theta_G\,(\Phi\cdot\hat{u})^2\right] = \mathrm{E}[\cos^2\!\theta_G]\,(\Phi\cdot\hat{u})^2 = F\,(\Phi\cdot\hat{u})^2,$$
$$\mathrm{E}\!\left[\sin^2\!\theta_G\,(\mathbf{e}_2\cdot\hat{u})^2\right] = \mathrm{E}[\sin^2\!\theta_G]\,\mathrm{E}\!\left[(\mathbf{e}_2\cdot\hat{u})^2\right] = (1-F)\,\mathrm{E}\!\left[(\mathbf{e}_2\cdot\hat{u})^2\right],$$

where $F = \mathrm{E}[\cos^2\!\theta_G]$ and $\mathrm{E}[\sin^2\!\theta_G] = \mathrm{E}[1-\cos^2\!\theta_G] = 1-F$ (by linearity, since $\sin^2\theta + \cos^2\theta = 1$ identically). Since $\mathbf{e}_2 \perp \Phi$, we have $\Psi\cdot\Phi = \cos\theta_G$, so equivalently $F = \mathrm{E}[(\Psi\cdot\Phi)^2]$ — this is the exact second moment computed via induction in §6 under the sequential Markov dynamics of Perspective B.

Summing over both real components $\hat{u}_{2w}$ and $\hat{u}_{2w+1}$ and using $(\Phi\cdot\hat{u}_{2w})^2 + (\Phi\cdot\hat{u}_{2w+1})^2 = p_\mathrm{ideal}$:

$$\mathrm{E}[p_e] = F\,p_\mathrm{ideal} + (1-F)\,\mathrm{E}\!\left[(\mathbf{e}_2\cdot\hat{u}_{2w})^2 + (\mathbf{e}_2\cdot\hat{u}_{2w+1})^2\right].$$

It remains to compute the two unknowns: the decoherent floor $\mathrm{E}[(\mathbf{e}_2\cdot\hat{u}_{2w})^2 + (\mathbf{e}_2\cdot\hat{u}_{2w+1})^2]$ (§5) and the second moment $F$ (§6).

---

#### §5 — The decoherent floor: computing $\mathrm{E}[(\mathbf{e}_2\cdot\hat{u}_{2w})^2 + (\mathbf{e}_2\cdot\hat{u}_{2w+1})^2]$

We need $\mathrm{E}[(\mathbf{e}_2\cdot\hat{u})^2]$ for a fixed unit vector $\hat{u}$. Rather than computing an integral, we determine the full **second moment matrix** $M = \mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top]$ from symmetry and then read off the scalar result [[Muirhead (1982)](#references); [Mardia & Jupp (2000)](#references)].

$M$ is a $d\times d$ symmetric positive semidefinite matrix. It is pinned down by two constraints:

**1. Subspace symmetry.** The uniform distribution on the unit sphere of $V_\perp$ is supported on $V_\perp$ (hence $M\Phi = \mathbf{0}$) and invariant under any orthogonal transformation $R$ acting within $V_\perp$ (i.e.\ $R\Phi = \Phi$, $R$ orthogonal). Under such a transformation, $\mathbf{e}_2\to R\mathbf{e}_2$, so $M\to RMR^\top = M$. By Schur's lemma (or symmetry of the uniform spherical measure), the only symmetric matrices supported on $V_\perp$ and commuting with all orthogonal transformations of $V_\perp$ are scalar multiples of the identity on that subspace, fixing $M = c\,P_{V_\perp}$ for some scalar $c$, where $P_{V_\perp}$ is the orthogonal projector onto $V_\perp$.

**2. Normalization.** Since $|\mathbf{e}_2|^2 = 1$ always:

$$\mathrm{tr}(M) = \mathrm{E}\!\left[\mathrm{tr}(\mathbf{e}_2\mathbf{e}_2^\top)\right] = \mathrm{E}\!\left[\mathbf{e}_2^\top\mathbf{e}_2\right] = \mathrm{E}[|\mathbf{e}_2|^2] = 1.$$

Since $V_\perp$ has dimension $d-1$, we have $\mathrm{tr}(c\,P_{V_\perp}) = c(d-1)$. Setting this equal to 1:

$$c(d-1) = 1 \implies c = \frac{1}{d-1}.$$

Conclusion:

$$\mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top] = \frac{P_{V_\perp}}{d-1}.$$

**Reading off the scalar.** Using the matrix result:

$$\mathrm{E}\!\left[(\mathbf{e}_2\cdot\hat{u})^2\right] = \hat{u}^\top\,\mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top]\,\hat{u} = \frac{\hat{u}^\top P_{V_\perp}\hat{u}}{d-1} = \frac{|P_{V_\perp}\hat{u}|^2}{d-1}.$$

Projecting $\hat{u}$ onto $V_\perp$ removes its component along $\Phi$:

$$P_{V_\perp}\hat{u} = \hat{u} - (\hat{u}\cdot\Phi)\,\Phi \implies |P_{V_\perp}\hat{u}|^2 = |\hat{u}|^2 - (\hat{u}\cdot\Phi)^2 = 1 - (\hat{u}\cdot\Phi)^2.$$

Therefore $\mathrm{E}[(\mathbf{e}_2\cdot\hat{u})^2] = (1-(\hat{u}\cdot\Phi)^2)/(d-1)$.

Summing over the two real components $\hat{u}_{2w}$ and $\hat{u}_{2w+1}$, and using the fact that $(\hat{u}_{2w}\cdot\Phi)^2+(\hat{u}_{2w+1}\cdot\Phi)^2 = \Phi_{2w}^2+\Phi_{2w+1}^2 = p_\mathrm{ideal}$:

$$\mathrm{E}\!\left[(\mathbf{e}_2\cdot\hat{u}_{2w})^2 + (\mathbf{e}_2\cdot\hat{u}_{2w+1})^2\right] = \frac{(1-(\hat{u}_{2w}\cdot\Phi)^2)+(1-(\hat{u}_{2w+1}\cdot\Phi)^2)}{d-1} = \frac{2-p_\mathrm{ideal}}{d-1}.$$

When $p_\mathrm{ideal}\approx 1$, this floor is approximately $1/(d-1)\approx 1/(2N)$. In the limit $\sigma^{2G}\to 0$ (maximum decoherence within this model; note $F\geq 1/d > 0$ always), the full formula from §7 gives $\mathrm{E}[p_e]\to 2/d = 1/N$, which is simply random guessing over $N$ outcomes.

---

#### §6 — The second moment $F$ via harmonic extension and induction

We need $F = \mathrm{E}[\cos^2\!\theta_G] = \mathrm{E}[(\Psi\cdot\Phi)^2]$ (see §4). Note that this is not the same as $(\mathrm{E}[\cos\theta_G])^2 = \sigma^{2G}$; the second moment of a distribution is generally not the square of its first moment.

**Harmonic extension of $(\xi\cdot\Phi)^2$.** Apply the Poisson integral formula from §2 with $h(\xi) = (\xi\cdot\Phi)^2$. The polynomial $(\mathbf{x}\cdot\Phi)^2$ is not harmonic: $\Delta((\mathbf{x}\cdot\Phi)^2) = 2|\Phi|^2 = 2$. Since $\Delta(|\mathbf{x}|^2/d) = 2$, the function

$$H(\mathbf{x}) = (\mathbf{x}\cdot\Phi)^2 - \frac{|\mathbf{x}|^2}{d}$$

is harmonic: $\Delta H = 2 - 2 = 0$. On $S^{d-1}$ (where $|\xi|=1$), $H(\xi) = (\xi\cdot\Phi)^2 - 1/d = h(\xi) - 1/d$, so the harmonic extension of $h$ is $\tilde{h}(\mathbf{x}) = H(\mathbf{x}) + 1/d$.

**Induction over $G$ gates.** Let $f_k = \mathrm{E}[(\Psi_k\cdot\Phi)^2]$ after $k$ gate errors. We prove $f_k = ((d-1)\sigma^{2k}+1)/d$ by induction.

*Base case ($k=0$).* Before any errors, $\Psi_0 = \Phi$, so $f_0 = (\Phi\cdot\Phi)^2 = 1 = ((d-1)\cdot 1+1)/d = d/d$.

*Inductive step.* The $(k+1)$-th error acts on the current state $\Psi_k$:

$$\Psi_{k+1} = \cos\theta_{k+1}\,\Psi_k + \sin\theta_{k+1}\,\mathbf{e}_{2,k+1},$$

where $\theta_{k+1}$ has the same per-gate distribution (parameter $\sigma$) and $\mathbf{e}_{2,k+1}$ is uniform in $V_\perp^{(\Psi_k)}$, the equatorial subspace orthogonal to $\Psi_k$. Expanding $(\Psi_{k+1}\cdot\Phi)^2$:

$$(\Psi_{k+1}\cdot\Phi)^2 = \cos^2\!\theta_{k+1}(\Psi_k\cdot\Phi)^2 + \sin^2\!\theta_{k+1}(\mathbf{e}_{2,k+1}\cdot\Phi)^2 + 2\cos\theta_{k+1}\sin\theta_{k+1}(\Psi_k\cdot\Phi)(\mathbf{e}_{2,k+1}\cdot\Phi).$$

The cross term vanishes by the same argument as §4: $\mathrm{E}[\mathbf{e}_{2,k+1}\mid\Psi_k]=\mathbf{0}$ since $\mathbf{e}_{2,k+1}$ is uniform on a sphere. Conditioning on $\Psi_k$ and using independence of $\theta_{k+1}$ and $\mathbf{e}_{2,k+1}$:

$$\mathrm{E}\!\left[(\Psi_{k+1}\cdot\Phi)^2\mid\Psi_k\right] = \mathrm{E}[\cos^2\!\theta_{k+1}\mid\Psi_k]\cdot(\Psi_k\cdot\Phi)^2 + \mathrm{E}[\sin^2\!\theta_{k+1}\mid\Psi_k]\cdot\mathrm{E}\!\left[(\mathbf{e}_{2,k+1}\cdot\Phi)^2\mid\Psi_k\right].$$

Applying the §5 result to $\mathbf{e}_{2,k+1}$ (uniform in a $(d-1)$-dimensional sphere orthogonal to $\Psi_k$):

$$\mathrm{E}\!\left[(\mathbf{e}_{2,k+1}\cdot\Phi)^2\,\big|\,\Psi_k\right] = \frac{1 - (\Psi_k\cdot\Phi)^2}{d-1}.$$

For $\mathrm{E}[\cos^2\!\theta_{k+1}\mid\Psi_k]$: apply the Poisson integral formula with $h(\xi) = (\xi\cdot\Psi_k)^2$ (the squared cosine between the new state $\Psi_{k+1}$ and the current state $\Psi_k$). Its harmonic extension has the same form as derived in §6's opening — with $\Psi_k$ in place of $\Phi$ — giving $\tilde{h}(\mathbf{x}) = (\mathbf{x}\cdot\Psi_k)^2 - |\mathbf{x}|^2/d + 1/d$. Evaluating at $\mathbf{x} = \sigma\Psi_k$:

$$\mathrm{E}[\cos^2\!\theta_{k+1}\mid\Psi_k] = \tilde{h}(\sigma\Psi_k) = \sigma^2 - \frac{\sigma^2}{d} + \frac{1}{d} = \frac{(d-1)\sigma^2+1}{d} =: \lambda,$$

a **constant independent of $\Psi_k$**. By the tower property (law of total expectation):

$$f_{k+1} = \mathrm{E}\!\left[\mathrm{E}\!\left[(\Psi_{k+1}\cdot\Phi)^2\mid\Psi_k\right]\right] = \lambda\cdot f_k + (1-\lambda)\cdot\frac{1-f_k}{d-1}.$$

*Closing the induction.* Assume $f_k = ((d-1)\sigma^{2k}+1)/d$:

$$d\cdot f_{k+1} = \lambda\bigl((d-1)\sigma^{2k}+1\bigr) + (1-\lambda)(1-\sigma^{2k}) = \sigma^{2k}(\lambda d-1) + 1.$$

Since $\lambda d - 1 = (d-1)\sigma^2$:

$$d\cdot f_{k+1} = (d-1)\sigma^{2k}\cdot\sigma^2 + 1 = (d-1)\sigma^{2(k+1)} + 1.$$

Setting $k = G$:

$$F = \mathrm{E}[\cos^2\!\theta_G] = \frac{(d-1)\sigma^{2G}+1}{d}.$$

*(Note on formalization)*: In the Lean formalization, the evaluation of the second moment $\mathrm{E}[\cos^2\theta] = \frac{(d-1)\sigma^2+1}{d}$ is proved for $d=2$ via Mathlib's complex Poisson formula, while the general case for $d \ge 3$ is currently introduced as an axiom (`poissonIntegral_cos_sq_d3`, tracked in [#9](https://github.com/lazyoracle/isotropic-grover-proof/issues/9)).

---

#### §7 — Combining everything

Substitute $F$ (§6) and $\mathrm{E}[(\mathbf{e}_2\cdot\hat{u}_{2w})^2 + (\mathbf{e}_2\cdot\hat{u}_{2w+1})^2] = (2-p_\mathrm{ideal})/(d-1)$ (§5) into the result of §4:

$$\mathrm{E}[p_e] = \frac{(d-1)\sigma^{2G}+1}{d}\cdot p_\mathrm{ideal} + \left(1 - \frac{(d-1)\sigma^{2G}+1}{d}\right)\cdot\frac{2-p_\mathrm{ideal}}{d-1}.$$

First simplify $1-F$:

$$1 - F = \frac{d - \bigl((d-1)\sigma^{2G}+1\bigr)}{d} = \frac{(d-1)(1-\sigma^{2G})}{d}.$$

The factor $(d-1)$ in the numerator cancels with the $(d-1)$ in the denominator of the floor term:

$$\mathrm{E}[p_e] = \frac{(d-1)\sigma^{2G}+1}{d}\cdot p_\mathrm{ideal} \;+\; \frac{(1-\sigma^{2G})(2-p_\mathrm{ideal})}{d}.$$

Expand the full numerator (multiply through by $d$ and collect):

$$\begin{aligned}
&(d-1)\sigma^{2G}\,p_\mathrm{ideal} + p_\mathrm{ideal} + 2(1-\sigma^{2G}) - p_\mathrm{ideal}(1-\sigma^{2G})\\
= &\;(d-1)\sigma^{2G}\,p_\mathrm{ideal} + p_\mathrm{ideal}\,\sigma^{2G} + 2 - 2\sigma^{2G}\\
= &\;d\,\sigma^{2G}\,p_\mathrm{ideal} + 2(1-\sigma^{2G}).
\end{aligned}$$

Dividing by $d$ and using $2/d = 1/N$ (since $d = 2N$):

$$\boxed{\mathrm{E}[p_e] = \sigma^{2G}\cdot p_\mathrm{ideal} + \frac{1-\sigma^{2G}}{N}.}$$

All intermediate dimension-dependent factors ($d$, $d-1$) cancel exactly, leaving a closed form in $N$ alone.

---

#### §8 — Limiting cases

When $\sigma^{2G}\to 1$ (near-perfect gates or a very short circuit), $\mathrm{E}[p_e]\to p_\mathrm{ideal}$ and the noisy algorithm recovers the ideal Grover result. In the opposite regime, $\sigma^{2G}\to 0$ (heavy decoherence, or a circuit long enough that $\sigma^{G(n)}\ll 1$), the formula gives $\mathrm{E}[p_e]\to 1/N$. The algorithm reduces to random guessing over $N$ outcomes, consistent with the geometric floor from $\mathbf{e}_2 \in V_\perp$ combining with $F\to 1/d$.

---

#### <a name="references">References</a>

- L. K. Grover, "A fast quantum mechanical algorithm for database search," *Proc. 28th Annual ACM Symposium on Theory of Computing (STOC)*, pp. 212–219, 1996. [arXiv:quant-ph/9605043](https://arxiv.org/abs/quant-ph/9605043) · [DOI:10.1145/237814.237866](https://doi.org/10.1145/237814.237866)
- J. Lacalle and L. M. Pozo Coronado, "Variance of the sum of independent quantum computing errors," *Quantum Information and Computation*, vol. 19, no. 15–16, pp. 1294–1312, 2019. [DOI:10.26421/QIC19.15-16-3](https://doi.org/10.26421/QIC19.15-16-3)
- S. Axler, P. Bourdon, and W. Ramey, *Harmonic Function Theory*, 2nd ed., Graduate Texts in Mathematics vol. 137, Springer, 2001. [DOI:10.1007/978-1-4757-8137-3](https://doi.org/10.1007/978-1-4757-8137-3) (Ch. 5: Poisson kernel and its harmonic extension property.)
- R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley Series in Probability and Statistics, Wiley, New York, 1982. [DOI:10.1002/9780470316559](https://doi.org/10.1002/9780470316559) (Second moment matrix of the uniform distribution on $S^{n-1}$.)
- K. V. Mardia and P. E. Jupp, *Directional Statistics*, Wiley Series in Probability and Statistics, Wiley, Chichester, 2000. [DOI:10.1002/9780470316979](https://doi.org/10.1002/9780470316979) (Moments of uniform distributions on spheres.)
