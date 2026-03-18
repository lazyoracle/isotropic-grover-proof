### Derivation of the $\sigma^{2G(n)}$ model

#### Goal

We want a closed-form expression for $\mathrm{E}[p_e(n)]$, the **expected success probability** of Grover's algorithm on $n$ qubits when every gate is subject to an independent isotropic error with per-gate fidelity parameter $\sigma \in (0,1)$. Once we have this, the repetition overhead

$$k(n) = \frac{\log(1-p_\mathrm{ideal})}{\log(1-\mathrm{E}[p_e])}$$

can be fit as an exponential in $n$.

The result we will derive is the mixture model

$$\boxed{\mathrm{E}[p_e] = \sigma^{2G(n)} \cdot p_\mathrm{ideal} + \frac{1-\sigma^{2G(n)}}{N},}$$

where $N = 2^n$ is the database size and $G(n)$ is the gate count at optimal Grover iterations (taken directly from simulation data). This formula is **exact** for the isotropic error model — no approximations are made and all finite-size corrections cancel.

The derivation proceeds in six steps:

1. Represent the quantum state as a real vector on a hypersphere.
2. Define the isotropic error model and the distribution of the perturbation angle.
3. Collapse all $G(n)$ per-gate errors to a single effective error (composition).
4. Expand $\mathrm{E}[p_e]$ and show the cross term vanishes.
5. Compute the "decoherent floor" $\mathrm{E}[|\langle w|\mathbf{e}_2\rangle|^2]$.
6. Compute the second moment $f_2 = \mathrm{E}[\cos^2\!\theta_G]$ using Gegenbauer polynomials.

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

**Definition.** A single isotropic error with parameter $\sigma \in (0,1)$ acts on a state $\Phi \in S^{d-1}$ to produce a new state [[Lacalle & Pozo Coronado (2019)](#references)]:

$$\Psi = \cos\theta\;\Phi + \sin\theta\;\mathbf{e}_2.$$

The two random quantities on the right are:

- $\theta \in [0,\pi]$: a random angle drawn from the density $g(\theta;\sigma)$ defined below.
- $\mathbf{e}_2$: a random unit vector drawn **uniformly** from $V_\perp = \{\mathbf{v}\in\mathbb{R}^d : \mathbf{v}\cdot\Phi = 0\}$, the $(d-1)$-dimensional subspace orthogonal to $\Phi$.
- $\theta$ and $\mathbf{e}_2$ are **drawn independently** of each other.

Geometrically, $\Psi$ is $\Phi$ rotated by angle $\theta$ in a uniformly random direction in the equatorial hypersphere. Because $\mathbf{e}_2$ is isotropically distributed in $V_\perp$, no direction is preferred — the error has no axis, hence "isotropic."

**The angle distribution $g(\theta;\sigma)$.** The density is

$$g(\theta;\sigma) = \frac{(d-1)!!}{(d-2)!!} \cdot \frac{(1-\sigma^2)\sin^{d-1}\!\theta}{\pi\,(1+\sigma^2-2\sigma\cos\theta)^{(d+1)/2}}.$$

This is the *marginal* of the **Poisson kernel** of the unit ball. Here is what that means.

The Poisson kernel of the unit ball $B^d = \{\mathbf{y}\in\mathbb{R}^d : |\mathbf{y}|<1\}$ is the function

$$P(\mathbf{y},\xi) = \frac{1-|\mathbf{y}|^2}{|\mathbf{y}-\xi|^d}, \qquad \mathbf{y}\in B^d,\;\xi\in S^{d-1}.$$

It has a concrete probabilistic meaning: if a Brownian particle starts at interior point $\mathbf{y}$ and runs until it first hits the boundary $S^{d-1}$, then $P(\mathbf{y},\xi)/\int P$ is the probability density of the hitting point $\xi$. Now place the interior point along the first axis at distance $\sigma$ from the origin: $\mathbf{y} = \sigma\mathbf{e}_1$. By rotational symmetry, the distance from $\mathbf{y}$ to any boundary point $\xi$ depends only on the angle $\theta$ between $\mathbf{e}_1$ and $\xi$:

$$|\sigma\mathbf{e}_1 - \xi|^2 = \sigma^2 - 2\sigma(\mathbf{e}_1\cdot\xi) + 1 = 1+\sigma^2-2\sigma\cos\theta,$$

so $P(\sigma\mathbf{e}_1,\xi) = (1-\sigma^2)/(1+\sigma^2-2\sigma\cos\theta)^{d/2}$.

The Poisson kernel is now a distribution over all of $S^{d-1}$, but it only depends on $\xi$ through the single angle $\theta$. To obtain a 1D density over $\theta$ alone — the "marginal" — we integrate over all boundary points at each fixed $\theta$. For a given $\theta$, those points form a $(d-2)$-sphere (a "latitude circle" on $S^{d-1}$), whose surface area element is proportional to $\sin^{d-2}\theta\,d\theta$. Multiplying and normalizing gives $g(\theta;\sigma) \propto (1-\sigma^2)\sin^{d-2}\theta/(1+\sigma^2-2\sigma\cos\theta)^{d/2}$. (The formula above has exponents shifted by $\tfrac{1}{2}$ because Lacalle & Pozo Coronado (2019) define the isotropic normal distribution via the Poisson kernel on $S^d$ rather than $S^{d-1}$; this does not affect any of the calculations below.)

**Why $\mathrm{E}[\cos\theta] = \sigma$.** This is the $l=1$ case of the Gegenbauer moment theorem stated and used in §6. Briefly: the Poisson kernel is the generating function for Gegenbauer polynomials (the zonal spherical harmonics on $S^{d-1}$) [[Axler, Bourdon & Ramey (2001)](#references), Ch. 5], and its $l$-th Gegenbauer moment equals $\sigma^l$. The first Gegenbauer polynomial is $C_1^\lambda(\cos\theta) = 2\lambda\cos\theta$ (see §6), so the $l=1$ moment gives

$$\mathrm{E}[2\lambda\cos\theta] = \sigma^1\cdot 2\lambda \implies \mathrm{E}[\cos\theta] = \sigma.$$

Physically: $\sigma = \mathrm{E}[\cos\theta]$ is the **average amplitude overlap** between the perturbed state $\Psi$ and the ideal state $\Phi$. This is the precise definition of the fidelity parameter — $\sigma=1$ means no rotation (perfect gate), $\sigma=0$ means a uniformly random final state.

---

#### §3 — Composition: $G(n)$ gates reduce to a single effective error

**Commutativity with gates.** Isotropic errors commute with unitary quantum gates [[Lacalle & Pozo Coronado (2019)](#references)]:

$$U \circ E = E' \circ U,$$

where $E'$ has the same distribution as $E$. Physically, an isotropic error has no preferred axis — it perturbs the state in all equatorial directions equally — so it cannot "know" which gate acts before or after it, and the order is irrelevant. This means every per-gate error can be commuted past all subsequent gates to the end of the circuit, just before measurement.

**Composition of errors.** Two independent isotropic errors with parameters $\sigma_1$ and $\sigma_2$ compose to a single isotropic error with parameter $\sigma_1\sigma_2$ [[Lacalle & Pozo Coronado (2019)](#references)]. This is a consequence of the Gegenbauer moment property: composing two distributions with $l$-th moments $\sigma_1^l$ and $\sigma_2^l$ gives a distribution with $l$-th moment $(\sigma_1\sigma_2)^l$, which is the Poisson kernel distribution with parameter $\sigma_1\sigma_2$. Therefore $G(n)$ independent per-gate errors each with parameter $\sigma$ compose to a single effective error with parameter

$$\sigma_\mathrm{eff} = \sigma^{G(n)}.$$

From this point forward we work with a single effective error applied to the ideal final state $\Phi$:

$$\Psi = \cos\theta_G\;\Phi + \sin\theta_G\;\mathbf{e}_2,$$

where $\theta_G$ has density $g(\theta;\sigma^{G(n)})$ and $\mathrm{E}[\cos\theta_G] = \sigma^{G(n)}$.

---

#### §4 — Expanding $\mathrm{E}[p_e]$: the cross term

The noisy success probability is, from §1,

$$p_e = (\Psi\cdot\hat{u}_{2w})^2 + (\Psi\cdot\hat{u}_{2w+1})^2.$$

Both components have the same form, so we expand $(\Psi\cdot\hat{u})^2$ for a generic unit vector $\hat{u}$ and sum at the end. Substituting $\Psi = \cos\theta_G\,\Phi + \sin\theta_G\,\mathbf{e}_2$:

$$\Psi\cdot\hat{u} = \cos\theta_G\,(\Phi\cdot\hat{u}) + \sin\theta_G\,(\mathbf{e}_2\cdot\hat{u}).$$

Squaring (every term is real):

$$(\Psi\cdot\hat{u})^2 = \underbrace{\cos^2\!\theta_G\,(\Phi\cdot\hat{u})^2}_{\text{ideal term}} + \underbrace{\sin^2\!\theta_G\,(\mathbf{e}_2\cdot\hat{u})^2}_{\text{noise term}} + \underbrace{2\cos\theta_G\sin\theta_G\,(\Phi\cdot\hat{u})(\mathbf{e}_2\cdot\hat{u})}_{\text{cross term}}.$$

**Taking the expectation.**

*Cross term vanishes.* Condition on $\theta_G$ and $\Phi$ (both fixed). Then $\mathbf{e}_2$ is the only random quantity, and $\mathrm{E}[\mathbf{e}_2\cdot\hat{u}] = \hat{u}\cdot\mathrm{E}[\mathbf{e}_2]$. Now $\mathrm{E}[\mathbf{e}_2] = \mathbf{0}$ because the uniform distribution on $V_\perp$ is symmetric under the antipodal map $\mathbf{e}_2\mapsto -\mathbf{e}_2$ (every point and its antipode are equally likely, so the distribution is preserved), which forces

$$\mathrm{E}[\mathbf{e}_2] = \mathrm{E}[-\mathbf{e}_2] = -\mathrm{E}[\mathbf{e}_2] \implies \mathrm{E}[\mathbf{e}_2] = \mathbf{0}.$$

Therefore the cross term contributes zero to the expectation.

*Remaining terms.* By the independence of $\theta_G$ and $\mathbf{e}_2$ (stated in §2), the expectation of their product factors:

$$\mathrm{E}\!\left[\cos^2\!\theta_G\,(\Phi\cdot\hat{u})^2\right] = \mathrm{E}[\cos^2\!\theta_G]\,(\Phi\cdot\hat{u})^2 = f_2\,(\Phi\cdot\hat{u})^2,$$
$$\mathrm{E}\!\left[\sin^2\!\theta_G\,(\mathbf{e}_2\cdot\hat{u})^2\right] = \mathrm{E}[\sin^2\!\theta_G]\,\mathrm{E}\!\left[(\mathbf{e}_2\cdot\hat{u})^2\right] = (1-f_2)\,\mathrm{E}\!\left[(\mathbf{e}_2\cdot\hat{u})^2\right],$$

where $f_2 = \mathrm{E}[\cos^2\!\theta_G]$ and $\mathrm{E}[\sin^2\!\theta_G] = \mathrm{E}[1-\cos^2\!\theta_G] = 1-f_2$ (by linearity, since $\sin^2\theta + \cos^2\theta = 1$ identically).

Summing over both real components $\hat{u}_{2w}$ and $\hat{u}_{2w+1}$ and using $(\Phi\cdot\hat{u}_{2w})^2 + (\Phi\cdot\hat{u}_{2w+1})^2 = p_\mathrm{ideal}$:

$$\mathrm{E}[p_e] = f_2\,p_\mathrm{ideal} + (1-f_2)\,\mathrm{E}\!\left[|\langle w|\mathbf{e}_2\rangle|^2\right].$$

It remains to compute the two unknowns: the decoherent floor $\mathrm{E}[|\langle w|\mathbf{e}_2\rangle|^2]$ (§5) and the second moment $f_2$ (§6).

---

#### §5 — The decoherent floor: computing $\mathrm{E}[|\langle w|\mathbf{e}_2\rangle|^2]$

We need $\mathrm{E}[(\mathbf{e}_2\cdot\hat{u})^2]$ for a fixed unit vector $\hat{u}$. Rather than computing an integral, we determine the full **second moment matrix** $M = \mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top]$ from symmetry and then read off the scalar result [[Muirhead (1982)](#references); [Mardia & Jupp (2000)](#references)].

$M$ is a $d\times d$ symmetric positive semidefinite matrix. It is pinned down by three constraints:

**1. Range.** Since $\mathbf{e}_2 \in V_\perp$ always, every component of $\mathbf{e}_2$ in the direction of $\Phi$ is zero. The outer product $\mathbf{e}_2\mathbf{e}_2^\top$ therefore maps every vector into $V_\perp$ and annihilates the $\Phi$-direction. So $M$ must be of the form $M = c\,P_{V_\perp}$ for some scalar $c$, where $P_{V_\perp}$ is the orthogonal projector onto $V_\perp$ (this also follows from constraint 2).

**2. Rotational symmetry within $V_\perp$.** The uniform distribution on the unit sphere of $V_\perp$ is invariant under any rotation $R$ that acts within $V_\perp$ (i.e.\ $R\Phi = \Phi$, $R$ unitary). Under such a rotation, $\mathbf{e}_2\to R\mathbf{e}_2$, so $M\to RMR^\top = M$. The only matrices commuting with all rotations within a subspace $V_\perp$ are scalar multiples of the identity on that subspace, confirming $M = c\,P_{V_\perp}$.

**3. Trace constraint.** Since $|\mathbf{e}_2|^2 = 1$ always:

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

$$\mathrm{E}\!\left[|\langle w|\mathbf{e}_2\rangle|^2\right] = \frac{(1-(\hat{u}_{2w}\cdot\Phi)^2)+(1-(\hat{u}_{2w+1}\cdot\Phi)^2)}{d-1} = \frac{2-p_\mathrm{ideal}}{d-1}.$$

**Physical interpretation.** When the circuit is completely decoherent ($f_2\to 0$), $\mathrm{E}[p_e]\to(2-p_\mathrm{ideal})/(d-1)$. For large $n$, $p_\mathrm{ideal}\to 1$ and $d=2N\to\infty$, so this approaches $1/N$ — random guessing. This decoherent floor is not assumed; it follows exactly from the geometry of $\mathbf{e}_2$ in $V_\perp$.

---

#### §6 — The second moment $f_2$ from Gegenbauer polynomials

We need $f_2 = \mathrm{E}[\cos^2\!\theta_G]$. Note that this is not the same as $(\mathrm{E}[\cos\theta_G])^2 = \sigma^{2G}$; the second moment of a distribution is generally not the square of its first moment. We need the Gegenbauer polynomial machinery to relate the two.

**Gegenbauer polynomials.** The Gegenbauer polynomials $C_l^\lambda(x)$, $\lambda>0$, are a family of polynomials orthogonal on $[-1,1]$ with weight $(1-x^2)^{\lambda-1/2}$ [[Axler, Bourdon & Ramey (2001)](#references), Ch. 5]. They arise naturally on spheres: $C_l^\lambda(\cos\theta)$ are the rotationally symmetric ("zonal") eigenfunctions of the Laplacian on $S^{d-1}$, with $\lambda = (d-2)/2$. The first three, at the value $\lambda = (d-2)/2$, are:

$$C_0^\lambda(x) = 1, \qquad C_1^\lambda(x) = 2\lambda x, \qquad C_2^\lambda(x) = 2\lambda(\lambda+1)x^2 - \lambda.$$

These can be verified by the recurrence $C_l^\lambda(x) = \frac{1}{l}\bigl[2x(\lambda+l-1)C_{l-1}^\lambda(x) - (2\lambda+l-2)C_{l-2}^\lambda(x)\bigr]$ starting from $C_0^\lambda = 1$, $C_1^\lambda(x) = 2\lambda x$.

**Key theorem: Poisson kernel moments [[Axler, Bourdon & Ramey (2001)](#references), Ch. 5].** For $\theta$ distributed according to $g(\theta;\sigma)$:

$$\mathrm{E}\!\left[C_l^\lambda(\cos\theta)\right] = \sigma^l \cdot C_l^\lambda(1), \qquad l = 0,1,2,\ldots$$

This holds because the Poisson kernel $P(\sigma\mathbf{e}_1,\xi)$, as a function of $\cos\theta$, has a series expansion in Gegenbauer polynomials whose $l$-th coefficient is precisely $\sigma^l$. Integrating $C_l^\lambda(\cos\theta)$ against the Poisson kernel marginal $g(\theta;\sigma)$ then picks out this coefficient.

*Consistency check at $l=1$:* $C_1^\lambda(\cos\theta) = 2\lambda\cos\theta$ and $C_1^\lambda(1) = 2\lambda$, so the theorem gives $\mathrm{E}[2\lambda\cos\theta] = \sigma\cdot 2\lambda$, confirming $\mathrm{E}[\cos\theta] = \sigma$ as stated in §2.

**Applying the theorem at $l=2$.** With $\lambda = (d-2)/2$, evaluate $C_2^\lambda$ at $x=1$:

$$C_2^\lambda(1) = 2\lambda(\lambda+1)(1)^2 - \lambda = 2\lambda(\lambda+1) - \lambda = \lambda\bigl(2(\lambda+1)-1\bigr) = \lambda(2\lambda+1).$$

Now substitute $2\lambda = d-2$, so $2\lambda+1 = d-1$:

$$C_2^\lambda(1) = \lambda(d-1).$$

The theorem gives:

$$\mathrm{E}\!\left[2\lambda(\lambda+1)\cos^2\!\theta - \lambda\right] = \sigma^2\cdot\lambda(d-1).$$

Apply linearity of expectation:

$$2\lambda(\lambda+1)\,\mathrm{E}[\cos^2\!\theta] - \lambda = \sigma^2\lambda(d-1).$$

Isolate $\mathrm{E}[\cos^2\!\theta]$ (dividing through by $2\lambda(\lambda+1)$, using $2(\lambda+1) = d$):

$$\mathrm{E}[\cos^2\!\theta] = \frac{\sigma^2\lambda(d-1)+\lambda}{2\lambda(\lambda+1)} = \frac{(d-1)\sigma^2+1}{2(\lambda+1)} = \frac{(d-1)\sigma^2+1}{d}.$$

After $G$ gates, the composed error has $\sigma\to\sigma^G$:

$$f_2 = \mathrm{E}[\cos^2\!\theta_G] = \frac{(d-1)\sigma^{2G}+1}{d}.$$

---

#### §7 — Combining everything

Substitute $f_2$ (§6) and $\mathrm{E}[|\langle w|\mathbf{e}_2\rangle|^2] = (2-p_\mathrm{ideal})/(d-1)$ (§5) into the result of §4:

$$\mathrm{E}[p_e] = \frac{(d-1)\sigma^{2G}+1}{d}\cdot p_\mathrm{ideal} + \left(1 - \frac{(d-1)\sigma^{2G}+1}{d}\right)\cdot\frac{2-p_\mathrm{ideal}}{d-1}.$$

First simplify $1-f_2$:

$$1 - f_2 = \frac{d - \bigl((d-1)\sigma^{2G}+1\bigr)}{d} = \frac{(d-1)(1-\sigma^{2G})}{d}.$$

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

No approximations were made. All finite-$d$ corrections cancel exactly.

---

#### §8 — Limiting cases

**When $\sigma^{2G}\to 1$** (near-perfect gates or very short circuit): $\mathrm{E}[p_e]\to p_\mathrm{ideal}$. The noisy algorithm recovers the ideal Grover result.

**When $\sigma^{2G}\to 0$** (heavy decoherence, or the circuit is so long that $\sigma^{G(n)}\ll 1$): $\mathrm{E}[p_e]\to 1/N$. The algorithm is no better than a random guess over $N$ outcomes. This floor follows from the geometry of $\mathbf{e}_2$ in $V_\perp$ — it is not separately assumed.

---

#### <a name="references">References</a>

- L. K. Grover, "A fast quantum mechanical algorithm for database search," *Proc. 28th Annual ACM Symposium on Theory of Computing (STOC)*, pp. 212–219, 1996. [arXiv:quant-ph/9605043](https://arxiv.org/abs/quant-ph/9605043) · [DOI:10.1145/237814.237866](https://doi.org/10.1145/237814.237866)
- J. Lacalle and L. M. Pozo Coronado, "Variance of the sum of independent quantum computing errors," *Quantum Information and Computation*, vol. 19, no. 15–16, pp. 1294–1312, 2019. [DOI:10.26421/QIC19.15-16-3](https://doi.org/10.26421/QIC19.15-16-3)
- S. Axler, P. Bourdon, and W. Ramey, *Harmonic Function Theory*, 2nd ed., Graduate Texts in Mathematics vol. 137, Springer, 2001. [DOI:10.1007/978-1-4757-8137-3](https://doi.org/10.1007/978-1-4757-8137-3) (Ch. 5: Poisson kernel and its Gegenbauer expansion into zonal spherical harmonics.)
- R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley Series in Probability and Statistics, Wiley, New York, 1982. [DOI:10.1002/9780470316559](https://doi.org/10.1002/9780470316559) (Second moment matrix of the uniform distribution on $S^{n-1}$.)
- K. V. Mardia and P. E. Jupp, *Directional Statistics*, Wiley Series in Probability and Statistics, Wiley, Chichester, 2000. [DOI:10.1002/9780470316979](https://doi.org/10.1002/9780470316979) (Moments of uniform distributions on spheres.)
