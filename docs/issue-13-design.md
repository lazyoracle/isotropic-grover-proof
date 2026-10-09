# Issue #13 Design Document: Ground Multi-Gate Error Accumulation in §6 Markov Induction

## Problem Context
In `english-proof.md` (§3, lines 107–123), the multi-gate error accumulation was originally presented via an informal argument:
1. Isotropic errors commute with unitary gates ($U \circ E = E' \circ U$).
2. All $G(n)$ gate errors are commuted to the end of the circuit.
3. The claim was made that because each individual error is isotropic, the composition of $G$ such rotations on the sphere collapses identically into a single uniform isotropic rotation around the target state $\Phi$:
   $$\Psi = \cos\theta_G\,\Phi + \sin\theta_G\,\mathbf{e}_2,$$
   where $\mathbf{e}_2 \in V_\perp(\Phi)$ is uniformly distributed on $S^{d-2}$ and independent of the accumulated angle $\theta_G \sim P(\sigma^G \Phi, \cdot)$.

As identified in adversarial reviews and Issue #13:
- In sequential quantum evolution, the $k$-th error acts on the *current perturbed state* $\Psi_k$, rotating around $\Psi_k$ rather than the initial state $\Phi$.
- The claim that $G$ sequential rotations across dynamically tilted equatorial spheres compose into a single uniform rotation around $\Phi$ with independent angle $\theta_G$ is a substantial probabilistic claim (spherical convolution on $SO(d)$ / $S^{d-1}$) stated merely by citation ([Lacalle & Pozo Coronado 2019]).
- This step was bypassed in Lean using a vacuous `rfl` theorem and a definitional shortcut (`composedMeasure d G σ := poissonMarginal d (σ^G)`), tracked in Issue #6 and Issue #7.

## Goals & Remediation
Restructure §3 of `english-proof.md` to:
1. **Differentiate the two distinct perspectives:**
   - **Perspective A (Single-step effective error representation / ansatz):**
     Treating the multi-gate error as an effective single-step isotropic perturbation around $\Phi$ with parameter $\sigma^G$:
     $$\Psi = \cos\theta_G\,\Phi + \sin\theta_G\,\mathbf{e}_2, \qquad \mathbf{e}_2 \in V_\perp(\Phi).$$
     This ansatz is analytically convenient, intuitive, and matches the formal definition `composedMeasure` used in `IsotropicGroverProof/Composition.lean`. However, as a microscopic derivation, collapsing sequential rotations on evolving subspaces into a single rotation around $\Phi$ is an assertion of spherical convolution closure.
   - **Perspective B (Sequential gate-level Markov chain evolution):**
     The true microscopic physical process:
     $$\Psi_0 = \Phi, \qquad \Psi_{k+1} = \cos\theta_{k+1}\,\Psi_k + \sin\theta_{k+1}\,\mathbf{e}_{2,k+1},$$
     where $\mathbf{e}_{2,k+1}$ is uniform on the equatorial sphere orthogonal to $\Psi_k$, and $\theta_{k+1}$ is drawn from the per-gate Poisson kernel with parameter $\sigma$.
2. **Ground the headline formula in §6 Markov induction:**
   - Explain that the headline expectation $\mathrm{E}[p_e] = \sigma^{2G} p_\mathrm{ideal} + \frac{1-\sigma^{2G}}{N}$ does **not** rely on global commutativity, spherical convolution, or the collapse of $\Psi_G$ into a single rotation around $\Phi$.
   - The fidelity and success probability depend only on the second moment $f_k = \mathrm{E}[(\Psi_k \cdot \Phi)^2]$.
   - In §6, this recurrence is proven rigorously by induction:
     $$f_{k+1} = \lambda f_k + (1-\lambda)\frac{1-f_k}{d-1}, \qquad \lambda = \frac{(d-1)\sigma^2+1}{d},$$
     using *only* single-step properties (subspace symmetry around $\Psi_k$ and the per-gate Poisson second moment).
   - The recurrence has the unique closed-form solution:
     $$f_G = \frac{(d-1)\sigma^{2G}+1}{d},$$
     which produces the headline formula without requiring global composition or spherical convolution.
3. **Cross-reference formalization tracking issues:**
   - Reference §6 for the complete inductive proof.
   - Explicitly link to Issue #6 (formalization of the spherical convolution identity or its axiomatic status) and Issue #7 (formalization of the sequential Markov chain recurrence and induction in Lean).
