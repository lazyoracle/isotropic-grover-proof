# Exact Expected Success Probability of Noisy Quantum Circuits and Grover's Algorithm Under Isotropic Gate Errors

## Executive Summary

This document presents a self-contained, gap-free mathematical derivation — together with a complete 1-to-1 map to its Lean 4 formalization in `IsotropicGroverProof/` — of the **exact expected measurement probability** $`\mathrm{E}[p_e]`$ of an $`n`$-qubit quantum computation when every gate is followed by an independent isotropic pure-state perturbation of fidelity parameter $`\sigma \in [0, 1]`$. Across $`G \in \mathbb{N}`$ noisy gate operations on a Hilbert space of complex dimension $`N = 2^n`$ (real sphere dimension $`d = 2N = 2^{n+1}`$), the expected probability of measuring computational basis state $`|w\rangle`$ is:

$$
\boxed{\mathrm{E}[p_e] = \sigma^{2G}\thinspace p_{\mathrm{ideal}} + \frac{1 - \sigma^{2G}}{N}, \qquad N = 2^n, \quad \sigma \in [0, 1], \quad G, n \in \mathbb{N},}
$$

where $`p_{\mathrm{ideal}} = |\langle w | \psi_{\mathrm{ideal}} \rangle|^2`$ is the noiseless Born-rule probability of outcome $`w`$.

### Three Unified Levels of Formal Verification

The derivation and its Lean 4 formalization establish this convex mixture identity with **zero approximations**, **zero `sorry`s**, and **zero custom axioms** (`[propext, Classical.choice, Quot.sound]`) across three progressively richer physical and syntactic representations:

**1. Microscopic pure-state Markov chain on $`S^{d-1} \subset \mathbb{R}^{2 \cdot 2^n}`$ (`Sequential.lean`):** Starting from any unit state $`\Phi_0 \in S^{d-1}`$ and executing any sequence `gates` of $`G`$ linear isometries interleaved with state-dependent isotropic great-circle perturbations $`\Psi_k = \cos\theta_k\,(U_k\Psi_{k-1}) + \sin\theta_k\,\mathbf{e}_{2,k}`$ (with $`\mathbf{e}_{2,k} \perp U_k\Psi_{k-1}`$ uniform on the instantaneous equatorial $`(d-2)`$-sphere and $`\theta_k`$ drawn from the spherical Poisson marginal on $`[0, \pi]`$), the $`G`$-fold nested expectation evaluates to $`\sigma^{2G}\,p_{\mathrm{ideal}} + (1 - \sigma^{2G})/2^n`$ (`noisyTrajectory_succProb`). On the interior domain $`\sigma \in (0, 1)`$ and $`G > 0`$, this matches the single-effective-error formulation `isotropicGrover_main` (`MainTheorem.lean`).

**2. Emergence of the quantum depolarizing `CPTPMap` and syntactic `Circuit.size` (`QuantumChannel.lean`):** Translating the real unit sphere isometrically to `Physlib`'s `QuantumInfo` kets (`Ket`), density matrices (`MState`), completely positive trace-preserving maps (`CPTPMap`), and projective measurements (`POVM`), averaging the rank-1 projector $`|\psi'\rangle\langle\psi'|`$ over a single microscopic real-sphere perturbation causes imaginary even/odd cross-terms to cancel identically and diagonal noise floors to sum as $`\frac{1}{d} + \frac{1}{d} = \frac{1}{N}`$, yielding **exact** emergence of the complex $`n`$-qubit depolarizing channel (`isotropicOneStep_eq_depolarizingChannel`):

$$
\Lambda_\sigma(\rho) = \sigma^2 \rho + (1 - \sigma^2)\thinspace\frac{I_N}{N}.
$$

For any syntactic primitive-gate circuit `c : Circuit n` in `formal-quantum-computation`, gate-by-gate depolarizing channels commute past unitaries (`depolarizingChannel_comm_ofUnitary`) and compose multiplicatively (`depolarizingChannel_compose`) into $`\Lambda_{\sigma^{c.\mathrm{size}}} \circ \mathcal{U}_{c.\mathrm{eval}}`$ (`noisyCircuitChannel_eq`), giving exact Born probability $`\sigma^{2\,c.\mathrm{size}}\,p_{\mathrm{ideal}} + (1 - \sigma^{2\,c.\mathrm{size}})/2^n`$ (`noisyCircuit_bornProb`, `noisyCircuit_bornProb_pure`) where $`G = c.\mathrm{size}`$ is counted directly from the circuit AST.

**3. Specialization to Grover's search algorithm and primitive-gate circuits (`GroverCircuit.lean`):** Connecting to `formal-quantum-computation`'s Grover phase oracle `Grover.oracleUnitary`, diffuser `Grover.diffuserUnitary`, and Hadamard preparation `hadamardUnitary` after $`K \in \mathbb{N}`$ iterations — where `Grover.p_succ` gives $`p_{\mathrm{ideal}} = p_{\mathrm{succ}}(K, 2^n) = \sin^2\bigl((2K + 1)\arcsin(2^{-n/2})\bigr)`$ — proves

$$
\mathrm{E}[p_e] = \sigma^{2G}\sin^2\negthinspace\Bigl((2K + 1)\arcsin\bigl(2^{-n/2}\bigr)\Bigr) + \frac{1 - \sigma^{2G}}{2^n}
$$

across macro-iteration lists ($`G = 2K`$ in `noisyGrover_iterGates_succProb` and $`G = 2K + 1`$ in `noisyGrover_fullGates_succProb`), arbitrary unitary gate decompositions (`noisyGrover_unitaryList_bornProb`), syntactic circuits `c : Circuit n` ($`G = c.\mathrm{size}`$ in `noisyGrover_circuit_bornProb`), and concrete verified 1-qubit (`Circuit.H 0`, $`c.\mathrm{size} = 1`$) and 2-qubit (`grover2QubitCircuit`, $`c.\mathrm{size} = 14`$, $`K = 1`$) primitive-gate circuits.

### Exactness, Parameter Domains, and Physical Assumptions

- **Exact finite-dimensional cancellation:** Every intermediate dimension-dependent factor involving $`d = 2^{n+1}`$ and $`d - 1 = 2^{n+1} - 1`$ cancels algebraically — already at the single-gate real bilinear operator level (§4). No large-$`N`$ or small-angle approximations are invoked anywhere.
- **Parameter domains:** All sequential Markov-trajectory, `CPTPMap`, syntactic `Circuit n`, and dynamic Grover theorems hold across the **entire closed interval** $`\sigma \in [0, 1]`$ (`Set.Icc 0 1`) and **all** natural numbers $`G, K, n \in \mathbb{N}`$ (including $`G = 0`$, $`K = 0`$, $`n = 0`$, $`\sigma = 0`$, and $`\sigma = 1`$). The earlier single-effective-step theorems (`composedMeasure`, `expanded_E_pe`, `f₂_formula`, `isotropicGrover_main`) — along with the four static Grover search-plane wrappers (`isotropicGrover_uniformSuperposition`, `isotropicGrover_groverState2D`, `isotropicGrover_groverState2D_prob`, `isotropicGrover_targetBasisState`, with `1 < 2 ^ n` on the two `groverState2D` theorems so that $`|w^\perp\rangle`$ is non-empty) — are stated on the open interval $`\sigma \in (0, 1)`$ (`Set.Ioo 0 1`) and $`G > 0`$, where the unextended density `poissonMarginal` is smooth and strictly positive on $`(0, \pi)`$.
- **Physical noise model assumptions:** Exactness is conditional on the isotropic pure-state gate-error model [[Lacalle & Pozo Coronado (2019)](#references)]: after each gate, the state undergoes an independent random rotation on $`S^{d-1}`$ with polar angle $`\theta`$ drawn from the spherical Poisson marginal (`poissonAngleMeasure`) and orthogonal direction $`\mathbf{e}_2`$ drawn uniformly from the equatorial sphere $`V_\perp(\Psi) \cap S^{d-1}`$ (`perpSphereMeasure`). Crucially, **no global spherical-angle convolution assumption on $`\mathrm{SO}(d)`$ is needed**: multi-gate accumulation is proved directly from single-step conditional expectations (§6).
- **Gate count $`G`$ vs. downstream repetition analysis:** In general trajectory theorems, $`G`$ is the length of the gate list (`gates.length`); in syntactic circuit theorems, $`G = c.\mathrm{size}`$ is machine-computed from primitive gates (`X, Y, Z, H, S, T, CNOT, SWAP, TOFF`). Substituting transpiled empirical counts $`G(n)`$ or asymptotic scalings $`G(n) \propto \frac{\pi}{4}\sqrt{2^n}`$, and fitting the multi-run repetition overhead $`k(n) = \frac{\log(1 - p_{\mathrm{ideal}})}{\log(1 - \mathrm{E}[p_e])}`$ to an exponential $`a \cdot b^n + c`$, are downstream analytical applications (§8.2) outside the Lean formalization.

### Lean Formalization Map

Every module listed below is imported transitively by `IsotropicGroverProof/Basic.lean` (re-exported by `IsotropicGroverProof.lean`) and audited in CI with `lake build --wfail` and `axiom-audit`.

| Section | Mathematical Step | Lean Module | Key Verified Declarations |
| :--- | :--- | :--- | :--- |
| **§1** | $`\mathbb{C}^{2^n} \cong \mathbb{R}^{2 \cdot 2^n}`$ isomorphism, `Ket`/`MState` unitaries, and Born-rule `POVM` bridge | `Defs.lean`, `QuantumChannel.lean` | `d`, `E`, `unitSphere`, `succProb`, `sum_succProb_eq_norm_sq`, `vecToReal`, `realToVec`, `ketToReal`, `realToKet`, `unitaryToRealIso`, `computationalPOVM`, `succProb_ketToReal_eq_born` |
| **§2** | Single-gate isotropic sphere error across $`\sigma \in [0, 1]`$ | `IsotropicError.lean`, `CrossTerm.lean` | `poissonKernelDensity`, `poissonMarginal`, `poissonAngleMeasure`, `poissonAngleMeasure_isProbMeasure`, `isotropicError`, `isotropicError_norm`, `V_perp`, `perpSphereMeasure`, `perpSphereMeasure_isProbMeasure` |
| **§3** | Exact Poisson moments $`\mathrm{E}[\cos\theta] = \sigma`$ and $`\mathrm{E}[\cos^2\theta] = \frac{(d-1)\sigma^2+1}{d}`$ via harmonic polynomial algebra and 1D FTC + two-step induction | `IsotropicError.lean`, `Gegenbauer.lean`, `Composition.lean` | `halfcircle_cos_eq`, `halfcircle_cos_sq_eq`, `poissonMarginal_mean_cos`, `poissonAngleMeasure_mean_cos`, `poissonAngleMeasure_cos_sq`, `poissonIntegral_cos_sq`, `laplacian_trace_cancellation`, `harmonicExtension_eval`, `composedMeasure`, `f₂_formula` *(plus private FTC helpers `antiderivG0`, `antiderivF0`, `antiderivG1`, `antiderivH3` in `IsotropicError.lean`)* |
| **§4** | Equatorial reflection symmetries, $`\mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top] = \frac{P_\perp}{d-1}`$, and single-step bilinear $`(d-1)`$ cancellation | `CrossTerm.lean`, `SecondMoment.lean` | `perpSphereMeasure_neg_invariant`, `perpSphereMeasure_map_isometry`, `integral_perp_inner_eq_zero`, `expanded_E_pe`, `P_perp`, `secondMoment_coeff`, `decoherent_floor`, `perpSphere_inner_mul_inner`, `isotropicError_bilinear_secondMoment`, `isotropicError_succProb_oneStep` |
| **§5** | Exact emergence of the complex depolarizing `CPTPMap` $`\Lambda_\sigma(\rho) = \sigma^2\rho + (1-\sigma^2)\frac{I_N}{N}`$ | `QuantumChannel.lean` | `pureDensityMatrix`, `pureDensityMatrix_ketToReal`, `depolarizingChannel`, `noisyTrajectory_pureDensityMatrix_re`, `noisyTrajectory_pureDensityMatrix_im`, `isotropicOneStep_eq_depolarizingChannel`, `noisyTrajectory_eq_depolarizingChannel`, `noisyTrajectoryHet_pureDensityMatrix_re`, `noisyTrajectoryHet_pureDensityMatrix_im`, `noisyTrajectoryExpectationℂHet`, `noisyTrajectoryHet_eq_depolarizingChannel` |
| **§6** | Multi-gate accumulation: pure-state Markov chain (uniform & heterogeneous), unitary channel commutation, semigroup composition, and syntactic `Circuit.size` / `Circuit.count` | `Sequential.lean`, `QuantumChannel.lean`, `MainTheorem.lean` | `stepLambda`, `stepTransition_sub_inv_d`, `sequentialFidelity_eq`, `sequential_mixture_formula`, `fidelityProd`, `idealGateTrajectory`, `idealGateTrajectoryHet`, `noisyTrajectoryExpectation`, `noisyTrajectoryExpectationHet`, `noisyTrajectoryHet_eq_uniform`, `noisyTrajectoryHet_bilinear`, `noisyTrajectory_bilinear`, `noisyTrajectory_fidelity_eq_sequentialFidelity`, `noisyTrajectoryHet_succProb`, `noisyTrajectory_succProb`, `isotropicGrover_main`, `depolarizingChannel_comm_ofUnitary`, `depolarizingChannel_compose`, `noisyCircuitChannel_eq`, `noisyCircuit_trajectory_succProb_eq_measure`, `noisyCircuit_bornProb`, `noisyCircuit_bornProb_pure`, `circuitFidelity`, `noisyCircuitChannelHet_eq`, `noisyCircuitHet_trajectory_eq_channel`, `circuitFidelity_eq_prod_count`, `circuitFidelity_arity`, `gateCount_sum_eq_size` |
| **§7** | Grover's algorithm specialization (`Grover.p_succ`), multi-target ($`M`$-marked-item) search, and concrete 1- and 2-qubit primitive-gate circuits | `GroverCircuit.lean` | `targetBasisState`, `targetPerpState`, `uniformSuperposition`, `groverState2D`, `isotropicGrover_uniformSuperposition`, `isotropicGrover_groverState2D`, `groverIterGates`, `groverFullGates`, `idealUnitaryTrajectory_groverFullGates`, `groverState_bornProb`, `noisyGrover_iterGates_succProb`, `noisyGrover_fullGates_succProb`, `noisyGrover_unitaryList_bornProb`, `noisyGrover_circuit_bornProb`, `noisyGrover_circuit_groverMatrix_bornProb`, `noisyGrover_circuit_hadamard1_bornProb`, `grover2QubitCircuit`, `noisyGrover_circuit_grover2_bornProb`, `circuitFidelity_grover2QubitCircuit`, `noisyGroverHet_circuit_grover2_bornProb`, `subsetSuccProb`, `noisyTrajectoryHet_subsetSuccProb`, `noisyCircuitHet_subsetBornProb`, `multiOracleUnitary`, `multiGroverStep`, `multiGrover_ideal_subsetSuccProb`, `noisyMultiGroverHet_succProb`, `noisyMultiGroverHet_circuit_bornProb` |
| **§8** | Limiting regimes ($`\sigma = 1`$, $`\sigma = 0`$, $`G = 0`$), continuity on $`[0, 1]`$, and monotonicity | `LimitingCases.lean` | `mixtureProb`, `mixtureProb_mono`, `tendsto_expectedSuccProb_as_sigma_one`, `tendsto_expectedSuccProb_as_sigma_zero`, `noisyTrajectory_succProb_at_sigma_one`, `noisyTrajectory_succProb_at_sigma_zero`, `noisyTrajectory_succProb_nil`, `continuousOn_noisyTrajectory_succProb`, `tendsto_noisyTrajectory_succProb_sigma_one`, `tendsto_noisyTrajectory_succProb_sigma_zero` |

---

## §1 — Complex Quantum States, Born-Rule `POVM` Measurement, and the $`\mathbb{C}^{2^n} \cong \mathbb{R}^{2 \cdot 2^n}`$ Isomorphism

### Geometric Motivation

An $`n`$-qubit pure quantum state $`|\psi\rangle`$ lives in the $`N`$-dimensional complex Hilbert space $`\mathbb{C}^N`$ ($`N = 2^n`$) subject to the unit-norm constraint $`\langle \psi | \psi \rangle = 1`$. Why translate this complex state space into a real Euclidean space of twice the dimension, $`d = 2N = 2^{n+1}`$?

In the isotropic pure-state error model [[Lacalle & Pozo Coronado (2019)](#references)], a gate perturbation has **no preferred axis** in state space: it rotates the state vector uniformly across all real directions orthogonal to the current state, mixing real and imaginary amplitude components on an equal footing. Viewing $`\mathbb{C}^N`$ as $`\mathbb{R}^{2N}`$ turns:
- normalized quantum states $`|\psi\rangle \in \mathbb{C}^N`$ into points on the $`(d - 1)`$-dimensional Euclidean unit sphere $`S^{d-1} \subset \mathbb{R}^d`$,
- $`n`$-qubit unitary gates $`U \in \mathrm{U}(N)`$ into real linear isometries in $`\mathrm{O}(d)`$, and
- computational-basis Born-rule probabilities $`|\langle w | \psi \rangle|^2`$ into the sum of squares of **two orthogonal real coordinates**, corresponding to a rank-2 orthogonal projection on $`\mathbb{R}^d`$.

It is precisely the mismatch between the $`d = 2N`$ real coordinates mixed by isotropic sphere noise and the $`2`$ real coordinates summed by a complex basis measurement that produces the universal $`\frac{2}{d} = \frac{1}{N}`$ uniform guessing floor.

### Explicit Realification Bijection

Write a complex amplitude vector $`v \in \mathbb{C}^N`$ (`Fin (2 ^ n) → ℂ`) in terms of the real and imaginary parts of each computational-basis amplitude $`v_x = \alpha_{2x} + i\,\alpha_{2x+1}`$ for $`x \in \{0, 1, \dots, N - 1\}`$:

$$
\mathbf{v} = \bigl(\operatorname{Re} v_0,\thinspace \operatorname{Im} v_0,\thinspace \operatorname{Re} v_1,\thinspace \operatorname{Im} v_1,\thinspace \dots,\thinspace \operatorname{Re} v_{N-1},\thinspace \operatorname{Im} v_{N-1}\bigr) \in \mathbb{R}^d, \qquad d = 2N = 2 \cdot 2^n.
$$

In `IsotropicGroverProof/Defs.lean`, we define:
- `d (n : ℕ) : ℕ := 2 * 2 ^ n` (satisfying $`d(n) \ge 2`$ for every $`n \in \mathbb{N}`$ via `two_le_d`, including the 0-qubit edge case $`n = 0 \implies d = 2`$),
- the ambient real inner-product space `E (n : ℕ) := EuclideanSpace ℝ (Fin (d n))` and its unit sphere `unitSphere (n : ℕ) := Metric.sphere (0 : E n) 1`, and
- standard orthonormal basis vectors $`\hat{\mathbf{e}}_i`$ (`stdBasisVec n i`) for $`i \in \mathrm{Fin}(d(n))`$.

For each basis outcome $`w \in \mathrm{Fin}(2^n)`$, we pair the even and odd coordinate indices `succProbIdx0 n w` ($`i_0(w)`$) and `succProbIdx1 n w` ($`i_1(w)`$):

$$
i_0(w) = 2w \quad (\text{real part}), \qquad i_1(w) = 2w + 1 \quad (\text{imaginary part}),
$$

which are individually injective (`succProbIdx0_inj`, `succProbIdx1_inj`) and globally disjoint (`succProbIdx0_ne_succProbIdx1`: $`2x \ne 2y + 1`$ for all $`x, y`$).

In `IsotropicGroverProof/QuantumChannel.lean`, the coordinate maps `vecToReal` and `realToVec` implement this $`\mathbb{R}`$-linear bijection (`realToVec_vecToReal`, `vecToReal_realToVec`, `vecToReal_add`, `vecToReal_smul`). Because $`|v_x|^2 = (\operatorname{Re} v_x)^2 + (\operatorname{Im} v_x)^2`$, Euclidean squared norm is preserved identically (`norm_sq_vecToReal`, `sum_norm_sq_realToVec`):

$$
\lVert\operatorname{vecToReal}(v)\rVert_{\mathbb{R}^d}^2 = \sum_{i=0}^{d-1} \alpha_i^2 = \sum_{x=0}^{N-1} \bigl(\alpha_{2x}^2 + \alpha_{2x+1}^2\bigr) = \sum_{x=0}^{N-1} |v_x|^2.
$$

Restricting to normalized `QuantumInfo` kets `ψ : Ket (Fin (2 ^ n))` (satisfying $`\sum_x |\psi_x|^2 = 1`$) gives a bijection `ketToReal` between complex pure states and the real unit sphere $`S^{d-1}`$ (with unit-norm property `norm_ketToReal`):

$$
\operatorname{ketToReal} : \mathrm{Ket}(\mathrm{Fin}(2^n)) \longrightarrow S^{d-1} \subset E(n), \qquad \lVert\operatorname{ketToReal}(\psi)\rVert = 1,
$$

with two-sided inverse `realToKet` (`realToKet_ketToReal`, `ketToReal_realToKet`).

### Unitary Gates as Real Linear Isometries

Every $`n`$-qubit unitary matrix $`U \in \mathrm{U}(N)`$ (`U : 𝐔[Fin (2 ^ n)]`) preserves the $`\ell^2(\mathbb{C}^N)`$ norm $`\sum_x |(Uv)_x|^2 = \sum_x |v_x|^2`$. Conjugating complex matrix-vector multiplication by `vecToReal` and `realToVec` therefore lifts $`U`$ to an invertible real linear isometry `unitaryToRealIso U : E n ≃ₗᵢ[ℝ] E n` in $`\mathrm{O}(d)`$:

$$
\widetilde{U} \in \mathrm{O}(d), \qquad \widetilde{U}(\Phi) = \operatorname{vecToReal}\bigl(U \cdot \operatorname{realToVec}(\Phi)\bigr),
$$

with inverse $`\widetilde{U}^{-1}(\Phi) = \operatorname{vecToReal}\bigl(U^\dagger \cdot \operatorname{realToVec}(\Phi)\bigr)`$ and equivariance `ketToReal (applyUnitaryKet U ψ) = unitaryToRealIso U (ketToReal ψ)` (`ketToReal_applyUnitaryKet`). Geometrically, $`\mathrm{U}(N)`$ embeds into $`\mathrm{O}(2N)`$ as the subgroup of orthogonal transformations commuting with multiplication by $`i`$, i.e., the skew-symmetric block operator $`J(\alpha_{2x}, \alpha_{2x+1}) = (-\alpha_{2x+1}, \alpha_{2x})`$, whereas our real-sphere geometric theorems hold for *all* linear isometries in $`\mathrm{O}(2N)`$.

### Born-Rule Probability and `POVM` Equivalence

For any real vector $`\mathbf{v} \in \mathbb{R}^d`$ and target outcome $`w \in \mathrm{Fin}(2^n)`$, `Defs.lean` defines the measurement functional `succProb n v w` as the sum of squared projections onto the $`2w`$ and $`2w+1`$ coordinate axes:

$$
\operatorname{succProb}(n, \mathbf{v}, w) := \langle \mathbf{v}, \hat{\mathbf{e}}_{2w}\rangle_{\mathbb{R}}^2 + \langle \mathbf{v}, \hat{\mathbf{e}}_{2w+1}\rangle_{\mathbb{R}}^2 = v_{2w}^2 + v_{2w+1}^2.
$$

Reindexing $`\mathrm{Fin}(2^n) \times \mathrm{Fin}(2) \simeq \mathrm{Fin}(d(n))`$ proves Parseval's identity $`\sum_{w} \operatorname{succProb}(n, \mathbf{v}, w) = \|\mathbf{v}\|^2`$ (`sum_succProb_eq_norm_sq`), so $`\{\operatorname{succProb}(n, \Phi, w)\}_{w=0}^{N-1}`$ is a valid probability distribution whenever $`\|\Phi\| = 1`$.

To ensure complete compatibility with standard quantum information theory, `QuantumChannel.lean` packages the computational-basis projectors $`|w\rangle\langle w|`$ (`compProjObs w` from `QuantumComputation`) into a `QuantumInfo` positive operator-valued measure `computationalPOVM n : POVM (Fin (2 ^ n)) (Fin (2 ^ n))`. Theorem `succProb_ketToReal_eq_born` establishes that for every normalized ket $`|\psi\rangle`$, all five representations of the Born rule are mathematically and algebraically identical:

```math
\begin{aligned}
\operatorname{succProb}\bigl(n,\, \operatorname{ketToReal}(\psi),\, w\bigr)
&= |\psi_w|^2 \\[4pt]
&= \operatorname{Re}\bigl((|\psi\rangle\langle\psi|)_{w,w}\bigr) \\[4pt]
&= \operatorname{Tr}\bigl(|\psi\rangle\langle\psi|\, |w\rangle\langle w|\bigr) \\[4pt]
&= \mu_{\mathrm{computationalPOVM}(n)}\bigl(|\psi\rangle\langle\psi|\bigr)(w),
\end{aligned}
```

corresponding in Lean to `‖ψ w‖ ^ 2`, `((MState.pure ψ).m w w).re`, `(MState.pure ψ).exp_val (compProjObs w).1`, and `((computationalPOVM n).measure (MState.pure ψ) w : ℝ)`.

---

## §2 — Microscopic Single-Gate Isotropic Error Model Across $`\sigma \in [0, 1]`$

### Polar Decomposition of an Isotropic Sphere Perturbation

Suppose a gate produces the unit vector $`\Psi \in S^{d-1} \subset \mathbb{R}^d`$. A single **isotropic pure-state gate error** with fidelity parameter $`\sigma \in [0, 1]`$ perturbs $`\Psi`$ to a random unit vector (`isotropicError Ψ e₂ θ` in `IsotropicError.lean`):

$$
\Psi' = \cos\theta\thinspace\Psi + \sin\theta\thinspace\mathbf{e}_2,
$$

driven by two **independent** random variables:

**1. Equatorial direction $`\mathbf{e}_2 \in S(V_\perp(\Psi))`$:** Drawn uniformly from the $`(d - 2)`$-dimensional unit sphere of the orthogonal complement

$$
V_\perp(\Psi) = \lbrace\mathbf{v} \in \mathbb{R}^d : \langle \Psi, \mathbf{v}\rangle_{\mathbb{R}} = 0\rbrace, \qquad \dim_{\mathbb{R}} V_\perp(\Psi) = d - 1 \ge 1.
$$

In `CrossTerm.lean`, `perpSphereMeasure Ψ` constructs this probability measure rigorously without coordinate charts: it equips the subspace `V_perp Ψ` with the additive Haar measure `V_perp_haar Ψ` (private helper in `CrossTerm.lean`) induced by an orthonormal basis (`stdOrthonormalBasis`), restricts it radially to the unit sphere via Mathlib's `.toSphere` construction, normalizes by total finite nonzero mass, and pushes forward into the ambient space `E n` (`perpSphereMeasure_isProbMeasure`). Almost every $`\mathbf{e}_2`$ satisfies $`\mathbf{e}_2 \in V_\perp(\Psi)`$ and $`\|\mathbf{e}_2\| = 1`$ (`perpSphereMeasure_norm_ae`), whence $`\|\Psi'\|^2 = \cos^2\theta\,\|\Psi\|^2 + \sin^2\theta\,\|\mathbf{e}_2\|^2 = 1`$ (`isotropicError_norm`).

**2. Polar rotation angle $`\theta \in [0, \pi]`$:** Drawn from the 1D polar-angle marginal `poissonAngleMeasure d σ` of the spherical Poisson kernel on $`S^{d-1}`$.

Geometrically, $`\Psi'`$ is obtained by moving distance $`\theta`$ along a uniformly random geodesic (great circle) issuing from $`\Psi`$ on $`S^{d-1}`$. Because the distribution of $`\mathbf{e}_2`$ is invariant under all orthogonal transformations fixing $`\Psi`$, no tangent direction is favored — hence the name *isotropic*.

### Poisson Kernel Origin and Behavior Across All $`\sigma \in [0, 1]`$

On the open Euclidean unit ball $`B^d = \{\mathbf{y} \in \mathbb{R}^d : \|\mathbf{y}\| < 1\}`$ with boundary $`S^{d-1}`$, the **Poisson kernel** [[Axler, Bourdon & Ramey (2001)](#references), Ch. 5] is

$$
P(\mathbf{y}, \xi) = \frac{1 - \lVert\mathbf{y}\rVert^2}{\lVert\mathbf{y} - \xi\rVert^d}, \qquad \mathbf{y} \in B^d,\mspace{5mu} \xi \in S^{d-1}.
$$

Physically, if a standard $`d`$-dimensional Brownian particle starts at interior point $`\mathbf{y} = \sigma\Psi \in B^d`$ ($`\sigma \in [0, 1)`$) and diffuses until first hitting the boundary sphere $`S^{d-1}`$, the hitting location $`\xi \in S^{d-1}`$ has probability density proportional to $`P(\sigma\Psi, \xi)`$ with respect to uniform surface measure on $`S^{d-1}`$. Writing $`\cos\theta = \langle \Psi, \xi\rangle_{\mathbb{R}}`$ with $`\theta \in [0, \pi]`$, the squared chordal distance depends solely on $`\theta`$:

$$
\lVert\sigma\Psi - \xi\rVert^2 = \lVert\sigma\Psi\rVert^2 + \lVert\xi\rVert^2 - 2\sigma\langle \Psi, \xi\rangle_{\mathbb{R}} = 1 + \sigma^2 - 2\sigma\cos\theta =: D(\sigma, \theta).
$$

Integrating over the $`(d - 2)`$-dimensional latitude sphere $`\{\xi \in S^{d-1} : \langle \Psi, \xi\rangle = \cos\theta\}`$ of radius $`\sin\theta`$ multiplies $`P(\sigma\Psi, \xi)`$ by the latitude surface area factor $`\propto \sin^{d-2}\theta\,d\theta`$, yielding the unnormalized polar density (`poissonKernelDensity d σ θ` in `IsotropicError.lean`):

$$
g_d(\theta; \sigma) := \frac{(1 - \sigma^2)\sin^{d-2}\theta}{(1 + \sigma^2 - 2\sigma\cos\theta)^{d/2}}, \qquad \theta \in [0, \pi].
$$

Let $`Z_d(\sigma) := \int_0^\pi g_d(\theta; \sigma)\,d\theta`$ (`poissonNormConst d σ`). For every $`\sigma \in [0, 1)`$ and $`d \ge 2`$, $`D(\sigma, \theta) = (1 - \sigma)^2 + 2\sigma(1 - \cos\theta) \ge (1 - \sigma)^2 > 0`$, so $`g_d(\cdot; \sigma)`$ is continuous, non-negative on $`[0, \pi]`$, and strictly positive at $`\theta = \pi/2`$ ($`g_d(\pi/2; \sigma) = (1 - \sigma^2)/(1 + \sigma^2)^{d/2} > 0`$). Thus $`Z_d(\sigma) > 0`$ (`poissonNormConst_pos_Ico`), and normalizing on $`[0, \pi]`$ defines the probability measure `poissonMarginal d σ` (`poissonMarginal_isProbMeasure_Ico`).

To cover the **entire closed interval** $`\sigma \in [0, 1]`$ uniformly without ad-hoc limiting arguments downstream, `IsotropicError.lean` defines `poissonAngleMeasure d σ`:

```math
\nu_{d,\sigma} := \operatorname{poissonAngleMeasure}(d, \sigma) := \begin{cases}
\delta_0 & \text{if } \sigma = 1, \\[4pt]
\operatorname{poissonMarginal}(d, \sigma) & \text{if } \sigma \in [0, 1),
\end{cases}
```

which is a valid probability measure for all $`\sigma \in [0, 1]`$ and $`d \ge 2`$ (`poissonAngleMeasure_isProbMeasure`). Across the three regimes of $`[0, 1]`$, $`\nu_{d,\sigma}`$ behaves as follows:

**1. Noisy interior $`\sigma \in (0, 1)`$:** $`\nu_{d,\sigma}`$ has smooth positive density $`g_d(\theta; \sigma)/Z_d(\sigma)`$ on $`(0, \pi)`$. As $`\sigma \uparrow 1`$, the denominator $`D(\sigma, 0) = (1 - \sigma)^2`$ creates a sharp peak at $`\theta = 0`$, concentrating the perturbed state $`\Psi'`$ tightly around $`\Psi`$.

**2. Complete decoherence $`\sigma = 0`$:** Substituting $`\sigma = 0`$ directly into $`g_d(\theta; \sigma)`$ gives $`D(0, \theta) = 1`$ and $`1 - \sigma^2 = 1`$, so

$$
g_d(\theta; 0) = \sin^{d-2}\theta.
$$

Normalizing $`\sin^{d-2}\theta\,d\theta`$ on $`[0, \pi]`$ gives the exact polar-angle marginal of the **uniform Haar probability measure on $`S^{d-1}`$**! Together with $`\mathbf{e}_2 \sim \mu_\perp(\Psi)`$ independent of $`\theta`$, $`\Psi'`$ is distributed uniformly over the entire unit sphere $`S^{d-1}`$, retaining zero memory of $`\Psi`$.

**3. Noiseless gate $`\sigma = 1`$:** At $`\sigma = 1`$, the factor $`1 - \sigma^2 = 0`$ causes the Lebesgue density $`g_d(\theta; 1)`$ to vanish for $`\theta \in (0, \pi]`$ while the Poisson kernel converges weakly to the Dirac mass $`\delta_0`$. Defining $`\nu_{d,1} = \delta_0`$ (`Measure.dirac 0`) sets $`\theta = 0`$ almost surely, so $`\Psi' = \cos 0\,\Psi + \sin 0\,\mathbf{e}_2 = \Psi`$.

---

## §3 — Exact First and Second Moments of the Poisson Marginal

Everything in the noisy circuit calculation hinges on two exact moments of $`\theta \sim \nu_{d,\sigma}`$ for $`d \ge 2`$ and $`\sigma \in [0, 1]`$:

$$
\mathrm{E}[\cos\theta] = \sigma, \qquad \mathrm{E}[\cos^2\theta] = \frac{(d - 1)\sigma^2 + 1}{d}.
$$

Notice that $`\mathrm{E}[\cos^2\theta] \ne (\mathrm{E}[\cos\theta])^2 = \sigma^2`$: their difference $`\operatorname{Var}(\cos\theta) = \frac{1 - \sigma^2}{d} > 0`$ (for $`\sigma < 1`$) reflects the irreducible geometric spread of an isotropic perturbation across $`d`$ real dimensions. We present both the **geometric harmonic-extension derivation** (which explains *why* these formulas have this exact form) and the **self-contained 1D Fundamental Theorem of Calculus proof** formalized in `IsotropicError.lean` (which proves them for all $`d \ge 2`$ and $`\sigma \in [0, 1]`$ with zero multivariable PDE axioms).

### Part A — Geometric Derivation via Harmonic Polynomial Extension on $`B^d`$

By the **Poisson integral representation theorem** on the Euclidean unit ball [[Axler, Bourdon & Ramey (2001)](#references), Ch. 5, Thms. 5.5 & 5.14], if $`H : \overline{B}^d \to \mathbb{R}`$ is continuous on the closed ball $`\overline{B}^d`$ and harmonic on the interior ($`\Delta H = \sum_{j=1}^d \frac{\partial^2 H}{\partial x_j^2} = 0`$ on $`B^d`$), then for every interior point $`\mathbf{x} \in B^d`$, the Poisson-kernel expectation of its boundary restriction $`h = H|_{S^{d-1}}`$ equals $`H(\mathbf{x})`$:

$$
\mathrm{E}_{\xi \sim P(\mathbf{x}, \cdot)}[h(\xi)] = H(\mathbf{x}).
$$

Choosing $`\mathbf{x} = \sigma\Psi`$ ($`\sigma \in [0, 1)`$, $`\|\Psi\| = 1`$) gives $`\langle \xi, \Psi\rangle_{\mathbb{R}} = \cos\theta`$:

**1. First moment $`\mathrm{E}[\cos\theta] = \sigma`$:** Take boundary data $`h_1(\xi) = \langle \xi, \Psi\rangle_{\mathbb{R}} = \cos\theta`$. The linear polynomial $`H_1(\mathbf{x}) = \langle \mathbf{x}, \Psi\rangle_{\mathbb{R}}`$ already agrees with $`h_1`$ on $`S^{d-1}`$ and has vanishing second derivatives ($`\Delta H_1 = 0`$). Evaluating at $`\mathbf{x} = \sigma\Psi`$ gives

$$
\mathrm{E}[\cos\theta] = H_1(\sigma\Psi) = \langle \sigma\Psi, \Psi\rangle_{\mathbb{R}} = \sigma\lVert\Psi\rVert^2 = \sigma.
$$

Thus $`\sigma`$ is physically the **mean amplitude overlap** $`\mathrm{E}[\langle \Psi', \Psi\rangle_{\mathbb{R}}]`$ between the perturbed and ideal states.

**2. Second moment $`\mathrm{E}[\cos^2\theta] = \frac{(d - 1)\sigma^2 + 1}{d}`$:** Take quadratic boundary data $`h_2(\xi) = \langle \xi, \Psi\rangle_{\mathbb{R}}^2 = \cos^2\theta`$. The naive extension $`\langle \mathbf{x}, \Psi\rangle_{\mathbb{R}}^2`$ is *not* harmonic because

$$
\Delta\bigl(\langle \mathbf{x}, \Psi\rangle_{\mathbb{R}}^2\bigr) = \sum_{j=1}^d \frac{\partial^2}{\partial x_j^2}\left(\sum_{k=1}^d x_k \Psi_k\right)^2 = \sum_{j=1}^d 2\Psi_j^2 = 2\lVert\Psi\rVert^2 = 2.
$$

To cancel this constant Laplacian without changing values on the unit sphere $`S^{d-1}`$ (where $`\|\xi\|^2 = 1`$), subtract $`\frac{\|\mathbf{x}\|^2}{d}`$ — whose Laplacian is $`\Delta\bigl(\|\mathbf{x}\|^2/d\bigr) = \frac{2d}{d} = 2`$ — and add back the constant $`\frac{1}{d}`$:

$$
H_2(\mathbf{x}) := \langle \mathbf{x}, \Psi\rangle_{\mathbb{R}}^2 - \frac{\lVert\mathbf{x}\rVert^2}{d} + \frac{1}{d}.
$$

- *Harmonicity on $`B^d`$:* $`\Delta H_2(\mathbf{x}) = 2 - \frac{2d}{d} + 0 = 0`$ (`laplacian_trace_cancellation` in `Gegenbauer.lean`).
- *Boundary agreement on $`S^{d-1}`$:* When $`\|\xi\| = 1`$, $`H_2(\xi) = \langle \xi, \Psi\rangle_{\mathbb{R}}^2 - \frac{1}{d} + \frac{1}{d} = \langle \xi, \Psi\rangle_{\mathbb{R}}^2`$ (`harmonicExtension_boundary`).
- *Interior radial evaluation at $`\mathbf{x} = \sigma\Psi`$:* Since $`\langle \sigma\Psi, \Psi\rangle_{\mathbb{R}} = \sigma`$ and $`\|\sigma\Psi\|^2 = \sigma^2`$, theorem `harmonicExtension_eval` gives:

$$
\mathrm{E}[\cos^2\theta] = H_2(\sigma\Psi) = \sigma^2 - \frac{\sigma^2}{d} + \frac{1}{d} = \frac{(d - 1)\sigma^2 + 1}{d},
$$

which evaluates to $`1`$ at $`\sigma = 1`$ (`poissonIntegral_val_sigma_one`) and to $`\frac{1}{d}`$ at $`\sigma = 0`$ (`poissonIntegral_val_sigma_zero`).

### Part B — Self-Contained 1D Calculus & Two-Step Induction Proof in Lean

Mathlib `v4.35.0` provides the 2D complex-disc Poisson integral (`Mathlib.Analysis.Complex.Poisson`), whereas formalizing $`d`$-dimensional spherical surface-measure disintegration and the multivariable Dirichlet problem on $`B^d`$ would require substantial PDE infrastructure. Instead, `IsotropicError.lean` proves both moment formulas **directly from 1D calculus on $`[0, \pi]`$** for all $`d \ge 2`$ and $`\sigma \in [0, 1)`$, using four smooth global antiderivatives and a parity-preserving two-step induction $`d \mapsto d + 2`$ anchored at $`d = 2`$ and $`d = 3`$.

For fixed $`\sigma \in [0, 1)`$ and $`d \ge 2`$, recall $`D(\sigma, \theta) = 1 + \sigma^2 - 2\sigma\cos\theta > 0`$ with derivative $`\frac{\partial}{\partial\theta}D(\sigma, \theta) = 2\sigma\sin\theta`$, and define the unnormalized moments

$$
I_k(d) := \int_0^\pi g_d(\theta; \sigma)\cos^k\theta\thinspace d\theta \qquad (k = 0, 1, 2), \qquad g_d(\theta; \sigma) = (1 - \sigma^2)\sin^{d-2}\theta\thinspace D(\sigma, \theta)^{-d/2}.
$$

Observe the fundamental algebraic dimension-shift relation:

$$
g_{d+2}(\theta; \sigma)\thinspace D(\sigma, \theta) = g_d(\theta; \sigma)\thinspace\sin^2\theta = g_d(\theta; \sigma)\thinspace(1 - \cos^2\theta).
$$

#### Step 1: Three Global Antiderivatives Relating $`d`$ and $`d + 2`$

In `IsotropicError.lean`, we construct three globally $`C^1`$ functions on $`\mathbb{R}`$ that vanish identically at both endpoints $`\theta = 0`$ and $`\theta = \pi`$ (since $`d \ge 2 \implies d - 1 \ge 1`$, so $`\sin^{d-1} 0 = \sin^{d-1}\pi = 0`$):

**1. Normalization shift antiderivative $`\tilde{G}_0`$** (`antiderivG0`, private helper in `IsotropicError.lean`):

$$
\tilde{G}_0(\theta) := (1 - \sigma^2)\sin^{d-1}\theta\thinspace D(\sigma, \theta)^{-d/2} = g_d(\theta; \sigma)\sin\theta.
$$

Differentiating by the product and chain rules gives

```math
\begin{aligned}
\tilde{G}_0'(\theta)
&= (1 - \sigma^2)\Bigl[(d - 1)\sin^{d-2}\theta\cos\theta\,D^{-d/2} + \sin^{d-1}\theta\left(-\frac{d}{2}\right)D^{-d/2 - 1}(2\sigma\sin\theta)\Bigr] \\[4pt]
&= (d - 1)\,g_d(\theta; \sigma)\cos\theta - d\sigma\,g_{d+2}(\theta; \sigma).
\end{aligned}
```

Since $`\tilde{G}_0(\pi) = \tilde{G}_0(0) = 0`$, the 1D Fundamental Theorem of Calculus on $`[0, \pi]`$ gives **Identity (I)**:

$$
d\sigma\thinspace I_0(d + 2) = (d - 1)\thinspace I_1(d).
$$

**2. Three-term moment antiderivative $`\tilde{F}_0`$** (`antiderivF0`, private helper in `IsotropicError.lean`):

$$
\tilde{F}_0(\theta) := D(\sigma, \theta)\thinspace\tilde{G}_0(\theta) = (1 - \sigma^2)\sin^{d-1}\theta\thinspace D(\sigma, \theta)^{1 - d/2}.
$$

Applying the product rule $`\tilde{F}_0' = D'\tilde{G}_0 + D\tilde{G}_0'`$ and using $`g_{d+2}\,D = g_d\sin^2\theta`$ together with $`D = 1 + \sigma^2 - 2\sigma\cos\theta`$ and $`\sin^2\theta = 1 - \cos^2\theta`$:

```math
\begin{aligned}
\tilde{F}_0'(\theta)
&= 2\sigma\sin^2\theta\,g_d + \bigl(1 + \sigma^2 - 2\sigma\cos\theta\bigr)(d - 1)g_d\cos\theta - d\sigma\sin^2\theta\,g_d \\[4pt]
&= (d - 1)(1 + \sigma^2)\,g_d\cos\theta - 2(d - 1)\sigma\,g_d\cos^2\theta - (d - 2)\sigma\,g_d(1 - \cos^2\theta) \\[4pt]
&= (d - 1)(1 + \sigma^2)\,g_d(\theta; \sigma)\cos\theta - d\sigma\,g_d(\theta; \sigma)\cos^2\theta - (d - 2)\sigma\,g_d(\theta; \sigma).
\end{aligned}
```

Since $`\tilde{F}_0(\pi) = \tilde{F}_0(0) = 0`$, 1D FTC gives the **Three-Term Recurrence — Identity (II)**:

$$
d\sigma\thinspace I_2(d) = (d - 1)(1 + \sigma^2)\thinspace I_1(d) - (d - 2)\sigma\thinspace I_0(d).
$$

**3. Cosine shift antiderivative $`\tilde{G}_1`$** (`antiderivG1`, private helper in `IsotropicError.lean`):

$$
\tilde{G}_1(\theta) := \cos\theta\thinspace\tilde{G}_0(\theta) = g_d(\theta; \sigma)\sin\theta\cos\theta.
$$

Differentiating gives $`\tilde{G}_1' = -\sin\theta\,\tilde{G}_0 + \cos\theta\,\tilde{G}_0' = -g_d(1 - \cos^2\theta) + (d - 1)g_d\cos^2\theta - d\sigma\,g_{d+2}\cos\theta = d\,g_d\cos^2\theta - g_d - d\sigma\,g_{d+2}\cos\theta`$. Since $`\tilde{G}_1(\pi) = \tilde{G}_1(0) = 0`$, 1D FTC gives **Identity (III)**:

$$
d\sigma\thinspace I_1(d + 2) = d\thinspace I_2(d) - I_0(d).
$$

#### Step 2: Two-Step Induction $`d \mapsto d + 2`$ and Base Cases $`d = 2, 3`$

First consider $`\sigma \in (0, 1)`$. Suppose $`I_1(d) = \sigma\,I_0(d)`$ holds at dimension $`d`$. Forming the linear combination $`\sigma \cdot \text{(III)} + \text{(II)} - \sigma^2 \cdot \text{(I)}`$ and substituting $`I_1(d) = \sigma\,I_0(d)`$ gives:

```math
\begin{aligned}
d\sigma^2\,I_1(d + 2) - d\sigma^3\,I_0(d + 2)
&= \bigl[d\sigma\,I_2(d) - \sigma\,I_0(d)\bigr] - (d - 1)\sigma^2\,I_1(d) \\[4pt]
&= \bigl[(d - 1)(1 + \sigma^2)\sigma - (d - 2)\sigma - \sigma - (d - 1)\sigma^3\bigr] I_0(d) = 0.
\end{aligned}
```

Since $`d\sigma^2 \ne 0`$, cancelling $`d\sigma^2`$ yields $`I_1(d + 2) = \sigma\,I_0(d + 2)`$! Thus the first-moment relation propagates across all even dimensions $`2 \to 4 \to 6 \to \cdots`$ and all odd dimensions $`3 \to 5 \to 7 \to \cdots`$ once anchored at $`d = 2`$ and $`d = 3`$:

**Even base case $`d = 2`$:** Here $`\sin^{2-2}\theta = 1`$, so $`g_2(\theta; \sigma) = \frac{1 - \sigma^2}{1 + \sigma^2 - 2\sigma\cos\theta}`$ equals Mathlib's complex-disc Poisson kernel `poissonKernel (0 : ℂ) (σ : ℂ) (Complex.exp (↑θ * Complex.I))`. Applying Mathlib's `DiffContOnCl.circleAverage_poissonKernel_smul` on the unit disc to the holomorphic functions $`f(z) = 1`$ and $`f(z) = z`$ at $`z = \sigma \in B^2(0, 1)`$, taking real parts, and folding $`[0, 2\pi]`$ onto $`[0, \pi]`$ by reflection symmetry $`\cos(2\pi - \theta) = \cos\theta`$ gives $`I_0(2) = \pi`$ and $`I_1(2) = \pi\sigma = \sigma\,I_0(2)`$.

**Odd base case $`d = 3`$ via elementary antiderivative $`\tilde{H}_3`$** (`antiderivH3`, private helper in `IsotropicError.lean`): At $`d = 3`$, $`g_3(\theta; \sigma) = (1 - \sigma^2)\sin\theta\,D(\sigma, \theta)^{-3/2}`$ contains a single factor of $`\sin\theta = \frac{1}{2\sigma}D'(\sigma, \theta)`$, making the integrand completely elementary via $`u = D(\sigma, \theta)`$ and $`\cos\theta = \frac{1 + \sigma^2 - D}{2\sigma}`$. Explicitly, define:

$$
\tilde{H}_3(\theta) := -\frac{1 - \sigma^2}{2\sigma^2}\Bigl((1 - \sigma^2)\thinspace D(\sigma, \theta)^{-1/2} + D(\sigma, \theta)^{1/2}\Bigr).
$$

Differentiating with respect to $`\theta`$ gives

$$
\tilde{H}_3'(\theta) = -\frac{1 - \sigma^2}{2\sigma^2}\left(-\frac{1 - \sigma^2}{2}D^{-3/2} + \frac{1}{2}D^{-1/2}\right)(2\sigma\sin\theta) = g_3(\theta; \sigma)\thinspace\frac{(1 - \sigma^2) - D(\sigma, \theta)}{2\sigma} = g_3(\theta; \sigma)(\cos\theta - \sigma).
$$

Why does $`\tilde{H}_3(\pi) = \tilde{H}_3(0)`$? Because for $`\sigma \in (0, 1)`$, both $`1 - \sigma > 0`$ and $`1 + \sigma > 0`$, so $`\sqrt{D(\sigma, 0)} = \sqrt{(1 - \sigma)^2} = 1 - \sigma`$ and $`\sqrt{D(\sigma, \pi)} = \sqrt{(1 + \sigma)^2} = 1 + \sigma`$. Evaluating the parenthesized factor at both endpoints swaps $`1 - \sigma`$ and $`1 + \sigma`$:

```math
\begin{aligned}
\text{at } \theta = 0:&\quad \frac{1 - \sigma^2}{1 - \sigma} + (1 - \sigma) = (1 + \sigma) + (1 - \sigma) = 2, \\[4pt]
\text{at } \theta = \pi:&\quad \frac{1 - \sigma^2}{1 + \sigma} + (1 + \sigma) = (1 - \sigma) + (1 + \sigma) = 2.
\end{aligned}
```

Therefore $`\tilde{H}_3(\pi) = \tilde{H}_3(0) = -\frac{1 - \sigma^2}{\sigma^2}`$, and 1D FTC gives $`I_1(3) - \sigma\,I_0(3) = \tilde{H}_3(\pi) - \tilde{H}_3(0) = 0`$!

By two-step pattern-matching induction on $`d \ge 2`$, `halfcircle_cos_eq` establishes $`I_1(d) = \sigma\,I_0(d)`$ for all $`d \ge 2`$ and $`\sigma \in (0, 1)`$. Substituting $`I_1(d) = \sigma\,I_0(d)`$ back into the Three-Term Recurrence **Identity (II)** and cancelling $`\sigma \ne 0`$ immediately yields the unnormalized second moment (`halfcircle_cos_sq_eq`):

$$
d\sigma\thinspace I_2(d) = \bigl[(d - 1)(1 + \sigma^2)\sigma - (d - 2)\sigma\bigr] I_0(d) = \sigma\bigl((d - 1)\sigma^2 + 1\bigr)I_0(d) \implies I_2(d) = \frac{(d - 1)\sigma^2 + 1}{d}\thinspace I_0(d).
$$

#### Step 3: Endpoints $`\sigma = 0`$ and $`\sigma = 1`$

- **At $`\sigma = 0`$:** Identities (I) and (III) were proved on the half-open interval $`\sigma \in [0, 1)`$! Setting $`\sigma = 0`$ directly in Identity (I) gives $`0 = (d - 1)I_1(d) \implies I_1(d) = 0 = 0 \cdot I_0(d)`$ (`halfcircle_cos_eq_Ico`), and setting $`\sigma = 0`$ in Identity (III) gives $`0 = d\,I_2(d) - I_0(d) \implies I_2(d) = \frac{1}{d}\,I_0(d) = \frac{(d - 1)\cdot 0^2 + 1}{d}\,I_0(d)`$ (`halfcircle_cos_sq_eq_Ico`). Dividing by $`Z_d(\sigma) = I_0(d) > 0`$ proves `poissonMarginal_mean_cos_Ico` and `poissonMarginal_cos_sq_Ico` on $`[0, 1)`$ (as well as `poissonMarginal_mean_cos` and `poissonIntegral_cos_sq` on $`(0, 1)`$, and the effective-parameter corollary $`f_2 = \mathrm{E}[\cos^2\theta_G] = \frac{(d - 1)\sigma^{2G} + 1}{d}`$ in `f₂_formula` for `composedMeasure d G σ := poissonMarginal d (σ ^ G)`).
- **At $`\sigma = 1`$:** Under $`\nu_{d,1} = \delta_0`$, $`\int \cos\theta\,d\delta_0 = \cos 0 = 1`$ and $`\int \cos^2\theta\,d\delta_0 = \cos^2 0 = 1 = \frac{(d - 1)\cdot 1^2 + 1}{d}`$, completing `poissonAngleMeasure_mean_cos` and `poissonAngleMeasure_cos_sq` for **all** $`\sigma \in [0, 1]`$ and $`d \ge 2`$.

---

## §4 — Equatorial Sphere Symmetry and the Full Real Bilinear Second-Moment Operator

### Why Work at the Bilinear Operator Level?

A naive calculation expands only the single-outcome probability $`\operatorname{succProb}(n, \Psi', w) = (\Psi'_{2w})^2 + (\Psi'_{2w+1})^2`$. However, computing the expectation of the **general real bilinear form** $`\langle \Psi', \mathbf{u}\rangle_{\mathbb{R}}\langle \Psi', \mathbf{v}\rangle_{\mathbb{R}}`$ for *arbitrary* vectors $`\mathbf{u}, \mathbf{v} \in \mathbb{R}^d`$ is no harder and buys three major payoffs at once:
1. It exposes why the dimension factor $`d - 1`$ cancels **already in a single gate step**, independent of the basis or observable.
2. It determines all off-diagonal entries of the complex density matrix $`|\psi'\rangle\langle\psi'|`$ in §5.
3. It closes the $`G`$-gate Markov induction in §6 in a single step by pulling $`\mathbf{u}, \mathbf{v}`$ back along the adjoint of the remaining ideal gates.

### Step 1: Antipodal Symmetry Kills the Linear Cross-Terms

For any unit vector $`\Psi \in S^{d-1}`$ and arbitrary $`\mathbf{u}, \mathbf{v} \in \mathbb{R}^d`$, expand $`\Psi' = \cos\theta\,\Psi + \sin\theta\,\mathbf{e}_2`$:

$$
\langle \Psi', \mathbf{u}\rangle_{\mathbb{R}}\langle \Psi', \mathbf{v}\rangle_{\mathbb{R}} = \cos^2\theta\thinspace\langle \Psi, \mathbf{u}\rangle\langle \Psi, \mathbf{v}\rangle + \cos\theta\sin\theta\bigl(\langle \Psi, \mathbf{u}\rangle\langle \mathbf{e}_2, \mathbf{v}\rangle + \langle \Psi, \mathbf{v}\rangle\langle \mathbf{e}_2, \mathbf{u}\rangle\bigr) + \sin^2\theta\thinspace\langle \mathbf{e}_2, \mathbf{u}\rangle\langle \mathbf{e}_2, \mathbf{v}\rangle.
$$

Integrate first over $`\mathbf{e}_2 \sim \mu_\perp(\Psi)`$ (`perpSphereMeasure Ψ`) at fixed $`\theta`$. Every linear isometry of $`V_\perp(\Psi)`$ has determinant $`\pm 1`$ (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`), preserving the subspace Haar measure and its sphere restriction (`V_perp_haar_map_isometry` and `V_perp_rawSph_isometry_invariant`, private helpers in `CrossTerm.lean`). Viewing negation $`\mathbf{e}_2 \mapsto -\mathbf{e}_2`$ on $`V_\perp(\Psi)`$ as `LinearIsometryEquiv.neg ℝ` therefore delegates directly to `V_perp_rawSph_isometry_invariant` and preserves `perpSphereMeasure Ψ` (`perpSphereMeasure_neg_invariant` in `CrossTerm.lean`). Consequently, for every fixed vector $`\mathbf{w} \in \mathbb{R}^d`$:

$$
\int \langle \mathbf{e}_2, \mathbf{w}\rangle_{\mathbb{R}}\thinspace d\mu_\perp(\mathbf{e}_2) = \int \langle -\mathbf{e}_2, \mathbf{w}\rangle_{\mathbb{R}}\thinspace d\mu_\perp(\mathbf{e}_2) = -\int \langle \mathbf{e}_2, \mathbf{w}\rangle_{\mathbb{R}}\thinspace d\mu_\perp(\mathbf{e}_2) \implies \int \langle \mathbf{e}_2, \mathbf{w}\rangle_{\mathbb{R}}\thinspace d\mu_\perp(\mathbf{e}_2) = 0
$$

(`integral_perp_inner_eq_zero`). Both $`\cos\theta\sin\theta`$ cross-terms vanish identically! (Specializing to $`\hat{\mathbf{e}}_{2w}, \hat{\mathbf{e}}_{2w+1}`$ also yields `integral_cross_term_eq_zero`, `integral_e₂_succProb`, and `expanded_E_pe`.)

### Step 2: Reflection Symmetries Pin Down $`\mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top] = \frac{1}{d - 1}P_{V_\perp(\Psi)}`$

Let $`P_\perp`$ (`P_perp Ψ : E n →L[ℝ] E n`) denote orthogonal projection onto $`V_\perp(\Psi)`$ (`SecondMoment.lean`), which acts on any $`\mathbf{u} \in \mathbb{R}^d`$ via (`P_perp_apply`):

$$
P_\perp \mathbf{u} = \mathbf{u} - \langle \Psi, \mathbf{u}\rangle_{\mathbb{R}}\thinspace\Psi.
$$

Rather than evaluating spherical coordinate integrals, `CrossTerm.lean` and `SecondMoment.lean` determine the second-moment operator $`M\mathbf{u} := \int \langle \mathbf{e}_2, \mathbf{u}\rangle_{\mathbb{R}}\,\mathbf{e}_2\,d\mu_\perp(\mathbf{e}_2)`$ purely from ambient orthogonal reflection symmetries [[Muirhead (1982)](#references); [Mardia & Jupp (2000)](#references)]. Choose an orthonormal basis $`\mathbf{b}_1, \dots, \mathbf{b}_{d-1}`$ of $`V_\perp(\Psi)`$. Whenever $`\mathbf{w} \in V_\perp(\Psi)`$ ($`\langle \Psi, \mathbf{w}\rangle_{\mathbb{R}} = 0`$), the ambient hyperplane reflection on `E n` across $`(\mathbb{R}\mathbf{w})^\perp \subset \mathbb{R}^d`$ fixes $`\Psi`$ (`Submodule.reflection_mem_subspace_eq_self`) and therefore preserves `perpSphereMeasure Ψ` via `perpSphereMeasure_map_isometry` (`integral_perpSphere_reflection_eq`, private helper in `CrossTerm.lean`):

**1. Off-diagonal vanishing (`integral_perpSphere_inner_mul_ortho`):** For $`i \ne j`$ ($`\mathbf{b}_i \perp \mathbf{b}_j`$), ambient reflection across $`(\mathbb{R}\mathbf{b}_i)^\perp \subset \mathbb{R}^d`$ fixes $`\Psi`$, sends $`\mathbf{b}_i \mapsto -\mathbf{b}_i`$ (`Submodule.reflection_orthogonalComplement_singleton_eq_neg`), and fixes $`\mathbf{b}_j \mapsto \mathbf{b}_j`$. By self-adjointness and `integral_perpSphere_reflection_eq`, $`\int \langle \mathbf{e}_2, \mathbf{b}_i\rangle\langle \mathbf{e}_2, \mathbf{b}_j\rangle\,d\mu_\perp = -\int \langle \mathbf{e}_2, \mathbf{b}_i\rangle\langle \mathbf{e}_2, \mathbf{b}_j\rangle\,d\mu_\perp = 0`$.

**2. Diagonal equality via Householder reflection (`integral_perpSphere_inner_sq_eq`):** Uniformly for all $`i, j`$ (including $`i = j`$, where $`(\mathbb{R}\mathbf{0})^\perp = \mathbb{R}^d`$ acts as the identity), the ambient Householder reflection across $`(\mathbb{R}(\mathbf{b}_i - \mathbf{b}_j))^\perp \subset \mathbb{R}^d`$ fixes $`\Psi`$ (since $`\mathbf{b}_i - \mathbf{b}_j \in V_\perp(\Psi)`$) and maps $`\mathbf{b}_i \mapsto \mathbf{b}_j`$ (`Submodule.reflection_sub`). Measure invariance (`integral_perpSphere_reflection_eq`) therefore forces all $`d - 1`$ diagonal expectations to share a common value $`c := \int \langle \mathbf{e}_2, \mathbf{b}_1\rangle^2\,d\mu_\perp`$. Since $`\langle \mathbf{e}_2, \mathbf{u}\rangle = \langle \mathbf{e}_2, P_\perp\mathbf{u}\rangle`$ almost everywhere, expanding $`P_\perp\mathbf{u}`$ and $`P_\perp\mathbf{v}`$ in $`\{\mathbf{b}_i\}`$ proves $`M\mathbf{u} = c\,P_\perp\mathbf{u}`$ (`secondMoment_eq_scalar_perp`).

**3. Trace normalization (`trace_secondMoment_eq_one`, `trace_P_perp`, `secondMoment_coeff`):** Summing diagonal entries over the ambient standard basis $`\{\hat{\mathbf{e}}_1, \dots, \hat{\mathbf{e}}_d\}`$ of $`\mathbb{R}^d`$ and applying Parseval's identity gives:

$$
1 = \int \lVert\mathbf{e}_2\rVert^2\thinspace d\mu_\perp(\mathbf{e}_2) = \sum_{k=1}^d \int \langle \mathbf{e}_2, \hat{\mathbf{e}}_k\rangle_{\mathbb{R}}^2\thinspace d\mu_\perp(\mathbf{e}_2) = c \sum_{k=1}^d \langle P_\perp\hat{\mathbf{e}}_k, \hat{\mathbf{e}}_k\rangle_{\mathbb{R}} = c\thinspace(d - 1) \implies c = \frac{1}{d - 1}.
$$

Taking the inner product of $`M\mathbf{u} = \frac{1}{d - 1}P_\perp\mathbf{u}`$ with $`\mathbf{v}`$ yields the exact equatorial bilinear expectation (`perpSphere_inner_mul_inner`):

$$
\int \langle \mathbf{e}_2, \mathbf{u}\rangle_{\mathbb{R}}\langle \mathbf{e}_2, \mathbf{v}\rangle_{\mathbb{R}}\thinspace d\mu_\perp(\mathbf{e}_2) = \frac{\langle P_\perp\mathbf{u}, \mathbf{v}\rangle_{\mathbb{R}}}{d - 1} = \frac{\langle \mathbf{u}, \mathbf{v}\rangle_{\mathbb{R}} - \langle \Psi, \mathbf{u}\rangle_{\mathbb{R}}\langle \Psi, \mathbf{v}\rangle_{\mathbb{R}}}{d - 1}.
$$

*(Note:* Summing this identity over $`\mathbf{u} = \mathbf{v} = \hat{\mathbf{e}}_{2w}`$ and $`\mathbf{u} = \mathbf{v} = \hat{\mathbf{e}}_{2w+1}`$ immediately yields the equatorial "decoherent floor" $`\int \operatorname{succProb}(n, \mathbf{e}_2, w)\,d\mu_\perp(\mathbf{e}_2) = \frac{2 - \operatorname{succProb}(n, \Psi, w)}{d - 1}`$ proved in `decoherent_floor`.)

### Step 3: Exact $`(d - 1)`$ Cancellation in One Isotropic Error Step

Now integrate over $`\theta \sim \nu_{d,\sigma}`$ (`poissonAngleMeasure (d n) σ`) for any $`\sigma \in [0, 1]`$. By `poissonAngleMeasure_cos_sq` (§3), $`\mathrm{E}[\cos^2\theta] = \frac{(d - 1)\sigma^2 + 1}{d}`$, so $`\mathrm{E}[\sin^2\theta] = 1 - \mathrm{E}[\cos^2\theta] = \frac{(d - 1)(1 - \sigma^2)}{d}`$ (`integral_sin_sq_eq_one_sub_integral_cos_sq`). Combining the $`\mathbf{e}_2`$ and $`\theta`$ integrals:

```math
\begin{aligned}
\mathrm{E}_{\theta, \mathbf{e}_2}\!\bigl[\langle \Psi', \mathbf{u}\rangle_{\mathbb{R}}\langle \Psi', \mathbf{v}\rangle_{\mathbb{R}}\bigr]
&= \frac{(d - 1)\sigma^2 + 1}{d}\,\langle \Psi, \mathbf{u}\rangle\langle \Psi, \mathbf{v}\rangle + \frac{(d - 1)(1 - \sigma^2)}{d} \cdot \frac{\langle \mathbf{u}, \mathbf{v}\rangle - \langle \Psi, \mathbf{u}\rangle\langle \Psi, \mathbf{v}\rangle}{d - 1} \\[4pt]
&= \frac{(d - 1)\sigma^2 + 1 - (1 - \sigma^2)}{d}\,\langle \Psi, \mathbf{u}\rangle\langle \Psi, \mathbf{v}\rangle + \frac{1 - \sigma^2}{d}\,\langle \mathbf{u}, \mathbf{v}\rangle \\[4pt]
&= \sigma^2\,\langle \Psi, \mathbf{u}\rangle_{\mathbb{R}}\langle \Psi, \mathbf{v}\rangle_{\mathbb{R}} + \frac{1 - \sigma^2}{d}\,\langle \mathbf{u}, \mathbf{v}\rangle_{\mathbb{R}}.
\end{aligned}
```

This is theorem `isotropicError_bilinear_secondMoment` in `SecondMoment.lean`. Notice the geometry behind this cancellation: the polar variance gives $`1 - \mathrm{E}[\cos^2\theta] = \frac{d - 1}{d}(1 - \sigma^2)`$ because $`d - 1`$ of the $`d`$ ambient axes are orthogonal to $`\Psi`$, while the equatorial uniform average divides that orthogonal energy equally across those same $`d - 1`$ axes! In matrix form on $`\mathbb{R}^d`$,

$$
\mathrm{E}\bigl[\Psi'(\Psi')^\top\bigr] = \sigma^2\thinspace\Psi\Psi^\top + \frac{1 - \sigma^2}{d}\thinspace I_d.
$$

Setting $`\mathbf{u} = \mathbf{v} = \hat{\mathbf{e}}_{2w}`$ and $`\mathbf{u} = \mathbf{v} = \hat{\mathbf{e}}_{2w+1}`$ and summing uses $`\langle \hat{\mathbf{e}}_{2w}, \hat{\mathbf{e}}_{2w}\rangle + \langle \hat{\mathbf{e}}_{2w+1}, \hat{\mathbf{e}}_{2w+1}\rangle = 1 + 1 = 2`$ and $`\frac{2}{d} = \frac{2}{2 \cdot 2^n} = \frac{1}{2^n}`$ to give the single-step mixture formula (`isotropicError_succProb_oneStep`):

$$
\mathrm{E}_{\theta, \mathbf{e}_2}\bigl[\operatorname{succProb}\bigl(n,\thinspace \cos\theta\thinspace\Psi + \sin\theta\thinspace\mathbf{e}_2,\thinspace w\bigr)\bigr] = \sigma^2\thinspace\operatorname{succProb}(n, \Psi, w) + \frac{1 - \sigma^2}{2^n}.
$$

---

## §5 — Exact Emergence of the Complex Quantum Depolarizing Channel (`CPTPMap`)

### Physical Question: Does Real-Sphere Noise Respect Complex Quantum Mechanics?

In §4 we saw that on $`\mathbb{R}^{2N}`$, one isotropic pure-state perturbation maps $`\Psi\Psi^\top \mapsto \sigma^2\Psi\Psi^\top + \frac{1-\sigma^2}{2N}I_{2N}`$. At first glance, one might worry: because individual realizations $`\Psi'`$ rotate across *real* subspaces that do not preserve complex phases, could averaging the *complex* rank-1 projector $`|\psi'\rangle\langle\psi'| \in \mathbb{C}^{N \times N}`$ introduce anomalous phase-dependent or off-diagonal noise terms?

Here we show — mirroring `IsotropicGroverProof/QuantumChannel.lean` line-for-line — that the orthogonality between even (real-part) and odd (imaginary-part) coordinates causes all imaginary noise floor terms to cancel **identically**, while the real noise floor terms pair up as $`\frac{1}{d} + \frac{1}{d} = \frac{1}{N}`$, producing the **exact complex $`n`$-qubit depolarizing channel**!

### Entrywise Real and Imaginary Expectation of $`|\psi'\rangle\langle\psi'|`$

For any real vector $`\Psi \in \mathbb{R}^d`$ with corresponding complex vector $`\psi_x = \Psi_{2x} + i\,\Psi_{2x+1}`$ (`realToVec Ψ`), `QuantumChannel.lean` defines the associated $`N \times N`$ complex outer-product matrix (`pureDensityMatrix n Ψ`):

$$
\Pi(\Psi)_{x,y} := \psi_x \overline{\psi_y} = (\Psi_{2x} + i\thinspace\Psi_{2x+1})(\Psi_{2y} - i\thinspace\Psi_{2y+1}), \qquad x, y \in \mathrm{Fin}(2^n).
$$

Whenever $`\Psi = \operatorname{ketToReal}(\psi)`$ for a normalized ket $`|\psi\rangle`$, $`\Pi(\Psi)`$ agrees entrywise with `Physlib`'s pure-state density matrix `(MState.pure ψ).m` (`pureDensityMatrix_ketToReal`). Multiplying out $`\Pi(\Psi)_{x,y}`$ separates its real and imaginary parts into sums and differences of real inner products with $`\hat{\mathbf{e}}_{2x}`$ (`stdBasisVec n (succProbIdx0 n x)`) and $`\hat{\mathbf{e}}_{2x+1}`$ (`stdBasisVec n (succProbIdx1 n x)`):

```math
\begin{aligned}
\operatorname{Re}\Pi(\Psi)_{x,y} &= \langle \Psi, \hat{\mathbf{e}}_{2x}\rangle_{\mathbb{R}}\langle \Psi, \hat{\mathbf{e}}_{2y}\rangle_{\mathbb{R}} + \langle \Psi, \hat{\mathbf{e}}_{2x+1}\rangle_{\mathbb{R}}\langle \Psi, \hat{\mathbf{e}}_{2y+1}\rangle_{\mathbb{R}}, \\[4pt]
\operatorname{Im}\Pi(\Psi)_{x,y} &= \langle \Psi, \hat{\mathbf{e}}_{2x+1}\rangle_{\mathbb{R}}\langle \Psi, \hat{\mathbf{e}}_{2y}\rangle_{\mathbb{R}} - \langle \Psi, \hat{\mathbf{e}}_{2x}\rangle_{\mathbb{R}}\langle \Psi, \hat{\mathbf{e}}_{2y+1}\rangle_{\mathbb{R}}.
\end{aligned}
```

Now replace $`\Psi`$ by the perturbed state $`\Psi' = \cos\theta\,\Psi + \sin\theta\,\mathbf{e}_2`$ and apply `isotropicError_bilinear_secondMoment` (§4) to each bilinear product:

**1. Real part (`noisyTrajectory_pureDensityMatrix_re`):** Both products pair indices of the **same parity** ($`2x`$ with $`2y`$, and $`2x+1`$ with $`2y+1`$). By orthonormality and index injectivity (`succProbIdx0_inj`, `succProbIdx1_inj`),

$$
\langle \hat{\mathbf{e}}_{2x}, \hat{\mathbf{e}}_{2y}\rangle_{\mathbb{R}} = \delta_{x,y}, \qquad \langle \hat{\mathbf{e}}_{2x+1}, \hat{\mathbf{e}}_{2y+1}\rangle_{\mathbb{R}} = \delta_{x,y}.
$$

Summing the two expectations therefore adds their isotropic floors:

```math
\begin{aligned}
\mathrm{E}\bigl[\operatorname{Re}\Pi(\Psi')_{x,y}\bigr]
&= \left(\sigma^2\Psi_{2x}\Psi_{2y} + \frac{1 - \sigma^2}{d}\delta_{x,y}\right) + \left(\sigma^2\Psi_{2x+1}\Psi_{2y+1} + \frac{1 - \sigma^2}{d}\delta_{x,y}\right) \\[4pt]
&= \sigma^2\,\operatorname{Re}\Pi(\Psi)_{x,y} + (1 - \sigma^2)\,\frac{2}{2 \cdot 2^n}\,\delta_{x,y} \\[4pt]
&= \sigma^2\,\operatorname{Re}\Pi(\Psi)_{x,y} + (1 - \sigma^2)\,\frac{\delta_{x,y}}{2^n}.
\end{aligned}
```

**2. Imaginary part (`noisyTrajectory_pureDensityMatrix_im`):** Both products pair an **even index with an odd index** ($`2x+1`$ with $`2y`$, and $`2x`$ with $`2y+1`$). Because an even integer never equals an odd integer (`succProbIdx0_ne_succProbIdx1`), these basis vectors are orthogonal **for all $`x, y`$ — including on the diagonal $`x = y`$**:

$$
\langle \hat{\mathbf{e}}_{2x+1}, \hat{\mathbf{e}}_{2y}\rangle_{\mathbb{R}} = 0, \qquad \langle \hat{\mathbf{e}}_{2x}, \hat{\mathbf{e}}_{2y+1}\rangle_{\mathbb{R}} = 0.
$$

Hence both $`\frac{1 - \sigma^2}{d}`$ floor terms vanish identically, leaving pure $`\sigma^2`$ contraction:

$$
\mathrm{E}\bigl[\operatorname{Im}\Pi(\Psi')_{x,y}\bigr] = \sigma^2\bigl(\Psi_{2x+1}\Psi_{2y} - \Psi_{2x}\Psi_{2y+1}\bigr) = \sigma^2\thinspace\operatorname{Im}\Pi(\Psi)_{x,y}.
$$

### Packaging as a Verified `CPTPMap`

Recombining real and imaginary parts (`noisyTrajectoryExpectationℂ_eq_re_im`) gives the exact complex matrix identity:

$$
\mathrm{E}_{\theta, \mathbf{e}_2}\bigl[|\psi'\rangle\langle\psi'|\bigr] = \sigma^2\thinspace|\psi\rangle\langle\psi| + (1 - \sigma^2)\thinspace\frac{I_N}{N}, \qquad N = 2^n, \quad \sigma \in [0, 1].
$$

In `QuantumChannel.lean`, we construct the $`n`$-qubit depolarizing channel `depolarizingChannel n σ hσ : CPTPMap (Fin (2 ^ n)) (Fin (2 ^ n))` for $`\sigma \in [0, 1]`$ as the convex combination

$$
\Lambda_\sigma(\rho) := \sigma^2\thinspace\mathrm{id}(\rho) + (1 - \sigma^2)\thinspace\mathrm{replacement}_{\rho_{\mathrm{unif}}}(\rho),
$$

where $`\rho_{\mathrm{unif}}`$ (`MState.uniform`) has density matrix $`\frac{1}{2^n}I_{2^n}`$. Complete positivity (`cp`) holds because $`\sigma^2 \ge 0`$ and $`1 - \sigma^2 \ge 0`$ for all $`\sigma \in [0, 1]`$, and trace preservation (`TP`) holds because $`\sigma^2 + (1 - \sigma^2) = 1`$ (`MatrixMap.IsTracePreserving.unit_linear`). Theorem `isotropicOneStep_eq_depolarizingChannel` verifies that one step of microscopic real-sphere isotropic noise on $`|\psi\rangle`$ equals $`\Lambda_\sigma(|\psi\rangle\langle\psi|)`$ entrywise.

---

## §6 — Multi-Gate Noisy Circuits: Markov Trajectories, Channel Commutation, and Syntactic `Circuit.size`

In a physical circuit of $`G`$ gates $`U_1, U_2, \dots, U_G`$, noise acts **after every gate**: the $`k`$-th error rotates around the *already-perturbed* state $`U_k\Psi_{k-1}`$, so the equatorial tangent sphere $`V_\perp(U_k\Psi_{k-1}) \cap S^{d-1}`$ tilts randomly from step to step. Prior literature [[Lacalle & Pozo Coronado (2019)](#references)] argued that all $`G`$ pure-state errors can be commuted to the end of the circuit as a single effective pure-state rotation of parameter $`\sigma^G`$ by appealing to spherical convolution on $`\mathrm{SO}(d)`$.

Our formalization requires **no spherical-angle convolution assumption**. Instead, we establish multi-gate error accumulation directly across three equivalent, machine-checked representations.

### 6.1 Representation A — Microscopic Pure-State Markov Chain (`Sequential.lean`)

Let $`\Phi_0 \in S^{d-1}`$ be any initial unit state and `gates` $`= [U_1, \dots, U_G]`$ (`gates : List (E n ≃ₗᵢ[ℝ] E n)`) be any sequence of real linear isometries. The ideal noiseless trajectory is $`\Phi_G = U_G \cdots U_1 \Phi_0`$ (`idealGateTrajectory`, `idealGateIso`), while the noisy pure-state Markov chain evolves via:

$$
\Psi_0 = \Phi_0, \qquad \Psi_k = \cos\theta_k\thinspace(U_k\Psi_{k-1}) + \sin\theta_k\thinspace\mathbf{e}_{2,k} \quad (k = 1, \dots, G),
$$

with $`\mathbf{e}_{2,k} \sim \mu_\perp(U_k\Psi_{k-1})`$ and $`\theta_k \sim \nu_{d,\sigma}`$ drawn independently at each step. In `Sequential.lean`, the $`G`$-fold iterated expectation of any observable $`f : \mathbb{R}^d \to \mathbb{R}`$ is defined recursively as `noisyTrajectoryExpectation`:

$$
\mathcal{E}_\sigma([\thinspace], \Phi_0, f) = f(\Phi_0), \qquad \mathcal{E}_\sigma(U :: \mathit{rest}, \Phi_0, f) = \int_0^\pi \int_{S(V_\perp(U\Phi_0))} \mathcal{E}_\sigma\bigl(\mathit{rest},\thinspace \cos\theta\thinspace(U\Phi_0) + \sin\theta\thinspace\mathbf{e}_2,\thinspace f\bigr)\thinspace d\mu_\perp(\mathbf{e}_2)\thinspace d\nu_{d,\sigma}(\theta).
$$

#### Analytic Subtlety: Householder Transport for Continuity on $`S^{d-1}`$

Because Lean's Bochner integral is only additive on *integrable* functions (`integral_add`), inducting over $`G`$ nested integrals requires proving that if $`g : \mathbb{R}^d \to \mathbb{R}`$ is continuous on $`S^{d-1}`$, then the one-step transition $`\Psi \mapsto \int \int g(\cos\theta\,\Psi + \sin\theta\,\mathbf{e}_2)\,d\mu_\perp(\Psi)\,d\nu_{d,\sigma}(\theta)`$ remains continuous on $`S^{d-1}`$ (`noisyTrajectoryExpectation_continuousOn_unitSphere`) — even though the integration measure $`\mu_\perp(\Psi)`$ varies with $`\Psi`$!

To transport $`\mu_\perp(\Psi_0)`$ continuously onto $`\mu_\perp(\Psi)`$ for $`\Psi \in S^{d-1}`$ near $`\Psi_0 \in S^{d-1}`$ (where $`\Psi_0 + \Psi \ne \mathbf{0}`$), `Sequential.lean` constructs the explicit involutive reflection (`rotTo`, private helper in `Sequential.lean`):

$$
R_{\Psi_0 + \Psi}(\mathbf{x}) := \frac{2\langle \Psi_0 + \Psi, \mathbf{x}\rangle_{\mathbb{R}}}{\lVert\Psi_0 + \Psi\rVert^2}(\Psi_0 + \Psi) - \mathbf{x}.
$$

For unit vectors $`\Psi_0, \Psi`$ with $`\Psi_0 + \Psi \ne \mathbf{0}`$, $`2\langle \Psi_0 + \Psi, \Psi_0\rangle = 2(1 + \langle \Psi, \Psi_0\rangle) = \|\Psi_0 + \Psi\|^2`$, so $`R_{\Psi_0 + \Psi}`$ is a linear isometry satisfying $`R_{\Psi_0 + \Psi}(\Psi_0) = \Psi`$ and varying continuously in $`\Psi`$ at $`\Psi_0`$. By ambient isometry equivariance (`perpSphereMeasure_map_isometry`), pushing $`\mu_\perp(\Psi_0)`$ forward along $`R_{\Psi_0 + \Psi}`$ yields $`\mu_\perp(\Psi)`$, rewriting the varying-domain integral over a **fixed** measure $`\mu_\perp(\Psi_0)`$:

$$
\int g(\cos\theta\thinspace\Psi + \sin\theta\thinspace\mathbf{e}_2)\thinspace d\mu_\perp(\Psi)(\mathbf{e}_2) = \int \tilde{g}\bigl(\cos\theta\thinspace\Psi + \sin\theta\thinspace R_{\Psi_0 + \Psi}(\mathbf{e}_2)\bigr)\thinspace d\mu_\perp(\Psi_0)(\mathbf{e}_2),
$$

where $`\tilde{g}`$ (`extendFromSphere`, private helper in `Sequential.lean`) radially extends $`g|_{S^{d-1}}`$ to a globally continuous, bounded function on $`\mathbb{R}^d`$. Lebesgue's Dominated Convergence Theorem then proves continuity on $`S^{d-1}`$ and full linearity (`noisyTrajectoryExpectation_add`, `noisyTrajectoryExpectation_sub`) for all $`\sigma \in [0, 1]`$.

#### Adjoint-Pullback Induction for `noisyTrajectory_bilinear`

With linearity and integrability in hand, `noisyTrajectory_bilinear` proves that for any gate list `gates` ($`\mathit{gates}`$) of length $`G`$, unit vector $`\|\Phi_0\| = 1`$, $`\sigma \in [0, 1]`$, and $`\mathbf{u}, \mathbf{v} \in \mathbb{R}^d`$:

$$
\mathcal{E}_\sigma\bigl(\mathit{gates}, \Phi_0, \Psi \mapsto \langle \Psi, \mathbf{u}\rangle_{\mathbb{R}}\langle \Psi, \mathbf{v}\rangle_{\mathbb{R}}\bigr) = \sigma^{2G}\thinspace\langle \Phi_G, \mathbf{u}\rangle_{\mathbb{R}}\langle \Phi_G, \mathbf{v}\rangle_{\mathbb{R}} + \frac{1 - \sigma^{2G}}{d}\thinspace\langle \mathbf{u}, \mathbf{v}\rangle_{\mathbb{R}}.
$$

*Proof by induction on `gates`:*

**Base case (`gates = []`, $`G = 0`$):** $`\sigma^0 = 1`$ and $`1 - \sigma^0 = 0`$, giving $`\langle \Phi_0, \mathbf{u}\rangle\langle \Phi_0, \mathbf{v}\rangle`$.

**Inductive step (`gates = U :: rest` of length $`G = 1 + m`$):** Let $`W \in \mathrm{O}(d)`$ (`idealGateIso rest : E n ≃ₗᵢ[ℝ] E n`) be the composite ideal isometry of `rest`, so $`\Phi_G = W(U\Phi_0)`$ and $`\langle W\Psi_1, \mathbf{u}\rangle = \langle \Psi_1, W^{-1}\mathbf{u}\rangle`$ for the post-first-gate noisy state $`\Psi_1 = \cos\theta_1\,(U\Phi_0) + \sin\theta_1\,\mathbf{e}_{2,1}`$. By the induction hypothesis on `rest` starting from unit state $`\Psi_1`$:

$$
\mathcal{E}_\sigma\bigl(\mathit{rest}, \Psi_1, \Psi \mapsto \langle \Psi, \mathbf{u}\rangle\langle \Psi, \mathbf{v}\rangle\bigr) = \sigma^{2m}\thinspace\langle \Psi_1, W^{-1}\mathbf{u}\rangle\langle \Psi_1, W^{-1}\mathbf{v}\rangle + \frac{1 - \sigma^{2m}}{d}\thinspace\langle \mathbf{u}, \mathbf{v}\rangle.
$$

Now take the outer single-step expectation over $`(\theta_1, \mathbf{e}_{2,1})`$ using `isotropicError_bilinear_secondMoment` (§4) with test vectors $`W^{-1}\mathbf{u}, W^{-1}\mathbf{v}`$, and use $`\langle W^{-1}\mathbf{u}, W^{-1}\mathbf{v}\rangle = \langle \mathbf{u}, \mathbf{v}\rangle`$:

```math
\begin{aligned}
\mathcal{E}_\sigma\bigl(U :: \mathit{rest}, \Phi_0, \Psi \mapsto \langle \Psi, \mathbf{u}\rangle\langle \Psi, \mathbf{v}\rangle\bigr)
&= \sigma^{2m}\left[\sigma^2\,\langle U\Phi_0, W^{-1}\mathbf{u}\rangle\langle U\Phi_0, W^{-1}\mathbf{v}\rangle + \frac{1 - \sigma^2}{d}\,\langle \mathbf{u}, \mathbf{v}\rangle\right] + \frac{1 - \sigma^{2m}}{d}\,\langle \mathbf{u}, \mathbf{v}\rangle \\[4pt]
&= \sigma^{2(m+1)}\,\langle W(U\Phi_0), \mathbf{u}\rangle\langle W(U\Phi_0), \mathbf{v}\rangle + \frac{\sigma^{2m}(1 - \sigma^2) + (1 - \sigma^{2m})}{d}\,\langle \mathbf{u}, \mathbf{v}\rangle \\[4pt]
&= \sigma^{2(m+1)}\,\langle \Phi_G, \mathbf{u}\rangle\langle \Phi_G, \mathbf{v}\rangle + \frac{1 - \sigma^{2(m+1)}}{d}\,\langle \mathbf{u}, \mathbf{v}\rangle. \qquad \blacksquare
\end{aligned}
```

Two immediate specializations follow:

**1. Squared state-overlap recurrence (`noisyTrajectory_fidelity_eq_sequentialFidelity`):** Taking $`\mathbf{u} = \mathbf{v} = \Phi_G`$ gives the expected squared overlap with the ideal output state:

$$
f_G := \mathrm{E}\bigl[\langle \Psi_G, \Phi_G\rangle_{\mathbb{R}}^2\bigr] = \sigma^{2G} + \frac{1 - \sigma^{2G}}{d} = \frac{(d - 1)\sigma^{2G} + 1}{d},
$$

matching the scalar Markov recurrence $`f_0 = 1`$, $`f_{k+1} = T(f_k) := \lambda f_k + (1 - \lambda)\frac{1 - f_k}{d - 1}`$ with $`\lambda = \frac{(d-1)\sigma^2+1}{d}`$ (`stepLambda`, `stepTransition`, `sequentialFidelity`), which contracts geometrically toward $`\frac{1}{d}`$ via $`T(f) - \frac{1}{d} = \sigma^2\bigl(f - \frac{1}{d}\bigr)`$ (`stepTransition_sub_inv_d`, `sequentialFidelity_eq`, `sequentialFidelity_eq_f₂`, `sequential_mixture_formula`).

**2. Multi-gate measurement probability (`noisyTrajectory_succProb`):** Summing over $`\mathbf{u} = \mathbf{v} = \hat{\mathbf{e}}_{2w}`$ and $`\hat{\mathbf{e}}_{2w+1}`$ proves for all $`\sigma \in [0, 1]`$ and any `gates` of length $`G`$ (`gates.length`, including `gates = []`):

$$
\mathcal{E}_\sigma\bigl(\mathit{gates}, \Phi_0, \Psi \mapsto \operatorname{succProb}(n, \Psi, w)\bigr) = \sigma^{2G}\thinspace\operatorname{succProb}(n, \Phi_G, w) + \frac{1 - \sigma^{2G}}{2^n},
$$

where $`\Phi_G = \operatorname{idealGateTrajectory}(\mathit{gates}, \Phi_0)`$ (`idealGateTrajectory gates Φ₀`). *(Note:* For $`\sigma \in (0, 1)`$ and $`G > 0`$, this agrees identically with `isotropicGrover_main` in `MainTheorem.lean`, which integrates over the single effective angle measure `composedMeasure (d n) G σ`.)

### 6.2 Representation B — `CPTPMap` Unitary Commutation and Semigroup Composition (`QuantumChannel.lean`)

Viewing the same multi-gate process on complex density matrices (`MState (Fin (2 ^ n))`) makes the algebraic reason for $`\sigma^{2G}`$ completely transparent:

**1. Commutation with arbitrary unitaries (`depolarizingChannel_comm_ofUnitary`):** Because the maximally mixed state is unitarily invariant — $`U\left(\frac{I_N}{N}\right)U^\dagger = \frac{1}{N}UU^\dagger = \frac{I_N}{N}`$ (`ofUnitary_uniform`) — every unitary channel $`\mathcal{U}_U(\rho) = U\rho U^\dagger`$ (`CPTPMap.ofUnitary U`) commutes with $`\Lambda_\sigma`$:

$$
\Lambda_\sigma \circ \mathcal{U}_U(\rho) = \sigma^2\thinspace(U\rho U^\dagger) + (1 - \sigma^2)\thinspace\frac{I_N}{N} = U\left(\sigma^2\rho + (1 - \sigma^2)\frac{I_N}{N}\right)U^\dagger = \mathcal{U}_U \circ \Lambda_\sigma(\rho).
$$

**2. Multiplicative depolarizing semigroup (`depolarizingChannel_compose`):** For any $`\sigma_1, \sigma_2 \in [0, 1]`$, composing two depolarizing channels multiplies their fidelity parameters:

$$
\Lambda_{\sigma_1}\negthinspace\bigl(\Lambda_{\sigma_2}(\rho)\bigr) = \sigma_1^2\left(\sigma_2^2\rho + (1 - \sigma_2^2)\frac{I_N}{N}\right) + (1 - \sigma_1^2)\frac{I_N}{N} = (\sigma_1\sigma_2)^2\rho + \bigl(1 - (\sigma_1\sigma_2)^2\bigr)\frac{I_N}{N} = \Lambda_{\sigma_1\sigma_2}(\rho).
$$

Repeatedly commuting $`\Lambda_\sigma`$ to the left of subsequent unitaries and merging $`\Lambda_\sigma \circ \cdots \circ \Lambda_\sigma = \Lambda_{\sigma^G}`$ collapses any $`G`$-stage unitary list `us : List 𝐔[Fin (2 ^ n)]` (`noisyUnitaryListChannel` in `GroverCircuit.lean`) to $`\Lambda_{\sigma^{\operatorname{length}(\mathit{us})}} \circ \mathcal{U}_{\operatorname{unitaryListProd}(\mathit{us})}`$ (`noisyUnitaryListChannel_eq`, where `unitaryListProd us` is the ordered unitary product `[] => 1`, `U :: rest => unitaryListProd rest * U`), and matches the $`G`$-step microscopic real-sphere expectation of `pureDensityMatrix` entrywise (`noisyTrajectory_eq_depolarizingChannel`).

### 6.3 Representation C — Syntactic Primitive-Gate Circuits and `Circuit.size` (`QuantumChannel.lean`)

In `formal-quantum-computation`, an $`n`$-qubit circuit `c : Circuit n` is an inductive syntax tree built from:
- `.identity` (the empty wire identity, `size = 0`, unitary $`I_N`$),
- `.gate g r` (a $`k`$-qubit `PrimitiveGate` $`g \in \{\mathrm{X}, \mathrm{Y}, \mathrm{Z}, \mathrm{H}, \mathrm{S}, \mathrm{T}, \mathrm{CNOT}, \mathrm{SWAP}, \mathrm{TOFF}\}`$ embedded on wire register `r : QRegister k n`, `size = 1`, unitary `r.embedUnitary g.eval`), and
- `.seq c₁ c₂` (sequential execution of `c₁` then `c₂`, `size = c₁.size + c₂.size`, unitary `c₂.eval * c₁.eval`).

`QuantumChannel.lean` defines the noisy semantics `noisyCircuitChannel σ hσ c` inductively by inserting $`\Lambda_\sigma`$ after every primitive gate `.gate g r` while leaving `.identity` noiseless. Structural induction on `c` using `depolarizingChannel_comm_ofUnitary`, `depolarizingChannel_compose`, and `ofUnitary_mul` proves (`noisyCircuitChannel_eq`):

$$
\operatorname{noisyCircuitChannel}(\sigma, c) = \Lambda_{\sigma^{c.\mathrm{size}}} \circ \mathcal{U}_{c.\mathrm{eval}}.
$$

Moreover, flattening `c` into its primitive unitary list `circuitUnitaries c` (of length `(circuitUnitaries c).length = c.size`, `length_circuitUnitaries`) proves that the microscopic real-sphere Markov trajectory of `c` and the `CPTPMap` / `computationalPOVM` semantics agree identically (`noisyCircuit_trajectory_eq_channel`, `noisyCircuit_trajectory_succProb_eq_measure`), giving for any initial mixed state $`\rho_0`$ (`noisyCircuit_bornProb`) and pure ket $`|\psi_0\rangle`$ (`noisyCircuit_bornProb_pure`):

$$
\mu_{\mathrm{computationalPOVM}(n)}\Bigl(\operatorname{noisyCircuitChannel}(\sigma, c)\bigl(|\psi_0\rangle\langle\psi_0|\bigr)\Bigr)(w) = \sigma^{2\thinspace c.\mathrm{size}}\thinspace\bigl|(c.\mathrm{evolve}\thinspace\psi_0)_w\bigr|^2 + \frac{1 - \sigma^{2\thinspace c.\mathrm{size}}}{2^n}.
$$

---

## §7 — Specialization to Grover's Search Algorithm and Concrete Primitive-Gate Circuits

We now specialize the general multi-gate theorems to Grover's quantum database search algorithm [[Grover (1996)](#references)], following `IsotropicGroverProof/GroverCircuit.lean`.

### 7.1 Geometry of Grover's 2D Search Plane

Given an unstructured search space of size $`N = 2^n`$ with marked target $`w \in \mathrm{Fin}(2^n)`$, ideal Grover dynamics takes place inside the real 2D plane spanned by two orthonormal states:
- the **target basis state** $`|w\rangle`$ (`targetBasisState n w = ketToReal (Ket.basis w)`, `targetBasisState_eq_ketToReal`, `succProb_targetBasisState`), with $`p_{\mathrm{ideal}} = 1`$, and
- the **uniform non-target superposition** $`|w^\perp\rangle = \frac{1}{\sqrt{N - 1}}\sum_{x \ne w} |x\rangle`$ (`targetPerpState n w`, a unit vector orthogonal to $`|w\rangle`$ when $`2^n > 1`$ via `norm_targetPerpState` and `inner_targetBasisState_targetPerpState`), with $`p_{\mathrm{ideal}} = 0`$ (`succProb_targetPerpState`).

Hadamard preparation $`H^{\otimes n}|0^n\rangle`$ creates the **uniform superposition** $`|s\rangle = \frac{1}{\sqrt{N}}\sum_{x=0}^{N-1} |x\rangle`$ (`uniformSuperposition n = ketToReal uniform_superposition`, `uniformSuperposition_eq_ketToReal`), which lies in this 2D plane at initial angle $`\frac{\theta_0}{2} := \arcsin(N^{-1/2})`$ (`Grover.halfAngle`), with initial success probability proved in `succProb_uniformSuperposition`:

$$
|s\rangle = \sin\negthinspace\left(\frac{\theta_0}{2}\right)|w\rangle + \cos\negthinspace\left(\frac{\theta_0}{2}\right)|w^\perp\rangle, \qquad \operatorname{succProb}(n, |s\rangle, w) = \sin^2\negthinspace\left(\frac{\theta_0}{2}\right) = \frac{1}{2^n}.
$$

Notice a revealing sanity check: prior to any Grover iterations ($`p_{\mathrm{ideal}} = 1/2^n`$), isotropic noise leaves the success probability invariant at $`\sigma^{2G}\cdot \frac{1}{2^n} + \frac{1 - \sigma^{2G}}{2^n} = \frac{1}{2^n}`$ — proved on the single-effective-step domain $`\sigma \in (0, 1),\, G > 0`$ in `isotropicGrover_uniformSuperposition`, and across the full closed domain $`\sigma \in [0, 1],\, G \in \mathbb{N}`$ via `noisyTrajectory_succProb` (and at $`K = 0`$ in `noisyGrover_iterGates_succProb` / `noisyGrover_fullGates_succProb`). More generally, wrapping `isotropicGrover_main` on $`\sigma \in (0, 1)`$ and $`G > 0`$, any search-plane state $`|\psi(\alpha)\rangle = \sin\alpha\,|w\rangle + \cos\alpha\,|w^\perp\rangle`$ (`groverState2D`, requiring `1 < 2 ^ n`, i.e. $`n \ge 1`$, so $`|w^\perp\rangle`$ is normalized) has expected success probability $`\sigma^{2G}\sin^2\alpha + \frac{1-\sigma^{2G}}{2^n}`$ (`isotropicGrover_groverState2D`; see also `isotropicGrover_groverState2D_prob` for $`p_{\mathrm{ideal}} \in [0, 1]`$ and `1 < 2 ^ n`, and `isotropicGrover_targetBasisState` for all $`n \in \mathbb{N}`$).

### 7.2 Dynamic $`K`$-Iteration Grover Evolution and End-to-End Noisy Theorems

In `formal-quantum-computation` (`QuantumComputation.Algorithms.Grover`), each Grover iteration applies two $`n`$-qubit unitaries:
1. the **phase oracle** $`O_w = I_N - 2|w\rangle\langle w|`$ (`Grover.oracleUnitary target`), which reflects across $`|w^\perp\rangle`$, followed by
2. the **Grover diffuser** $`D = 2|s\rangle\langle s| - I_N`$ (`Grover.diffuserUnitary`), which reflects across $`|s\rangle`$.

The product of two reflections $`D O_w`$ is a rotation by $`\theta_0 = 2\arcsin(2^{-n/2})`$ (`Grover.groverAngle`) toward $`|w\rangle`$ in the $`|w^\perp\rangle\text{--}|w\rangle`$ plane. After Hadamard preparation (`hadamardUnitary`) and $`K \in \mathbb{N}`$ Grover iterations starting from $`|0^n\rangle`$ (`Ket.basis 0`), the ideal unitary is `Grover.groverMatrix target K` and the evolved state is `Grover.groverState target K` (`unitaryListProd_groverFullGates_val`, `idealUnitaryTrajectory_groverIterGates`, `idealUnitaryTrajectory_groverFullGates`), achieving exact noiseless Born probability $`p_{\mathrm{succ}}(K, 2^n)`$ (`Grover.p_succ`, `groverState_bornProb`, `Grover.p_succ_eq_sin_sq`):

$$
p_{\mathrm{ideal}}(K, 2^n) = p_{\mathrm{succ}}(K, 2^n) = \sin^2\negthinspace\Bigl((2K + 1)\arcsin\bigl(2^{-n/2}\bigr)\Bigr).
$$

Combining this noiseless evolution bridge with §6 yields end-to-end noisy Grover theorems across **all $`\sigma \in [0, 1]`$ and $`K, n \in \mathbb{N}`$** at three levels of granularity:

**1. Macro-operator Grover sequences** (with $`p_{\mathrm{succ}}`$ denoting `Grover.p_succ`):

- *$`K`$ noisy oracle/diffuser iterations from $`|s\rangle`$ ($`G = 2K`$, `groverIterGates target K`):* Both the `computationalPOVM` Born probability (`noisyGrover_iterGates_bornProb`) and the pure-state sphere trajectory (`noisyGrover_iterGates_succProb`) equal:

$$
\mathrm{E}[p_e] = \sigma^{4K}\thinspace p_{\mathrm{succ}}(K, 2^n) + \frac{1 - \sigma^{4K}}{2^n}.
$$

- *Noisy Hadamard preparation plus $`K`$ noisy iterations from $`|0^n\rangle`$ ($`G = 2K + 1`$, `groverFullGates target K`):* Both representations (`noisyGrover_fullGates_bornProb`, `noisyGrover_fullGates_succProb`) equal:

$$
\mathrm{E}[p_e] = \sigma^{2(2K+1)}\thinspace p_{\mathrm{succ}}(K, 2^n) + \frac{1 - \sigma^{2(2K+1)}}{2^n}.
$$

**2. Arbitrary unitary gate decompositions (`us : List 𝐔[Fin (2 ^ n)]`):** Any unitary gate list `us` whose ideal evolution achieves `Grover.p_succ K (2 ^ n)` — in particular any decomposition satisfying `(unitaryListProd us).val = Grover.groverMatrix target K` — has noisy Born and trajectory success probability $`\sigma^{2\operatorname{length}(\mathit{us})}\,p_{\mathrm{succ}}(K, 2^n) + \frac{1 - \sigma^{2\operatorname{length}(\mathit{us})}}{2^n}`$ (`noisyGrover_unitaryList_bornProb`, `noisyGrover_unitaryList_succProb`, `noisyGrover_unitaryList_groverMatrix_bornProb`, `noisyGrover_unitaryList_groverMatrix_succProb`).

**3. Syntactic primitive-gate circuits (`c : Circuit n`, $`G = c.\mathrm{size}`$):** For target outcome $`w`$ (`target : Fin (2 ^ n)`), any primitive-gate circuit `c : Circuit n` achieving `Grover.p_succ K (2 ^ n)` (for instance when `c.eval.val = Grover.groverMatrix target K`) satisfies (`noisyGrover_circuit_bornProb`, `noisyGrover_circuit_trajectory_succProb`, `noisyGrover_circuit_groverMatrix_bornProb`, `noisyGrover_circuit_groverMatrix_trajectory_succProb`):

$$
\mu_{\mathrm{computationalPOVM}(n)}\Bigl(\operatorname{noisyCircuitChannel}(\sigma, c)\bigl(|\psi_0\rangle\langle\psi_0|\bigr)\Bigr)(w) = \sigma^{2\thinspace c.\mathrm{size}}\thinspace p_{\mathrm{succ}}(K, 2^n) + \frac{1 - \sigma^{2\thinspace c.\mathrm{size}}}{2^n}.
$$

### 7.3 Worked Primitive-Gate Circuit Examples

To demonstrate that the `Circuit n` theorems are non-vacuous and compute concrete polynomial formulas directly from circuit syntax, `GroverCircuit.lean` constructs and verifies two explicit primitive-gate circuits:

#### 1. 1-Qubit Hadamard Preparation ($`n = 1`$, $`N = 2`$, $`K = 0`$, $`c.\mathrm{size} = 1`$)

The single-gate circuit $`c = H_0`$ (`Circuit.H (0 : Wire 1)`) has `(Circuit.H 0).size = 1` and evaluates to `Grover.groverMatrix target 0` (`circuit_hadamard1_eval_val`), with ideal success probability `Grover.p_succ 0 2` equal to $`p_{\mathrm{succ}}(0, 2) = \sin^2(\arcsin(1/\sqrt{2})) = \frac{1}{2}`$ (`p_succ_zero`, `p_succ_zero_two`). Theorem `noisyGrover_circuit_hadamard1_bornProb` proves that for all $`\sigma \in [0, 1]`$ and both targets $`w \in \{0, 1\}`$ (`target : Fin 2`),

$$
\mu_{\mathrm{computationalPOVM}(1)}\negthinspace\Bigl(\operatorname{noisyCircuitChannel}(\sigma, H_0)(|0\rangle\langle 0|)\Bigr)(w) = \sigma^2 \cdot p_{\mathrm{succ}}(0, 2) + \frac{1 - \sigma^2}{2} = \frac{1}{2}.
$$

#### 2. 14-Gate 2-Qubit Grover Search ($`n = 2`$, $`N = 4`$, $`K = 1`$, marked state `target = 3`, i.e., $`|11\rangle`$)

`GroverCircuit.lean` builds `grover2QubitCircuit : Circuit 2` exclusively out of primitive `H`, `Z`, and `CNOT` gates:
- **Hadamard layer `layerH2` ($`2`$ gates):** `Circuit.H 0 ;;ᶜ Circuit.H 1`, implementing $`H^{\otimes 2}`$.
- **Phase oracle `oracle2Circuit` ($`3`$ gates):** `Circuit.H 1 ;;ᶜ Circuit.CNOT 0 1 _ ;;ᶜ Circuit.H 1`, implementing controlled-$`Z`$ ($`\operatorname{diag}(1, 1, 1, -1)`$, i.e., `Grover.oracleUnitary 3`).
- **Diffuser `diffuser2Circuit` ($`9`$ gates):** `layerH2 ;;ᶜ Circuit.Z 0 ;;ᶜ Circuit.Z 1 ;;ᶜ oracle2Circuit ;;ᶜ layerH2`, implementing $`H^{\otimes 2}(2|00\rangle\langle 00| - I_4)H^{\otimes 2} = 2|s\rangle\langle s| - I_4`$ (`Grover.diffuserUnitary`).
- **Full circuit `grover2QubitCircuit` ($`2 + 3 + 9 = 14`$ primitive gates):** `layerH2 ;;ᶜ oracle2Circuit ;;ᶜ diffuser2Circuit`, with `grover2QubitCircuit.size = 14` (`size_grover2QubitCircuit`, `rfl`) and `grover2QubitCircuit.eval.val = Grover.groverMatrix 3 1` (`grover2QubitCircuit_eval_val`).

For $`N = 4`$, the initial half-angle is $`\arcsin(1/\sqrt{4}) = \arcsin(1/2) = \frac{\pi}{6}`$, so a single Grover iteration ($`K = 1`$) rotates to $`(2 \cdot 1 + 1)\frac{\pi}{6} = \frac{\pi}{2}`$ and finds $`|11\rangle`$ with **unit ideal probability** $`p_{\mathrm{succ}}(1, 4) = \sin^2(\pi/2) = 1`$ (`Grover.p_succ 1 4`, `p_succ_one_four`)! Instantiating `noisyGrover_circuit_groverMatrix_bornProb` at $`c =`$ `grover2QubitCircuit` with $`c.\mathrm{size} = 14`$ (`2 * 14 = 28`) yields theorem `noisyGrover_circuit_grover2_bornProb`: for all $`\sigma \in [0, 1]`$,

$$
\mu_{\mathrm{computationalPOVM}(2)}\negthinspace\Bigl(\operatorname{noisyCircuitChannel}(\sigma, c)(|00\rangle\langle 00|)\Bigr)(3) = \sigma^{28} + \frac{1 - \sigma^{28}}{4}.
$$

---

## §8 — Limiting Regimes, Continuity, Monotonicity, and Downstream Repetition Overhead

### 8.1 Limiting Regimes, Closed-Interval Continuity, and Monotonicity

`IsotropicGroverProof/LimitingCases.lean` packages the affine convex combination `mixtureProb`:

$$
\operatorname{mixtureProb}(p, N, f) := f \cdot p + \frac{1 - f}{N}
$$

at effective fidelity $`f = \sigma^{2G}`$ (`isotropicGrover_lhs_eq_mixtureProb`, `noisyTrajectory_succProb_eq_mixtureProb`) and verifies its analytical properties across all regimes:

**1. Noiseless regime ($`\sigma = 1`$ or $`\sigma \to 1`$):** At $`\sigma = 1`$, $`\sigma^{2G} = 1`$ and $`\mathrm{E}[p_e] = p_{\mathrm{ideal}}`$ exactly for every gate list (`mixtureProb_at_one`, `noisyTrajectory_succProb_at_sigma_one`), with filter convergence as $`\sigma \to 1`$ on $`[0, 1]`$ for all `gates` (`tendsto_noisyTrajectory_succProb_sigma_one`) and on $`(0, 1)`$ for $`G > 0`$ (`tendsto_expectedSuccProb_as_sigma_one`, `tendsto_expectedSuccProb_as_sigma_one_left`).

**2. Complete decoherence ($`\sigma = 0`$ with $`G \ge 1`$, or $`\sigma^{2G} \to 0`$ as $`G \to \infty`$):** Whenever the circuit executes at least one gate (`gates ≠ []`, $`G \ge 1`$), setting $`\sigma = 0`$ gives $`0^{2G} = 0`$ and drives $`\mathrm{E}[p_e]`$ immediately to the uniform random-guessing floor $`\frac{1}{N} = \frac{1}{2^n}`$ (`mixtureProb_at_zero`, `noisyTrajectory_succProb_at_sigma_zero`), matching the limit $`\sigma \to 0^+`$ on $`[0, 1]`$ for `gates ≠ []` (`tendsto_noisyTrajectory_succProb_sigma_zero`) and on $`(0, 1)`$ for $`G > 0`$ (`tendsto_expectedSuccProb_as_sigma_zero`, `tendsto_expectedSuccProb_as_sigma_zero_right`). Geometrically, at $`\sigma = 0`$ the state $`\Psi_G`$ is Haar-uniform on $`S^{d-1}`$: its mean squared overlap with *each* real basis axis is $`\frac{1}{d} > 0`$ (`poissonIntegral_val_sigma_zero`), and summing the two real axes ($`2w`$ and $`2w+1`$) of $`|w\rangle`$ produces $`\frac{1}{d} + \frac{1}{d} = \frac{2}{d} = \frac{1}{N}`$.

**3. Zero-gate circuit ($`G = 0`$, `gates = []` or `Circuit.identity`):** When zero gates are executed, no error step acts; in Lean and real algebra $`0^0 = 1`$, so $`\sigma^{2 \cdot 0} p_{\mathrm{ideal}} + \frac{1 - \sigma^0}{2^n} = p_{\mathrm{ideal}}`$ (including at $`\sigma = 0`$), with `noisyTrajectory_succProb_nil` holding for all $`\sigma \in \mathbb{R}`$ and `noisyCircuitChannel_identity` holding for all $`\sigma \in [0, 1]`$. This explains why `hgates : gates ≠ []` is the exact sharp hypothesis in `noisyTrajectory_succProb_at_sigma_zero`.

**4. Continuity across $`[0, 1]`$ and monotonicity:** Even though the underlying measure `poissonAngleMeasure` changes type from an absolutely continuous Lebesgue density on $`[0, 1)`$ to a singular point mass $`\delta_0`$ at $`\sigma = 1`$, the resulting expectation $`\sigma \mapsto \sigma^{2G} p_{\mathrm{ideal}} + \frac{1 - \sigma^{2G}}{2^n}`$ is a polynomial on $`[0, 1]`$ and hence continuous everywhere on $`[0, 1]`$ (`continuous_mixtureProb_pow`, `continuousOn_noisyTrajectory_succProb`). Moreover, since

$$
\operatorname{mixtureProb}(p, N, f_2) - \operatorname{mixtureProb}(p, N, f_1) = (f_2 - f_1)\left(p - \frac{1}{N}\right),
$$

$`\operatorname{mixtureProb}(p, N, f)`$ is monotone non-decreasing in $`f = \sigma^{2G}`$ whenever the ideal algorithm outperforms random guessing, $`p_{\mathrm{ideal}} \ge \frac{1}{N}`$ (`mixtureProb_mono`).

### 8.2 Downstream Application: Multi-Run Repetition Overhead $`k(n)`$ *(Outside the Lean Formalization)*

Once $`\mathrm{E}[p_e]`$ is established, a standard operational question in noisy quantum search is: *how many independent runs $`k(n)`$ of the noisy circuit are needed so that at least one run finds the marked item $`w`$ (verified classically via the oracle) with cumulative probability $`p_{\mathrm{ideal}}`$?*

Across $`k`$ independent executions, each run fails with probability $`1 - \mathrm{E}[p_e]`$, so all $`k`$ runs fail with probability $`(1 - \mathrm{E}[p_e])^k`$. Setting $`1 - (1 - \mathrm{E}[p_e])^k = p_{\mathrm{ideal}}`$ and solving for $`k`$ yields:

$$
k(n) = \frac{\log(1 - p_{\mathrm{ideal}})}{\log(1 - \mathrm{E}[p_e])} = \frac{\log(1 - p_{\mathrm{ideal}})}{\log\negthinspace\left(1 - \sigma^{2G(n)} p_{\mathrm{ideal}} - \frac{1 - \sigma^{2G(n)}}{2^n}\right)}.
$$

In empirical benchmarking, $`G(n)`$ is read from transpiled circuit data at optimal Grover iteration count $`K_{\mathrm{opt}}(n) \approx \left\lfloor \frac{\pi}{4}\sqrt{2^n}\right\rfloor`$, and $`k(n)`$ can be fit numerically to an exponential curve $`a \cdot b^n + c`$. More generally, under heterogeneous per-gate fidelities (`noisyTrajectoryHet_succProb`, `circuitFidelity_eq_prod_count`, `circuitFidelity_arity`) and $`M`$-marked-item Grover search (`subsetSuccProb`, `noisyTrajectoryHet_subsetSuccProb`, `noisyCircuitHet_subsetBornProb`, `noisyMultiGroverHet_succProb`; see §9.2–§9.3), replacing $`\sigma^{2G(n)}`$ by $`\sigma_{\mathrm{eff}}(c)^2`$ and $`1/2^n`$ by $`M/2^n`$ yields the exact generalized expected success probability directly from the machine-checked theorems. Both the definition of $`k(n)`$ and empirical curve fitting are downstream applications built on the proved mixture formula rather than parts of `IsotropicGroverProof/`.

---

## §9 — Heterogeneous Gate Noise, Multi-Target Grover Search, and Generalizations

Because `IsotropicGroverProof/` separates the geometric real-sphere engine (`IsotropicError.lean`–`Sequential.lean`) from the `QuantumInfo` channel layer (`QuantumChannel.lean`) and the Grover specialization (`GroverCircuit.lean`), the formalization directly encompasses heterogeneous per-gate fidelity schedules and multi-target ($`M`$-marked-item) Grover search, and extends effortlessly to new quantum algorithms and general observables.

### 9.1 Extending to Any `Circuit n` Algorithm in `formal-quantum-computation`

Nothing in `QuantumChannel.lean` mentions Grover's algorithm: `noisyCircuitChannel_eq`, `noisyCircuitChannelHet_eq`, `noisyCircuit_bornProb`, `noisyCircuitHet_bornProb`, and `noisyCircuit_bornProb_pure` hold for **every** syntactic circuit `c : Circuit n` (`QuantumComputation` already includes Quantum Fourier Transform in `QuantumComputation/Algorithms/QFT/`, reversible Toffoli/AND gadgets, and chemistry/simulation specifications).

To obtain a verified noisy Born-rule theorem for *any* circuit `c : Circuit n`, initial ket `ψ₀ : Ket (Fin (2 ^ n))`, and basis outcome `w : Fin (2 ^ n)`:
1. Establish (or import) the noiseless specification `hideal : ‖(c.evolve ψ₀.vec) w‖ ^ 2 = p_ideal`.
2. Rewrite with `noisyCircuit_bornProb_pure σ hσ c ψ₀ w`:
   ```lean
   rw [noisyCircuit_bornProb_pure σ hσ c ψ₀ w, hideal]
   ```
   This single rewrite proves that for all $`\sigma \in [0, 1]`$, measuring $`w`$ under `computationalPOVM n` (and, via `noisyCircuit_trajectory_succProb_eq_measure`, along the microscopic real-sphere Markov trajectory) has exact probability $`\sigma^{2\,c.\mathrm{size}}\,p_{\mathrm{ideal}} + (1 - \sigma^{2\,c.\mathrm{size}})/2^n`$.

### 9.2 Arbitrary Hermitian Observables (`HermitianMat`), General `POVM`s, and Verified Multi-Target Grover Search

Theorem `noisyCircuitChannel_eq` (and its heterogeneous generalization `noisyCircuitChannelHet_eq`) determines the **full complex output density matrix** of any noisy circuit `c : Circuit n` on any initial mixed state $`\rho_0`$:

$$
\rho_{\mathrm{noisy}} = \Lambda_{\sigma^{c.\mathrm{size}}}\bigl(\mathcal{U}_{c.\mathrm{eval}}(\rho_0)\bigr) = \sigma^{2\thinspace c.\mathrm{size}}\thinspace\rho_{\mathrm{ideal}} + \bigl(1 - \sigma^{2\thinspace c.\mathrm{size}}\bigr)\thinspace\frac{I_N}{N}, \qquad \rho_{\mathrm{ideal}} := \mathcal{U}_{c.\mathrm{eval}}(\rho_0), \quad N = 2^n.
$$

By linearity of the Hilbert–Schmidt trace pairing `MState.exp_val` (`ρ.exp_val O = Re Tr(ρ O)`) for **any** Hermitian observable $`O`$ (`O : HermitianMat (Fin (2 ^ n)) ℂ`) in `QuantumInfo`:

$$
\operatorname{Tr}(\rho_{\mathrm{noisy}}\thinspace O) = \sigma^{2G}\thinspace\operatorname{Tr}(\rho_{\mathrm{ideal}}\thinspace O) + \bigl(1 - \sigma^{2G}\bigr)\thinspace\frac{\operatorname{Tr}(O)}{2^n}, \qquad G = c.\mathrm{size}.
$$

**Arbitrary `POVM` measurements:** For any finite outcome type `X` (`[Fintype X]`), `Λ : POVM X (Fin (2 ^ n))`, and outcome $`x \in X`$ with effect operator $`E_x`$ (`Λ.mats x`), the noisy outcome probability is $`\sigma^{2G}\,\operatorname{Tr}(\rho_{\mathrm{ideal}}\,E_x) + (1 - \sigma^{2G})\,\frac{\operatorname{Tr}(E_x)}{2^n}`$. (For traceless Pauli observables $`P \ne I_N`$, $`\operatorname{Tr}(P) = 0`$, giving pure exponential damping $`\operatorname{Tr}(\rho_{\mathrm{noisy}}\,P) = \sigma^{2G}\,\operatorname{Tr}(\rho_{\mathrm{ideal}}\,P)`$.)

**Verified multi-target Grover search ($`M`$ marked items, `GroverCircuit.lean`):** For any target subset $`S \subseteq \mathrm{Fin}(2^n)`$ (`S : Finset (Fin (2 ^ n))`, including the degenerate cases $`S = \emptyset`$ and $`S = \mathrm{Finset.univ}`$) of cardinality $`M = |S|`$ (`S.card`), `GroverCircuit.lean` defines the cumulative subset measurement probability `subsetSuccProb n Ψ S` ($`= \sum_{w \in S} \operatorname{succProb}(n, \Psi, w)`$, linked to `computationalPOVM` via `subsetSuccProb_ketToReal_eq_born`) and proves both the pure-state trajectory mixture `noisyTrajectoryHet_subsetSuccProb` and the channel Born-rule mixture `noisyCircuitHet_subsetBornProb`:

$$
\mathrm{E}[p_{e,S}] = \sigma_{\mathrm{eff}}^2\thinspace p_{\mathrm{ideal},S} + \bigl(1 - \sigma_{\mathrm{eff}}^2\bigr)\thinspace\frac{M}{N}.
$$

Further, `GroverCircuit.lean` formalizes the $`M`$-target phase oracle `multiOracleMatrix S` / `multiOracleUnitary S` ($`O_S = I_N - 2\sum_{w \in S} |w\rangle\langle w|`$), the Grover iteration step `multiGroverStep S` ($`G_S = D \cdot O_S`$), the marked/unmarked plane states `multiTargetState S` and `multiNonTargetState S`, the exact 2D search-plane rotation `multiGrover_ketToReal_eq_plane`, the noiseless success probability `multiGrover_ideal_subsetSuccProb` (`multiGroverPSucc K n S.card` $`= \sin^2\bigl((2K + 1)\theta_{n,M}\bigr)`$ with `multiGroverHalfAngle n M` $`= \arcsin\sqrt{M/2^n}`$ for $`0 < M < 2^n`$, recovering `Grover.p_succ` at $`M = 1`$ via `multiGroverPSucc_one_eq_p_succ`), and the end-to-end heterogeneous noisy $`M`$-target Grover theorems `noisyMultiGroverHet_succProb` (unitary-step lists) and `noisyMultiGroverHet_circuit_bornProb` (syntactic `Circuit n`, instantiated on `grover2QubitCircuit` in `noisyGroverHet_circuit_grover2_bornProb`).

### 9.3 Verified Heterogeneous Gate-Type Fidelities via `Circuit.count` (`Sequential.lean`, `QuantumChannel.lean`)

In physical quantum processors, two-qubit entangling gates (`CNOT`, `SWAP`), three-qubit `TOFF` gates, and non-Clifford `T` gates have significantly different error rates than single-qubit Clifford gates (`X, Y, Z, H, S`). `Sequential.lean` formalizes heterogeneous schedules `steps : List ((E n ≃ₗᵢ[ℝ] E n) × ℝ)` with effective fidelity product `fidelityProd steps` and ideal state `idealGateTrajectoryHet steps Φ₀`, proving `noisyTrajectoryHet_eq_uniform`, `noisyTrajectoryHet_bilinear`, and `noisyTrajectoryHet_succProb` across all `∀ p ∈ steps, p.2 ∈ Set.Icc 0 1`.

In `QuantumComputation.Circuits.ResourceCounting`, `PrimitiveGate : ℕ → Type` is an arity-indexed inductive family ($`k \in \{1, 2, 3\}`$), and `Circuit.count g c` counts syntactic occurrences of each of the nine primitive gates $`\mathcal{G} = \{\mathrm{X}, \mathrm{Y}, \mathrm{Z}, \mathrm{H}, \mathrm{S}, \mathrm{T}, \mathrm{CNOT}, \mathrm{SWAP}, \mathrm{TOFF}\}`$, satisfying `Circuit.size_eq_sum_count`:

$$
c.\mathrm{size} = \sum_{g \in \mathcal{G}} c.\mathrm{count}(g).
$$

`QuantumChannel.lean` types per-gate fidelity assignments polymorphically as `σGate : ∀ {k}, PrimitiveGate k → ℝ` (with `hσ : ∀ {k} (g : PrimitiveGate k), σGate g ∈ Set.Icc 0 1`), defines `circuitFidelity σGate c`, `noisyCircuitChannelHet σGate hσ c`, `noisyTrajectoryExpectationℂHet`, and `circuitStepsHet σGate c`, and proves channel collapse `noisyCircuitChannelHet_eq` ($`= \Lambda_{\mathrm{circuitFidelity}(\sigma_{\mathrm{Gate}}, c)} \circ \mathcal{U}_{c.\mathrm{eval}}`$), trajectory-to-channel equivalence `noisyCircuitHet_trajectory_eq_channel`, Born-rule mixture `noisyCircuitHet_bornProb`, the explicit 9-gate factorization `circuitFidelity_eq_prod_count`, and the 1q/2q/3q arity-tier specialization `circuitFidelity_arity` (`gateCount1Q`, `gateCount2Q`, `gateCount3Q`, with `gateCount_sum_eq_size`):

$$
\sigma_{\mathrm{eff}}(c) = \prod_{g \in \mathcal{G}} \sigma_g^{\thinspace c.\mathrm{count}(g)}, \qquad \mathrm{E}[p_e] = \left(\prod_{g \in \mathcal{G}} \sigma_g^{\thinspace 2\thinspace c.\mathrm{count}(g)}\right) p_{\mathrm{ideal}} + \frac{1 - \prod_{g \in \mathcal{G}} \sigma_g^{\thinspace 2\thinspace c.\mathrm{count}(g)}}{2^n}.
$$

For example, on our verified 14-gate 2-qubit circuit `grover2QubitCircuit` (§7.3) — which contains $`c.\mathrm{count}(\mathrm{H}) = 10`$, $`c.\mathrm{count}(\mathrm{Z}) = 2`$, and $`c.\mathrm{count}(\mathrm{CNOT}) = 2`$ (`gateCount1Q = 12`, `gateCount2Q = 2`, `gateCount3Q = 0`) — heterogeneous per-gate noise yields $`\sigma_{\mathrm{H}}^{20}\sigma_{\mathrm{Z}}^{4}\sigma_{\mathrm{CNOT}}^{4} + \frac{1 - \sigma_{\mathrm{H}}^{20}\sigma_{\mathrm{Z}}^{4}\sigma_{\mathrm{CNOT}}^{4}}{4}`$, reducing immediately to $`\sigma^{28} + \frac{1 - \sigma^{28}}{4}`$ when $`\sigma_{\mathrm{H}} = \sigma_{\mathrm{Z}} = \sigma_{\mathrm{CNOT}} = \sigma`$.

---

## <a name="references">References</a>

- L. K. Grover, "A fast quantum mechanical algorithm for database search," *Proc. 28th Annual ACM Symposium on Theory of Computing (STOC)*, pp. 212–219, 1996. [arXiv:quant-ph/9605043](https://arxiv.org/abs/quant-ph/9605043) · [DOI:10.1145/237814.237866](https://doi.org/10.1145/237814.237866)
- J. Lacalle and L. M. Pozo Coronado, "Variance of the sum of independent quantum computing errors," *Quantum Information and Computation*, vol. 19, no. 15–16, pp. 1294–1312, 2019. [DOI:10.26421/QIC19.15-16-3](https://doi.org/10.26421/QIC19.15-16-3)
- S. Axler, P. Bourdon, and W. Ramey, *Harmonic Function Theory*, 2nd ed., Graduate Texts in Mathematics vol. 137, Springer, 2001. [DOI:10.1007/978-1-4757-8137-3](https://doi.org/10.1007/978-1-4757-8137-3) (Ch. 5: Poisson kernel and harmonic representation on the Euclidean ball.)
- R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley Series in Probability and Statistics, Wiley, New York, 1982. [DOI:10.1002/9780470316559](https://doi.org/10.1002/9780470316559) (Second-moment operator of the uniform spherical distribution.)
- K. V. Mardia and P. E. Jupp, *Directional Statistics*, Wiley Series in Probability and Statistics, Wiley, Chichester, 2000. [DOI:10.1002/9780470316979](https://doi.org/10.1002/9780470316979) (Moments and reflection symmetries of uniform distributions on spheres.)
- A. Meiburg, L. A. Lessa, and R. R. Soldati, "A Formalization of the Generalized Quantum Stein's Lemma in Lean," 2025 (`QuantumInfo` in `Physlib`: `Ket`, `MState`, `CPTPMap`, `POVM`, `HermitianMat`). [arXiv:2510.08672](https://arxiv.org/abs/2510.08672) · [GitHub:leanprover-community/physlib](https://github.com/leanprover-community/physlib)
- S. Shirobokov, B. Jaderberg, K. Hristova, G. Tsoukalas, J. Bausch, E. Wieser, F. J. H. Heras, N. C. Rubin, G. H. Low, S. Racanière, N. Tomašev, L. M. Zhang, J. D. Watson, T. Khattar, A. Albarghouthi, S. Jain, H. Khan, L. Sarra, A. W. Senior, M. Broughton, H. Masoom, S. Boixo, R. Babbush, S. Chaudhuri, and P. Kohli, "Discovering formally verified quantum programs with AI," 2026 (`QuantumComputation` in `formal-quantum-computation`: `Circuit`, `Circuit.size`, `Circuit.count`, `Grover`). [arXiv:2611.09822](https://arxiv.org/abs/2611.09822) · [GitHub:google-deepmind/formal-quantum-computation](https://github.com/google-deepmind/formal-quantum-computation)
