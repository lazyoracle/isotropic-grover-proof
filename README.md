# isotropic-grover-proof

A zero-custom-axiom **Lean 4** formalization of the exact expected success probability of noisy $n$-qubit quantum circuits and Grover's database search algorithm under microscopic isotropic pure-state gate errors, bridging real spherical geometry (`Mathlib`) to `Physlib`'s `QuantumInfo` (`Ket`, `MState`, `CPTPMap`, `POVM`) and `google-deepmind/formal-quantum-computation` (`Circuit`, `Circuit.size`, `Grover`).

## Overview & Main Result

When an $n$-qubit quantum computation on Hilbert space $\mathbb{C}^{2^n}$ ($N = 2^n$, real unit-sphere dimension $d = 2N = 2^{n+1}$) executes $G \in \mathbb{N}$ gates — each followed by an independent isotropic pure-state sphere perturbation of fidelity parameter $\sigma \in [0, 1]$ — all intermediate finite-dimensional factors ($d$ and $d - 1$) cancel algebraically, yielding the exact convex mixture formula:

$$\boxed{\mathrm{E}[p_e] = \sigma^{2G}\,p_\mathrm{ideal} + \frac{1 - \sigma^{2G}}{N}, \qquad N = 2^n, \quad \sigma \in [0, 1], \quad G, n \in \mathbb{N},}$$

where $p_\mathrm{ideal} = |\langle w | \psi_\mathrm{ideal}\rangle|^2$ is the noiseless Born-rule probability of computational-basis outcome $w \in \mathrm{Fin}(2^n)$.

- **General gate lists vs. syntactic `Circuit.size`:** In trajectory theorems (`Sequential.lean`), $G = \texttt{gates.length}$ counts interleaved isometric gate stages; in syntactic circuit theorems (`QuantumChannel.lean`, `GroverCircuit.lean`), $G = c.\mathrm{size}$ is computed directly from the primitive-gate AST `c : Circuit n` (`X, Y, Z, H, S, T, CNOT, SWAP, TOFF`).
- **Grover's search algorithm ($K \in \mathbb{N}$ iterations):** Specializing to `formal-quantum-computation`'s Grover phase oracle and diffuser yields $p_\mathrm{ideal} = \mathrm{Grover.p\_succ}(K, 2^n) = \sin^2\bigl((2K + 1)\arcsin(2^{-n/2})\bigr)$, proved for macro-operator sequences ($G = 2K$ and $G = 2K + 1$), arbitrary unitary gate lists, syntactic `Circuit n` implementations ($G = c.\mathrm{size}$), and concrete 1- and 2-qubit primitive-gate circuits.
- **Downstream applications (outside the Lean formalization):** Once $\mathrm{E}[p_e]$ is established, the multi-run repetition overhead $k(n) = \frac{\log(1 - p_\mathrm{ideal})}{\log(1 - \mathrm{E}[p_e])}$ required for $k$ independent runs to succeed with cumulative probability $p_\mathrm{ideal}$ can be evaluated at transpiled empirical gate counts $G(n)$ (or asymptotic scalings $G(n) \propto \frac{\pi}{4}\sqrt{2^n}$) and fit to $a \cdot b^n + c$.

A self-contained mathematical exposition with explicit 1-to-1 Lean theorem cross-references and extensibility recipes is provided in **[english-proof.md](english-proof.md)**.

---

## Proved Theorem Layers

### 1. Geometric Sphere & Poisson Moment Engine (`Defs.lean`, `IsotropicError.lean`, `Composition.lean`, `CrossTerm.lean`, `SecondMoment.lean`, `Gegenbauer.lean`, `MainTheorem.lean`)
- **Closed-interval angle measure & exact 1D FTC moments (`IsotropicError.lean`, `Gegenbauer.lean`):** Defines `poissonAngleMeasure d σ` across $\sigma \in [0, 1]$ (coinciding with `poissonMarginal d σ` on $[0, 1)$ — including the uniform Haar polar marginal at $\sigma = 0$ — and `Measure.dirac 0` at $\sigma = 1$). Proves `poissonAngleMeasure_mean_cos` ($\mathrm{E}[\cos\theta] = \sigma$) and `poissonAngleMeasure_cos_sq` ($\mathrm{E}[\cos^2\theta] = \frac{(d - 1)\sigma^2 + 1}{d}$, along with `poissonIntegral_cos_sq` on $(0, 1)$) for all $d \ge 2$ via 1D Fundamental Theorem of Calculus recurrences and two-step induction $d \mapsto d + 2$ from $d = 2$ and $d = 3$, plus harmonic polynomial identities (`laplacian_trace_cancellation`, `harmonicExtension_boundary`, `harmonicExtension_eval`).
- **Equatorial reflection symmetries & bilinear operator (`CrossTerm.lean`, `SecondMoment.lean`):** Constructs the Haar-induced equatorial probability measure `perpSphereMeasure` on $V_\perp(\Psi) \cap S^{d-1}$, proves antipodal cross-term vanishing (`integral_perp_inner_eq_zero`), orthogonal/Householder second-moment symmetry `perpSphere_inner_mul_inner` ($\mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top] = \frac{P_\perp}{d - 1}$), and exact single-step $(d - 1)$ cancellation in `isotropicError_bilinear_secondMoment` and `isotropicError_succProb_oneStep` across $\sigma \in [0, 1]$.
- **Single-effective-error mixture theorem (`MainTheorem.lean`):** `isotropicGrover_main` (and `n = 0` specialization `isotropicGrover_n0`) proves the $\sigma^{2G}$ mixture formula under `composedMeasure (d n) G σ` for all $n \in \mathbb{N}$, $G > 0$, and $\sigma \in (0, 1)$.

### 2. Multi-Gate Pure-State Markov Trajectories (`Sequential.lean`)
- **Scalar fidelity recurrence:** Solves $f_0 = 1$, $f_{k+1} = \lambda f_k + (1 - \lambda)\frac{1 - f_k}{d - 1}$ ($\lambda =$ `stepLambda d σ`) via geometric contraction `stepTransition_sub_inv_d` to obtain $f_k = \frac{(d - 1)\sigma^{2k} + 1}{d}$ (`sequentialFidelity_eq`, `sequentialFidelity_eq_f₂`, `sequential_mixture_formula`).
- **Interleaved isometric Markov chain:** Defines the $G$-fold pure-state expectation `noisyTrajectoryExpectation` over arbitrary gate lists `gates : List (E n ≃ₗᵢ[ℝ] E n)` where each error rotates around the instantaneous perturbed state $U_k\Psi_{k-1}$. Using Householder measure transport on $S^{d-1}$ and adjoint pullback, proves `noisyTrajectory_bilinear`, `noisyTrajectory_fidelity_eq_sequentialFidelity`, and `noisyTrajectory_succProb` across all $\sigma \in [0, 1]$ and all `gates` (including `gates = []`) with **no** spherical-angle convolution assumption.

### 3. `QuantumInfo` Depolarizing `CPTPMap` & Syntactic `Circuit.size` Bridge (`QuantumChannel.lean`)
- **Hilbert-space & Born-rule isomorphism:** Bridges `Ket (Fin (2 ^ n))` and unitaries `𝐔[Fin (2 ^ n)]` isometrically to `E n` (`vecToReal`, `realToVec`, `ketToReal`, `realToKet`, `unitaryToRealIso`) and proves 5-way Born-rule equivalence `succProb_ketToReal_eq_born` between `succProb`, squared ket amplitudes, `MState.pure` diagonals, `MState.exp_val (compProjObs w).1`, and `computationalPOVM`.
- **Emergence of the complex depolarizing channel:** Constructs `depolarizingChannel n σ hσ : CPTPMap (Fin (2 ^ n)) (Fin (2 ^ n))` (`ρ ↦ σ² ρ + (1 - σ²) MState.uniform`) for $\sigma \in [0, 1]$ and proves in `isotropicOneStep_eq_depolarizingChannel` and `noisyTrajectory_eq_depolarizingChannel` that averaging the rank-1 density matrix `pureDensityMatrix` over microscopic real-sphere isotropic errors produces `depolarizingChannel` entrywise.
- **Channel commutation, semigroup, and `Circuit.size`:** Proves unitary commutation `depolarizingChannel_comm_ofUnitary`, multiplicative composition `depolarizingChannel_compose`, syntactic circuit collapse `noisyCircuitChannel_eq` ($\mathrm{noisyCircuitChannel}(\sigma, c) = \Lambda_{\sigma^{c.\mathrm{size}}} \circ \mathcal{U}_{c.\mathrm{eval}}$), trajectory-to-channel equivalence (`noisyCircuit_trajectory_eq_channel`, `noisyCircuit_trajectory_succProb_eq_measure`), and Born-rule mixture theorems `noisyCircuit_bornProb` and `noisyCircuit_bornProb_pure`.

### 4. End-to-End Grover's Algorithm & Concrete Primitive-Gate Circuits (`GroverCircuit.lean`)
- **Static 2D search-plane specializations ($\sigma \in (0, 1),\, G > 0$):** Formalizes `targetBasisState`, `targetPerpState`, `uniformSuperposition`, `groverState2D`, and `groverState2D_prob`, wrapping `isotropicGrover_main` to prove `isotropicGrover_uniformSuperposition` and `isotropicGrover_targetBasisState` for all $n \in \mathbb{N}$, and `isotropicGrover_groverState2D` and `isotropicGrover_groverState2D_prob` for `1 < 2 ^ n` ($n \ge 1$; full $\sigma \in [0, 1],\, G \in \mathbb{N}$ coverage holds via `noisyTrajectory_succProb` and `noisyGrover_iterGates_succProb` at $K = 0$).
- **Dynamic $K$-iteration Grover bridge:** Connects `Grover.oracleUnitary`, `Grover.diffuserUnitary`, and `hadamardUnitary` (`groverIterGates`, `groverFullGates`, `unitaryListProd`) to `Grover.groverMatrix`, `Grover.groverState`, and `Grover.p_succ` (`idealUnitaryTrajectory_groverIterGates`, `idealUnitaryTrajectory_groverFullGates`, `groverState_bornProb`).
- **Noisy Grover theorems across $\sigma \in [0, 1]$:** Proves both `computationalPOVM` Born-probability and pure-state trajectory theorems for $K$ macro-iterations (`G = 2 * K`: `noisyGrover_iterGates_bornProb`, `noisyGrover_iterGates_succProb`), noisy state preparation + $K$ iterations (`G = 2 * K + 1`: `noisyGrover_fullGates_bornProb`, `noisyGrover_fullGates_succProb`), arbitrary unitary decompositions (`noisyGrover_unitaryList_bornProb`, `noisyGrover_unitaryList_succProb`), and syntactic `Circuit n` implementations (`G = c.size`: `noisyGrover_circuit_bornProb`, `noisyGrover_circuit_groverMatrix_bornProb`).
- **Concrete primitive-gate circuit witnesses:**
  - *1-qubit Hadamard (`K = 0`, `c.size = 1`):* `Circuit.H (0 : Wire 1)` (`noisyGrover_circuit_hadamard1_bornProb`, evaluating to $\sigma^2 \cdot \mathrm{Grover.p\_succ}(0, 2) + (1 - \sigma^2)/2 = 1/2$).
  - *14-gate 2-qubit Grover search (`K = 1`, `c.size = 14`, target `3` = $|11\rangle$):* `grover2QubitCircuit` built from primitive `H`, `Z`, and `CNOT` gates (`grover2QubitCircuit_eval_val`, `p_succ_one_four`), yielding exact noisy Born probability $\sigma^{28} + (1 - \sigma^{28}) / 4$ (`noisyGrover_circuit_grover2_bornProb`).

### 5. Limiting Regimes, Monotonicity & Closed-Interval Continuity (`LimitingCases.lean`)
- Connects `mixtureProb` to both `isotropicGrover_main` (`isotropicGrover_lhs_eq_mixtureProb`) and `noisyTrajectory_succProb` (`noisyTrajectory_succProb_eq_mixtureProb`).
- Proves monotonicity in effective fidelity for $p_\mathrm{ideal} \ge 1/N$ (`mixtureProb_mono`), continuity across $\sigma \in [0, 1]$ (`continuousOn_noisyTrajectory_succProb`), exact endpoint evaluations (`noisyTrajectory_succProb_at_sigma_one`, `noisyTrajectory_succProb_at_sigma_zero` for `gates ≠ []` ($G \ge 1$), and `noisyTrajectory_succProb_nil`), and filter limits as $\sigma \to 1$ and $\sigma \to 0$ (`tendsto_noisyTrajectory_succProb_sigma_one`, `tendsto_noisyTrajectory_succProb_sigma_zero` for `gates ≠ []` ($G \ge 1$), and `tendsto_expectedSuccProb_as_sigma_one` / `tendsto_expectedSuccProb_as_sigma_zero` on $\sigma \in (0, 1)$ with $G > 0$).

---

## Dependencies

Pinned in [`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml):
- **Lean 4:** `leanprover/lean4:v4.35.0`
- **Mathlib:** [`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4) (`v4.35.0`)
- **Physlib (`QuantumInfo`):** [`leanprover-community/physlib`](https://github.com/leanprover-community/physlib) (`v4.35.0`)
- **Formal Quantum Computation (`QuantumComputation`):** [`google-deepmind/formal-quantum-computation`](https://github.com/google-deepmind/formal-quantum-computation) (`rev 489edc7039aa4cdded53724b39ea90e33d2c88b4`)

---

## Axiom Footprint & CI Verification

Every theorem in this repository is proved with **zero `sorry`s** and **zero custom axioms**, depending solely on Lean's three standard foundational axioms:
- `propext`, `Classical.choice`, `Quot.sound`

This guarantee is enforced in two ways:
1. **Compile-time `#guard_msgs in #print axioms` checks** across all modules (`Defs.lean`, `IsotropicError.lean`, `Composition.lean`, `CrossTerm.lean`, `SecondMoment.lean`, `Gegenbauer.lean`, `Sequential.lean`, `MainTheorem.lean`, `LimitingCases.lean`, `QuantumChannel.lean`, `GroverCircuit.lean`).
2. **GitHub Actions CI (`.github/workflows/lean_action_ci.yml`):** Runs `leanprover/lean-action@v1` with `build-args: '--wfail'`, `axiom-audit: true`, and `axiom-audit-root: 'IsotropicGroverProof'`, auditing every declaration transitively imported by `IsotropicGroverProof.lean` → `IsotropicGroverProof/Basic.lean`.

---

## Repository Structure

- `english-proof.md` — Complete end-to-end mathematical derivation, Lean formalization map, and extensibility guide (§1–§9).
- `IsotropicGroverProof.lean` — Root library entry point importing `IsotropicGroverProof.Basic`.
- `IsotropicGroverProof/` — Barrel module `Basic.lean` plus 11 verified submodules:
  ```text
  Basic.lean          — Barrel module importing all 11 submodules in dependency order
  Defs.lean           — Ambient space E n = ℝ^{2·2^n}, basis vectors, dimension lemmas, succProb, Parseval
  IsotropicError.lean — Poisson marginal density, closed-interval poissonAngleMeasure, 1D FTC moments, isotropicError
  Composition.lean    — Effective σ^G angle measure composedMeasure and second moment f₂
  CrossTerm.lean      — Equatorial sphere measure perpSphereMeasure, reflection symmetries, expanded_E_pe
  SecondMoment.lean   — Projector P_perp, E[e₂e₂ᵀ] = P_perp/(d-1), decoherent_floor, isotropicError_bilinear_secondMoment
  Gegenbauer.lean     — Harmonic-extension polynomial identities, poissonIntegral_cos_sq, f₂_formula
  Sequential.lean     — Fidelity recurrence sequentialFidelity_eq and multi-gate Markov trajectory noisyTrajectory_succProb
  MainTheorem.lean    — Effective-measure mixture theorem isotropicGrover_main and isotropicGrover_n0
  LimitingCases.lean  — mixtureProb, monotonicity, [0, 1] continuity, and noiseless/decoherent limits
  QuantumChannel.lean — QuantumInfo CPTPMap depolarizingChannel, POVM bridge, and syntactic Circuit.size theorems
  GroverCircuit.lean  — Grover search plane, Grover.p_succ bridge, and 1- & 2-qubit primitive-gate circuits
  ```
- `notes/` — Design specifications and implementation plans for completed issues.
- `sessions/` — Proof engineering and review logs.

---

## Building and Checking

Install [`elan`](https://leanprover-community.github.io/get_started.html), fetch the precompiled Mathlib cache, and build with warnings treated as errors:

```bash
lake exe cache get && lake build --wfail
```
