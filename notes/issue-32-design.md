# Issue #32 Design Document: Final Codebase Hygiene & End-to-End Exposition in `english-proof.md` and `README.md`

## Problem Context
With Issues #28–#31 merged, the Lean 4 formalization has:
- **Zero `sorry`s** and **zero non-standard kernel axioms** (`[propext, Classical.choice, Quot.sound]`, enforced in CI by `axiom-audit` and `#guard_msgs in #print axioms`).
- **Zero definitional shortcuts**: microscopic isotropic pure-state perturbations on $S^{2 \cdot 2^n - 1}$ are bridged isometrically to `Physlib` (`QuantumInfo`: `Ket`, `MState`, `CPTPMap`, `POVM`) and `google-deepmind/formal-quantum-computation` (`QuantumComputation`: `Circuit`, `Circuit.size`, `Grover`), covering all $\sigma \in [0, 1]$ and $G, K, n \in \mathbb{N}$.

However, minor cross-module cleanup opportunities remain in `IsotropicGroverProof/` (redundant root barrel imports, stale pre-#29/#30 header comments, repeated `2 ≤ d n` proofs), and both `english-proof.md` and `README.md` still reflect the older pre-`QuantumInfo` / static-vector exposition.

## Design

### 1. Whole-Codebase Hygiene & Simplification (`IsotropicGroverProof.lean`, `IsotropicGroverProof/*.lean`)
- Simplify `IsotropicGroverProof.lean` to `import IsotropicGroverProof.Basic` (removing duplicate `Sequential` and `GroverCircuit` imports already included in `Basic.lean`).
- Remove stale historical header comments (e.g., `MainTheorem.lean`'s `"All sorrys are in dependencies"`, outdated `"M3: ..."` notes) and replace remaining inline `2 ≤ d n` proofs with `two_le_d n` from `Defs.lean`.
- Ensure comprehensive `#guard_msgs in #print axioms` guards across all headline theorems (`MainTheorem`, `Sequential`, `LimitingCases`, `QuantumChannel`, `GroverCircuit`).

### 2. End-to-End Natural Language Proof Rewrite (`english-proof.md`)
Rewrite `english-proof.md` into a clear, self-contained, gap-free, and extensible 9-section mathematical exposition with explicit 1-to-1 theorem citations into `IsotropicGroverProof/`:
- **Executive Summary & Formalization Map:** Boxed theorem statement across $\sigma \in [0, 1]$ and $n, G \in \mathbb{N}$, plus a roadmap table mapping each mathematical step to its Lean module and verified theorem names.
- **§1 — Complex Quantum States, Born-Rule Measurement, and the $\mathbb{C}^{2^n} \cong \mathbb{R}^{2 \cdot 2^n}$ Isomorphism** (`Defs.lean`, `QuantumChannel.lean`).
- **§2 — Microscopic Single-Gate Isotropic Error Model Across $\sigma \in [0, 1]$** (`IsotropicError.lean`).
- **§3 — Exact First and Second Moments of the Poisson Marginal: Harmonic Intuition and 1D FTC Induction Proof** (`IsotropicError.lean`, `Gegenbauer.lean`).
- **§4 — Equatorial Sphere Symmetry and the Full Real Bilinear Second-Moment Operator** (`CrossTerm.lean`, `SecondMoment.lean`).
- **§5 — Emergence of the Complex Quantum Depolarizing Channel (`CPTPMap`)** (`QuantumChannel.lean`), showing explicitly how even/odd coordinate orthogonality cancels imaginary cross-noise terms and yields $\Lambda_\sigma(\rho) = \sigma^2\rho + (1-\sigma^2)\frac{I_N}{N}$.
- **§6 — Multi-Gate Noisy Circuits: Pure-State Markov Trajectories, Unitary Channel Commutation, and Syntactic `Circuit.size`** (`Sequential.lean`, `QuantumChannel.lean`).
- **§7 — Specialization to Grover's Algorithm and Concrete Primitive-Gate Circuits** (`GroverCircuit.lean`), covering $K$-iteration dynamics $p_\mathrm{succ}(K, 2^n) = \sin^2((2K+1)\arcsin(2^{-n/2}))$, canonical macro-gate lists, arbitrary gate decompositions, syntactic `Circuit n` ($G = c.\mathrm{size}$), and the verified 1-qubit and 14-gate 2-qubit (`grover2QubitCircuit`) examples.
- **§8 — Limiting Regimes, Monotonicity, and Downstream Repetition Overhead** (`LimitingCases.lean`).
- **§9 — Extensibility Guide:** How the verified architecture generalizes out-of-the-box to arbitrary algorithms in `formal-quantum-computation` (`Circuit n`), general `HermitianMat` observables / multi-target `POVM`s, and gate-type-dependent error rates $\prod_g \sigma_g^{2 \cdot c.\mathrm{count}(g)}$ via `Circuit.count`.

### 3. `README.md` Update
Update `README.md` to accurately present the verified scope, dependency stack (`Lean v4.35.0`, `Mathlib`, `Physlib`/`QuantumInfo`, `formal-quantum-computation`), headline theorems across all layers, zero-custom-axiom CI `axiom-audit` verification, complete module map (including `QuantumChannel.lean`), and build instructions.
