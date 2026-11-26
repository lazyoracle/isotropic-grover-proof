# Issue #30 Design Document: Bridge Isotropic Sphere Errors to `QuantumInfo` `CPTPMap` and `QuantumComputation` `Circuit.size`

## Problem Context
With non-standard kernel axioms eliminated in #29, four structural "axioms by definition" remain:
1. `Defs.lean` encodes $n$-qubit states as real vectors in `E n = EuclideanSpace ℝ (Fin (2 * 2^n))` with coordinate-pair `succProb`, without machine-checking equivalence to complex `Ket (Fin (2^n))`, `MState.pure`, or Born-rule `POVM` / `compProjObs` measurement.
2. `Composition.lean` retains the deprecated tautology `isotropicComposition := rfl` and defines multi-gate composition `composedMeasure d G σ := poissonMarginal d (σ ^ G)` by fiat.
3. `Sequential.lean` proves only a scalar recurrence on `ℝ`, disconnected from `Measure (E n)` transitions and interleaved gates.
4. Theorems restrict to `0 < G` and `σ ∈ Set.Ioo 0 1`, and `G` is an external free parameter rather than derived from syntactic circuits (`Circuit.size`).

## Architecture & Mathematical Design

### 1. Full `[0, 1]` Parameter Domain & Bilinear Second-Moment Operator (`IsotropicError.lean`, `Composition.lean`, `SecondMoment.lean`)
- Define `poissonAngleMeasure (d : ℕ) (σ : ℝ) : Measure ℝ := if σ = 1 then Measure.dirac 0 else poissonMarginal d σ`.
  - For $\sigma = 1$: `Measure.dirac 0` gives $\theta = 0$ ($\Psi' = \Psi$), $\mathbb{E}[\cos\theta] = 1$, $\mathbb{E}[\cos^2\theta] = 1$.
  - For $\sigma = 0$: `poissonKernelDensity d 0 θ = sin θ ^ (d - 2)`, so `poissonMarginal d 0` is already the exact Haar polar marginal on $[0, \pi]$ with $\mathbb{E}[\cos\theta] = 0$ (antiderivative $\frac{\sin^{d-1}\theta}{d-1}$) and $\mathbb{E}[\cos^2\theta] = 1/d$ (antiderivative $\sin^{d-1}\theta\cos\theta$).
  - For $\sigma \in (0, 1)$: coincides with `poissonMarginal d σ`.
  Thus `IsProbabilityMeasure`, $\mathbb{E}[\cos\theta] = \sigma$, and $\mathbb{E}[\cos^2\theta] = \frac{(d-1)\sigma^2+1}{d}$ hold uniformly for **all `σ ∈ Set.Icc 0 1`** and `2 ≤ d`.
- Remove the deprecated `isotropicComposition := rfl` stub from `Composition.lean`.
- Prove the **general bilinear second-moment identity** on `E n` (`SecondMoment.lean`) for any unit `‖Ψ‖ = 1`, `σ ∈ Set.Icc 0 1`, and arbitrary `u v : E n`:
  $$\int \theta,\, \int e_2,\, \langle \mathrm{isotropicError}\,\Psi\,e_2\,\theta, u \rangle_{\mathbb{R}} \langle \mathrm{isotropicError}\,\Psi\,e_2\,\theta, v \rangle_{\mathbb{R}} \, \partial(\mathrm{perpSphereMeasure}\,\Psi) \, \partial(\mathrm{poissonAngleMeasure}\,(d\,n)\,\sigma) = \sigma^2 \langle \Psi, u \rangle_{\mathbb{R}} \langle \Psi, v \rangle_{\mathbb{R}} + \frac{1 - \sigma^2}{d\,n} \langle u, v \rangle_{\mathbb{R}}.$$

### 2. Measure-Theoretic Pure-State Markov Chain Over Interleaved Gates (`Sequential.lean`, `LimitingCases.lean`)
- For any list of orthogonal/unitary gates `gates : List (E n ≃ₗᵢ[ℝ] E n)`, define the ideal noiseless output `idealGateTrajectory gates Φ₀ := gates.foldl (fun v U => U v) Φ₀` (alongside its composite linear isometry `idealGateIso gates`), and define the recursive iterated-integral Markov expectation `noisyTrajectoryExpectation (n : ℕ) (σ : ℝ) : List (E n ≃ₗᵢ[ℝ] E n) → E n → (E n → ℝ) → ℝ` (plus `noisyTrajectoryExpectationℂ` on `E n → ℂ` in `QuantumChannel.lean`):
  - `[] => fun Φ₀ f => f Φ₀`
  - `U :: rest => fun Φ₀ f => ∫ θ, ∫ e₂, noisyTrajectoryExpectation n σ rest (isotropicError (U Φ₀) e₂ θ) f ∂(perpSphereMeasure (U Φ₀)) ∂(poissonAngleMeasure (d n) σ)`
  *(Formulating the Markov chain directly via iterated integrals over `(poissonAngleMeasure, perpSphereMeasure)` at each gate step avoids non-measurable `Classical.choice` basis selection in `Ψ ↦ perpSphereMeasure Ψ` while faithfully tracking `Ψ_{k+1} = cos θ_{k+1} (U_{k+1} Ψ_k) + sin θ_{k+1} e_{2,k+1}`.)*
- Prove by induction on `gates` (for all `G = gates.length : ℕ`, including `G = 0`, and all `σ ∈ Set.Icc 0 1`):
  1. Unit-sphere support and regularity (`noisyTrajectory_congr_unitSphere`, `noisyTrajectoryExpectation_continuousOn_unitSphere`, and linearity): when `‖Φ₀‖ = 1`, `noisyTrajectoryExpectation` evaluates observables a.e. on the unit sphere `‖Ψ‖ = 1` and preserves `ContinuousOn` on `Metric.sphere 0 1`.
  2. Bilinear expectation after `gates` (`noisyTrajectory_bilinear`): `noisyTrajectoryExpectation n σ gates Φ₀ (fun Ψ => ⟪Ψ, u⟫_ℝ * ⟪Ψ, v⟫_ℝ) = σ ^ (2 * G) * (⟪Φ_G, u⟫_ℝ * ⟪Φ_G, v⟫_ℝ) + (1 - σ ^ (2 * G)) / (d n) * ⟪u, v⟫_ℝ`, where `Φ_G = idealGateTrajectory gates Φ₀`.
  3. Squared overlap with $\Phi_G$ (`noisyTrajectory_fidelity_eq_sequentialFidelity`) equals `sequentialFidelity (d n) σ gates.length`.
  4. Expected `succProb n Ψ w` (`noisyTrajectory_succProb`) equals $\sigma^{2G} \cdot \mathrm{succProb}\,n\,\Phi_G\,w + \frac{1 - \sigma^{2G}}{2^n}$.
- Connect `LimitingCases.lean` to the `[0, 1]` closed-interval formulation so $\sigma = 0, 1$ and $G = 0$ hold both by evaluation and by continuity.

### 3. `QuantumInfo` `CPTPMap` Depolarizing Bridge & `QuantumComputation` `Circuit.size` (`IsotropicGroverProof/QuantumChannel.lean`)
- **Complex ↔ Real bridge:** Define mutual bijections `vecToReal : (Fin (2^n) → ℂ) → E n` and `realToVec : E n → (Fin (2^n) → ℂ)` (`realToVec n Φ x = ⟨Φ (succProbIdx0 n x), Φ (succProbIdx1 n x)⟩`), lifting to `ketToReal : Ket (Fin (2^n)) → E n` (`‖ketToReal ψ‖ = 1`), `realToKet`, and `unitaryToRealIso : 𝐔[Fin (2^n)] → (E n ≃ₗᵢ[ℝ] E n)`.
- **Born-rule & `POVM` equivalence:** Define `computationalPOVM n : POVM (Fin (2^n)) (Fin (2^n))` (`mats w := (compProjObs w).1`) and prove `succProb n (ketToReal ψ) w = ‖ψ w‖ ^ 2 = ((MState.pure ψ).m w w).re = (MState.pure ψ).exp_val (compProjObs w).1 = ((computationalPOVM n).measure (MState.pure ψ) w : ℝ)`.
- **Depolarizing `CPTPMap` emergence:** Define `depolarizingChannel n σ hσ : CPTPMap (Fin (2^n)) (Fin (2^n))` acting as $\rho \mapsto \sigma^2 \rho + (1 - \sigma^2)\,\mathrm{MState.uniform}$ for `σ ∈ Set.Icc 0 1`. Using the bilinear second-moment theorem on `E n` (where odd/even index cross-deltas vanish identically!), prove that averaging the rank-1 density matrix `pureDensityMatrix n Ψ'` over one isotropic sphere error step equals `(depolarizingChannel n σ hσ (MState.pure ψ)).m` entrywise, and after a list of unitaries `us : List 𝐔[Fin (2^n)]` equals `(depolarizingChannel n (σ ^ us.length) ... (MState.pure ψ_G)).m`.
- **Channel algebra & `Circuit.size` theorem:**
  - Prove `depolarizingChannel_comm_ofUnitary`: `depolarizingChannel n σ hσ ∘ₘ CPTPMap.ofUnitary U = CPTPMap.ofUnitary U ∘ₘ depolarizingChannel n σ hσ`.
  - Prove `depolarizingChannel_compose`: `depolarizingChannel n σ₁ hσ₁ ∘ₘ depolarizingChannel n σ₂ hσ₂ = depolarizingChannel n (σ₁ * σ₂) hσ₁₂`.
  - Define `noisyCircuitChannel (σ : ℝ) (hσ : σ ∈ Set.Icc 0 1) : Circuit n → CPTPMap (Fin (2^n)) (Fin (2^n))` applying `depolarizingChannel n σ hσ` after each primitive gate `.gate g r`, and prove by structural induction on `c : Circuit n`:
    $$\mathrm{noisyCircuitChannel}\,\sigma\,h\sigma\,c = \mathrm{depolarizingChannel}\,n\,(\sigma^{c.\mathrm{size}})\,\dots \circ_{\mathrm{m}} \mathrm{CPTPMap.ofUnitary}\,c.\mathrm{eval},$$
    yielding exact Born-rule outcome probability $\sigma^{2 \cdot c.\mathrm{size}} \cdot p_{\mathrm{ideal}} + \frac{1 - \sigma^{2 \cdot c.\mathrm{size}}}{2^n}$ where the gate count $G = c.\mathrm{size}$ is machine-computed by `Circuit.size`!
