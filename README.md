# isotropic-grover-proof

This is an attempt to formalise a proof for studying the impact of Isotropic Errors on Grover's Algorithm using Lean 4, Mathlib and agentic AI tools. 

## Goal

We want a closed-form expression for $\mathrm{E}[p_e(n)]$, the **expected success probability** of Grover's algorithm on $n$ qubits when every gate is subject to an independent isotropic error with per-gate fidelity parameter $\sigma \in (0,1)$. Once we have this, the repetition overhead

$$k(n) = \frac{\log(1-p_\mathrm{ideal})}{\log(1-\mathrm{E}[p_e])}$$

can be fit as an exponential in $n$.

The result we will derive is the mixture model

$$\boxed{\mathrm{E}[p_e] = \sigma^{2G(n)} \cdot p_\mathrm{ideal} + \frac{1-\sigma^{2G(n)}}{N},}$$

where $N = 2^n$ is the database size and $G(n)$ is the gate count at optimal Grover iterations (taken directly from simulation data). This formula is **exact** for the isotropic error model — no approximations are made and all finite-size corrections cancel.

More details are available in [english-proof.md](english-proof.md).

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
