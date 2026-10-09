# Issue #12 Design Document: Connect Limiting Cases Theorems to `isotropicGrover_main`

## Problem Context
`IsotropicGroverProof/LimitingCases.lean` defined `mixtureProb p N f := f * p + (1 - f) / N` and proved:
- `tendsto_ideal_as_fidelity_one`: `Tendsto (mixtureProb p N) (𝓝 1) (𝓝 p)`
- `tendsto_random_as_fidelity_zero`: `Tendsto (mixtureProb p N) (𝓝 0) (𝓝 (1 / N))`

These were proved only for the abstract real function `mixtureProb` and were not formally connected to `isotropicGrover_main` from `IsotropicGroverProof/MainTheorem.lean`, nor to the nested integral representing the expected success probability under isotropic gate noise:
$$\int_\theta \int_{e_2} p_\mathrm{succ}(\mathcal{E}(\Phi, e_2, \theta)) \, \partial(\mu_{\Phi^\perp}) \, \partial(\mu_{composed}).$$

## Goals
1. Connect the RHS and LHS of `isotropicGrover_main` directly to `mixtureProb`.
2. Connect limiting behaviors to `isotropicGrover_main`:
   - Specialization of `mixtureProb` limits to the Grover setting with $p = \mathrm{succProb}\ n\ \Phi\ w$ and $N = 2^n$.
   - Continuity and limits as per-gate parameter $\sigma \to 1$ and $\sigma \to 0$.
   - Rigorous convergence of the actual expected success probability nested integral as $\sigma \to 1^-$ and $\sigma \to 0^+$ (or in $\mathcal{N}_{(0,1)}(1)$ and $\mathcal{N}_{(0,1)}(0)$).

## Proposed Additions to `IsotropicGroverProof/LimitingCases.lean`
1. **Connection Lemmas:**
   - `isotropicGrover_rhs_eq_mixtureProb`: Shows that the RHS of `isotropicGrover_main` is definitionally/algebraically equal to `mixtureProb (succProb n Φ w) (2^n) (σ^(2G))`.
   - `isotropicGrover_eq_mixtureProb` (or `isotropicGrover_lhs_eq_mixtureProb`): Shows that the LHS integral of `isotropicGrover_main` equals `mixtureProb (succProb n Φ w) (2^n) (σ^(2G))` for $\sigma \in (0,1)$, $G > 0$, $n \ge 2$, $\|\Phi\|=1$.

2. **Per-Gate Fidelity Mixture Limits:**
   - `continuous_mixtureProb_pow`: Shows `σ ↦ mixtureProb p N (σ^(2G))` is continuous on $\mathbb{R}$.
   - `tendsto_mixtureProb_pow_as_sigma_one`: Limit as $\sigma \to 1$ is $p$.
   - `tendsto_mixtureProb_pow_as_sigma_zero`: Limit as $\sigma \to 0$ is $1/N$ for $G > 0$.

3. **Grover Limiting Case Corollaries (Integral Form):**
   - `tendsto_expectedSuccProb_as_sigma_one`: The nested integral of `isotropicGrover_main` tends to `succProb n Φ w` as $\sigma \to 1$ along $\mathcal{N}_{(0,1)}(1)$ (and along $\mathcal{N}_{<}(1)$).
   - `tendsto_expectedSuccProb_as_sigma_zero`: The nested integral tends to $1/2^n$ as $\sigma \to 0$ along $\mathcal{N}_{(0,1)}(0)$ (and along $\mathcal{N}_{>}(0)$).
