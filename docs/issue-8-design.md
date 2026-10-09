# Issue #8 Design Document: Formalize Grover State Vectors and Circuit Connection

## Problem Context
In `IsotropicGroverProof/MainTheorem.lean`, `isotropicGrover_main` proves the $\sigma^{2G}$ mixture formula for an arbitrary unit vector $\Phi \in E(n)$ and positive integer $G$:
$$ \mathbb{E}[p_e] = \sigma^{2G} \cdot \mathrm{succProb}(n, \Phi, w) + \frac{1 - \sigma^{2G}}{2^n} $$
While mathematically general and powerful, the code previously lacked explicit definitions of:
1. The initial uniform superposition state vector $|s\rangle$.
2. The target basis state vector $|w\rangle$.
3. The orthogonal non-target superposition $|w^\perp\rangle$.
4. The 2D Grover search plane $\mathrm{span}(|w\rangle, |w^\perp\rangle)$ parameterized by angle $\alpha$ or ideal success probability $p_{\mathrm{ideal}}$.
5. Explicit specialization of `isotropicGrover_main` to these Grover states.

## Goals
1. Create `IsotropicGroverProof/GroverCircuit.lean`:
   - Define target basis state `targetBasisState (n : ℕ) (w : Fin (2 ^ n)) : E n`.
     - Prove `‖targetBasisState n w‖ = 1`.
     - Prove `succProb n (targetBasisState n w) w = 1`.
   - Define non-target orthogonal state `targetPerpState (n : ℕ) (w : Fin (2 ^ n)) : E n`.
     - Prove `inner (targetBasisState n w) (targetPerpState n w) = 0`.
     - Prove `succProb n (targetPerpState n w) w = 0`.
     - Prove `‖targetPerpState n w‖ = 1` for $1 < 2^n$.
   - Define uniform superposition `uniformSuperposition (n : ℕ) : E n`.
     - Prove `succProb n (uniformSuperposition n) w = 1 / 2^n`.
     - Prove `‖uniformSuperposition n‖ = 1`.
     - Specialize `isotropicGrover_main` to `uniformSuperposition`: prove the expected success probability under isotropic noise is identically $1 / 2^n$ for any gate count $G$ and fidelity parameter $\sigma$.
   - Define the 2D Grover search plane:
     - `groverState2D (n : ℕ) (w : Fin (2 ^ n)) (α : ℝ) : E n` parameterized by angle $\alpha$.
       - Prove `‖groverState2D n w α‖ = 1` for $1 < 2^n$.
       - Prove `succProb n (groverState2D n w α) w = \sin^2(\alpha)`.
       - Specialization theorem `isotropicGrover_groverState2D` yielding $\sigma^{2G} \sin^2(\alpha) + (1 - \sigma^{2G}) / 2^n$.
     - `groverState2D_prob (n : ℕ) (w : Fin (2 ^ n)) (p_ideal : ℝ) : E n` parameterized by $p_{\mathrm{ideal}} \in [0, 1]$.
       - Prove `‖groverState2D_prob n w p_ideal‖ = 1` for $1 < 2^n$ and $p_{\mathrm{ideal}} \in [0, 1]$.
       - Prove `succProb n (groverState2D_prob n w p_ideal) w = p_ideal`.
       - Specialization theorem `isotropicGrover_groverState2D_prob` yielding $\sigma^{2G} p_{\mathrm{ideal}} + (1 - \sigma^{2G}) / 2^n$.
   - For the ideal Grover output state ($p_{\mathrm{ideal}} = 1$ or $\Phi = \mathrm{targetBasisState}$):
     - Specialization theorem `isotropicGrover_targetBasisState` yielding $\sigma^{2G} + (1 - \sigma^{2G}) / 2^n$.
2. In `IsotropicGroverProof/MainTheorem.lean`:
   - Add explicit documentation clarifying that `isotropicGrover_main` is the geometric invariant engine which acts on any unit vector $\Phi$, and that `GroverCircuit.lean` specializes this geometric invariant to Grover's algorithm (uniform superposition, Grover 2D search plane, and target basis state).
3. Export `IsotropicGroverProof/GroverCircuit.lean` in `IsotropicGroverProof/Basic.lean` and `IsotropicGroverProof.lean`.
4. Verify 0 errors, 0 warnings, 0 sorries via `lake build`.
