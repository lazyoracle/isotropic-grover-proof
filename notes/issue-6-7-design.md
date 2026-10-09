# Issue #6 & #7 Design Document: Formalize Sequential Markov Error Induction

## Problem Context
In `IsotropicGroverProof/Composition.lean`, `isotropicComposition` is a vacuous tautology (`X = X` via `rfl`). The multi-gate composition of $G$ independent errors was defined by fiat as `composedMeasure d G σ := poissonMarginal d (σ^G)`.
In physical quantum circuits, gate errors do not commute as global rotations, nor do they rotate around the fixed initial state $\Phi$. Rather, each gate error $k \in \{1, \dots, G\}$ rotates around the perturbed intermediate state $\Psi_{k-1}$:
$$\Psi_k = \cos\theta_k \Psi_{k-1} + \sin\theta_k \mathbf{e}_{2,k}$$
where $\mathbf{e}_{2,k} \in V_\perp^{(\Psi_{k-1})}$.

In `english-proof.md` §6, this physical reality is rigorously handled via a Markov chain on the fidelity (second moment) $f_k = \mathbb{E}[(\Psi_k \cdot \Phi)^2]$:
- Base case: $f_0 = (\Phi \cdot \Phi)^2 = 1$
- Transition parameter: $\lambda = \frac{(d-1)\sigma^2 + 1}{d}$
- Step transition operator: $T(f) = \lambda f + (1-\lambda)\frac{1-f}{d-1}$
- Recurrence: $f_{k+1} = T(f_k)$
- Contraction: $T(f) - \frac{1}{d} = \sigma^2 \left(f - \frac{1}{d}\right)$
- Closed-form solution: $f_k = \frac{(d-1)\sigma^{2k} + 1}{d}$ unconditionally for all $k \ge 0$.

This eliminates the need for an unproven spherical convolution theorem or rotational commutativity, resolving both Issue #6 and Issue #7.

## Goals

1. **`IsotropicGroverProof/Sequential.lean`**:
   - Formalize the Markov step parameters:
     - `stepLambda (d : ℕ) (σ : ℝ) : ℝ := ((d - 1 : ℝ) * σ ^ 2 + 1) / d`
     - `stepTransition (d : ℕ) (σ : ℝ) (f : ℝ) : ℝ := stepLambda d σ * f + (1 - stepLambda d σ) * (1 - f) / (d - 1)`
   - Define the sequential fidelity recurrence:
     - `def sequentialFidelity (d : ℕ) (σ : ℝ) : ℕ → ℝ`
       `| 0 => 1`
       `| k + 1 => stepTransition d σ (sequentialFidelity d σ k)`
   - Prove the contraction property:
     - `theorem stepTransition_sub_inv_d (d : ℕ) (σ f : ℝ) (hd : 2 ≤ d) : stepTransition d σ f - 1 / d = σ ^ 2 * (f - 1 / d)`
   - Prove the closed-form theorem by induction on $k$:
     - `theorem sequentialFidelity_eq (d : ℕ) (σ : ℝ) (k : ℕ) (hd : 2 ≤ d) : sequentialFidelity d σ k = ((d - 1 : ℝ) * σ ^ (2 * k) + 1) / d`
   - Prove equivalence between sequential Markov fidelity and the single-step parameter formula:
     - `theorem sequentialFidelity_eq_f₂ (d G : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 2 ≤ d) (hG : 0 < G) : sequentialFidelity d σ G = f₂ d G σ`
   - Prove the sequential mixture formula:
     - `theorem sequential_mixture_formula (p : ℝ) (n G : ℕ) (σ : ℝ) : sequentialFidelity (d n) σ G * p + (1 - sequentialFidelity (d n) σ G) * (2 - p) / ((d n : ℝ) - 1) = σ ^ (2 * G) * p + (1 - σ ^ (2 * G)) / (2 ^ n : ℝ)`

2. **`IsotropicGroverProof/Composition.lean`**:
   - Replace the misleading `:= rfl` theorem / docstring with clear documentation deprecating `isotropicComposition` and noting that multi-gate composition is derived via the sequential Markov chain in `Sequential.lean`.

3. **Exports and integration**:
   - Re-export `Sequential.lean` in `IsotropicGroverProof/Basic.lean` and `IsotropicGroverProof.lean`.
   - Ensure clean build with 0 sorries, 0 errors, 0 warnings.
