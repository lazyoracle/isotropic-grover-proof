# Issue #9 Design Document: Harmonic Extension Derivation and Documentation of d ≥ 3 Poisson Axiom

## Problem Context
In `IsotropicGroverProof/Gegenbauer.lean` (lines 28–30), the second moment of the Poisson marginal distribution for $d \ge 3$ is axiomatized:
```lean
axiom poissonIntegral_cos_sq_d3 (d : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Ioo 0 1) (hd : 3 ≤ d) :
    ∫ θ, (cos θ) ^ 2 ∂(poissonMarginal d σ) =
    ((d - 1 : ℝ) * σ ^ 2 + 1) / d
```
Running `#print axioms isotropicGrover_main` confirms that `poissonIntegral_cos_sq_d3` is the sole non-foundational axiom in the entire proof (`[propext, Classical.choice, poissonIntegral_cos_sq_d3, Quot.sound]`).

While $d = 2$ is 100% formally verified without axioms in `IsotropicGroverProof/GegenbaurerHelper.lean` via Mathlib's complex Poisson integral formula on the unit disc (`Mathlib.Analysis.Complex.Poisson`), general $d$-dimensional spherical harmonic analysis and the Poisson representation formula for Euclidean balls in $\mathbb{R}^d$ ($d \ge 3$) are currently outside Mathlib's library scope.

## Mathematical Derivation via Harmonic Polynomial Extension

### 1. Setting and Boundary Data
Let $S^{d-1} = \{ \xi \in \mathbb{R}^d : |\xi| = 1 \}$ denote the unit sphere in $\mathbb{R}^d$, and let $\Phi \in \mathbb{R}^d$ be a fixed unit pole vector ($|\Phi| = 1$). The boundary function is the quadratic form:
$$ h(\xi) = (\xi \cdot \Phi)^2 = \cos^2\theta $$
where $\theta$ is the angle between $\xi$ and $\Phi$.

### 2. Harmonic Polynomial Decomposition
In the interior ball $B^d = \{ \mathbf{x} \in \mathbb{R}^d : |\mathbf{x}| < 1 \}$:
- The Laplacian of $(\mathbf{x} \cdot \Phi)^2$ is:
  $$\Delta ((\mathbf{x} \cdot \Phi)^2) = \sum_{i=1}^d \frac{\partial^2}{\partial x_i^2} \left(\sum_j x_j \Phi_j\right)^2 = \sum_{i=1}^d 2 \Phi_i^2 = 2 |\Phi|^2 = 2.$$
- The Laplacian of $|\mathbf{x}|^2$ is:
  $$\Delta (|\mathbf{x}|^2) = \sum_{i=1}^d \frac{\partial^2}{\partial x_i^2} \sum_j x_j^2 = \sum_{i=1}^d 2 = 2d.$$
  Hence $\Delta (|\mathbf{x}|^2 / d) = 2$.
- Consequently, the difference
  $$P_2(\mathbf{x}) = (\mathbf{x} \cdot \Phi)^2 - \frac{|\mathbf{x}|^2}{d}$$
  satisfies $\Delta P_2 = 2 - 2 = 0$. $P_2$ is a solid spherical harmonic of degree 2 (trace-free quadratic polynomial).

### 3. Boundary Matching and Harmonic Extension
On the boundary sphere $S^{d-1}$ where $|\xi| = 1$:
$$P_2(\xi) = (\xi \cdot \Phi)^2 - \frac{1}{d} = h(\xi) - \frac{1}{d}.$$
Adding the constant harmonic function $1/d$ ($\Delta(1/d) = 0$), the unique harmonic extension of $h$ to $\overline{B}^d$ is:
$$H(\mathbf{x}) = (\mathbf{x} \cdot \Phi)^2 - \frac{|\mathbf{x}|^2}{d} + \frac{1}{d}.$$
This function satisfies:
1. $\Delta H = 0$ on $B^d$.
2. $H(\xi) = h(\xi)$ for all $\xi \in S^{d-1}$.

### 4. Poisson Representation and Radial Evaluation
By the classical Poisson representation theorem for harmonic functions on Euclidean balls (Axler, Bourdon & Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137, 2001, Theorems 5.5 and 5.14):
$$H(\mathbf{x}) = \int_{S^{d-1}} P(\mathbf{x}, \xi) h(\xi) \, d\sigma_{S^{d-1}}(\xi)$$
where $P(\mathbf{x}, \xi) = \frac{1 - |\mathbf{x}|^2}{|\mathbf{x} - \xi|^d}$ is the Poisson kernel for $B^d$.

Evaluating at the interior point $\mathbf{x} = \sigma \Phi$ with $\sigma \in (0, 1)$:
- $\mathbf{x} \cdot \Phi = \sigma (\Phi \cdot \Phi) = \sigma |\Phi|^2 = \sigma$.
- $|\mathbf{x}|^2 = |\sigma \Phi|^2 = \sigma^2 |\Phi|^2 = \sigma^2$.
- Therefore:
  $$H(\sigma \Phi) = \sigma^2 - \frac{\sigma^2}{d} + \frac{1}{d} = \frac{(d - 1)\sigma^2 + 1}{d}.$$

By rotational symmetry around the axis $\Phi$, integrating against the Poisson kernel centered at $\sigma \Phi$ on $S^{d-1}$ is identical to integrating $\cos^2\theta$ with respect to the projected 1D marginal measure `poissonMarginal d σ`:
$$\int_0^\pi \cos^2\theta \, d(\mathrm{poissonMarginal}\, d\, \sigma)(\theta) = H(\sigma \Phi) = \frac{(d - 1)\sigma^2 + 1}{d}.$$

## Mathlib Scope Boundary
- For $d = 2$, $S^1 \cong \mathbb{T} \subset \mathbb{C}$, where harmonic functions coincide with real parts of holomorphic functions. Mathlib provides `circleAverage_poissonKernel_of_diffContOnCl` in `Mathlib.Analysis.Complex.Poisson`.
- For $d \ge 3$, Mathlib does not yet possess the Poisson representation theorem on Euclidean balls $\mathbb{R}^d$ or general spherical harmonics.
- Hence, `poissonIntegral_cos_sq_d3` is the sole non-foundational axiom of the project, isolating the exact boundary where the quantum proof interfaces with differential equations / potential theory.

## Goals & Deliverables
1. In `IsotropicGroverProof/Gegenbauer.lean`:
   - Detailed docstrings explaining the harmonic extension derivation, Poisson representation, boundary matching, and Mathlib library boundary.
   - Formal algebraic verification lemmas:
     - `laplacian_trace_cancellation (d : ℝ) (hd : d ≠ 0) : (2 : ℝ) - (2 * d) / d = 0`
     - `harmonicExtension_boundary (d : ℝ) (dot : ℝ) : dot ^ 2 - 1 / d + 1 / d = dot ^ 2`
     - `harmonicExtension_eval (d σ : ℝ) (hd : d ≠ 0) : σ ^ 2 - σ ^ 2 / d + 1 / d = ((d - 1) * σ ^ 2 + 1) / d`
     - `poissonIntegral_val_sigma_one (d : ℝ) (hd : d ≠ 0) : ((d - 1) * 1 ^ 2 + 1) / d = 1`
     - `poissonIntegral_val_sigma_zero (d : ℝ) : ((d - 1) * 0 ^ 2 + 1) / d = 1 / d`
   - Numeric TDD spot checks for $d = 3, 4, 8, 16, 32, 64$.
2. In `README.md`:
   - Update and expand Section "Axiom Footprint" with the rigorous mathematical explanation and Axler et al. citation.
3. Verification:
   - Ensure `lake build` passes with 0 errors, 0 warnings, 0 sorries.
