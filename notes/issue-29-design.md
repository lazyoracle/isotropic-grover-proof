# Issue #29 Design Document: Prove `poissonIntegral_cos_sq_d3` and Eliminate All Non-Standard Kernel Axioms

## Problem Context
`poissonIntegral_cos_sq_d3` in `IsotropicGroverProof/Gegenbauer.lean` is the sole non-foundational kernel `axiom` in the repository:
$$\int \theta,\, (\cos\theta)^2 \;\partial(\mathrm{poissonMarginal}\, d\, \sigma) = \frac{(d - 1)\sigma^2 + 1}{d} \qquad (d \ge 3,\; \sigma \in (0, 1)).$$
Additionally, `IsotropicGroverProof/GegenbaurerHelper.lean` (329 lines, with a filename typo) duplicates ~180 lines of $d = 2$ complex Poisson integral setup already present in `IsotropicGroverProof/IsotropicError.lean`.

## Mathematical Strategy (Pure 1D Fundamental Theorem of Calculus)

Because `poissonMarginal d σ` is defined on $[0, \pi]$ via `poissonKernelDensity d σ θ = (1 - σ²) sin^{d-2}θ / D(σ,θ)^{d/2}` where $D(\sigma, \theta) = 1 + \sigma^2 - 2\sigma\cos\theta \ge (1 - \sigma)^2 > 0$ for $\sigma \in (0, 1)$, all real powers $D(\sigma, \theta)^r$ are smooth everywhere on $\mathbb{R}$ with zero endpoint singularities.

Define the unnormalized interval moments $I_k(d, \sigma) := \int_0^\pi \mathrm{poissonKernelDensity}\, d\, \sigma\, \theta \cdot (\cos\theta)^k \, d\theta$.

1. **Generic `poissonMarginal` integral reduction (`IsotropicError.lean`):**
   For all $d \ge 2$, $\sigma \in (0, 1)$, and continuous $h : \mathbb{R} \to \mathbb{R}$:
   $$\int \theta,\, h\,\theta \;\partial(\mathrm{poissonMarginal}\, d\, \sigma) = \frac{\int_{\theta \in (0:\mathbb{R})..\pi} \mathrm{poissonKernelDensity}\, d\, \sigma\, \theta \cdot h\,\theta}{\mathrm{poissonNormConst}\, d\, \sigma}.$$

2. **Three-term moment identity for all $d \ge 2$:**
   Differentiating $\tilde{F}_0(\theta) = (1 - \sigma^2)\sin^{d-1}\theta \cdot D(\sigma, \theta)^{1 - d/2}$ (which vanishes at $0$ and $\pi$ since $d - 1 \ge 1$) via `intervalIntegral.integral_eq_sub_of_hasDerivAt` yields:
   $$\sigma d \, I_2(d, \sigma) = (d - 1)(1 + \sigma^2) I_1(d, \sigma) - (d - 2)\sigma I_0(d, \sigma).$$
   Consequently, **for every $d \ge 2$ (including $d = 2$!), $I_1(d, \sigma) = \sigma I_0(d, \sigma)$ immediately implies $I_2(d, \sigma) = \frac{(d - 1)\sigma^2 + 1}{d} I_0(d, \sigma)$**. This renders the entire 329-line `GegenbaurerHelper.lean` unnecessary!

3. **Base cases for the first moment $I_1(d, \sigma) = \sigma I_0(d, \sigma)$:**
   - **$d = 2$:** Already proved in `IsotropicError.lean` (`halfcircle_cos_d2` and `halfcircle_norm_d2`).
   - **$d = 3$:** Differentiating
     $$\tilde{H}_3(\theta) = -(1 - \sigma^2) \cdot \frac{(1 - \sigma^2) D(\sigma, \theta)^{-1/2} + D(\sigma, \theta)^{1/2}}{2\sigma^2}$$
     gives $\tilde{H}_3'(\theta) = \mathrm{poissonKernelDensity}\, 3\, \sigma\, \theta \cdot (\cos\theta - \sigma)$, with $\tilde{H}_3(\pi) = \tilde{H}_3(0) = -(1 - \sigma^2)/\sigma^2$ (since $\sqrt{D(\sigma, 0)} = 1 - \sigma$ and $\sqrt{D(\sigma, \pi)} = 1 + \sigma$). FTC yields $\int_0^\pi \mathrm{poissonKernelDensity}\, 3\, \sigma\, \theta \cdot (\cos\theta - \sigma) = 0$, hence $I_1(3, \sigma) = \sigma I_0(3, \sigma)$.

4. **Two-step induction $d \mapsto d + 2$ for all $d \ge 2$:**
   Differentiating two smooth functions vanishing at $0$ and $\pi$:
   - $\tilde{G}_0(\theta) = (1 - \sigma^2)\sin^{d-1}\theta \cdot D(\sigma, \theta)^{-d/2} \implies d\sigma I_0(d + 2, \sigma) = (d - 1) I_1(d, \sigma)$
   - $\tilde{G}_1(\theta) = (1 - \sigma^2)\cos\theta \sin^{d-1}\theta \cdot D(\sigma, \theta)^{-d/2} \implies d\sigma I_1(d + 2, \sigma) = d I_2(d, \sigma) - I_0(d, \sigma)$
   
   Combined with step 2, $I_1(d, \sigma) = \sigma I_0(d, \sigma) \implies I_1(d + 2, \sigma) = \sigma I_0(d + 2, \sigma)$. Pattern matching on `d` (`2`, `3`, `d + 4`) proves $I_1(d, \sigma) = \sigma I_0(d, \sigma)$ and $I_2(d, \sigma) = \frac{(d - 1)\sigma^2 + 1}{d} I_0(d, \sigma)$ for all $d \ge 2$.

## Architecture & Cleanup Decisions
- Generalize `poissonMarginal_mean_cos` ($\mathbb{E}[\cos\theta] = \sigma$ for all $d \ge 2$) in `IsotropicError.lean` (keeping `poissonMarginal_mean_cos_d2` as a 1-line specialization).
- Prove `poissonIntegral_cos_sq` ($\mathbb{E}[\cos^2\theta] = \frac{(d-1)\sigma^2 + 1}{d}$ for all $d \ge 2$) and `theorem poissonIntegral_cos_sq_d3` / `poissonIntegral_cos_sq_d2` in `Gegenbauer.lean` with **zero custom axioms**.
- Delete `IsotropicGroverProof/GegenbaurerHelper.lean` completely (~329 lines of duplicated $d = 2$ boilerplate removed).
- Update `#guard_msgs in #print axioms isotropicGrover_main` in `MainTheorem.lean` to `[propext, Classical.choice, Quot.sound]` and enable `axiom-audit: true` in `.github/workflows/lean_action_ci.yml` so CI rejects any non-foundational axiom across the entire `IsotropicGrover` namespace.
