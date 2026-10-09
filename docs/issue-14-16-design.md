# Issue #14 & #16 Design Document: Align Scope, Derivation Framing, and Formal Verification Disclosures

## Problem Context
1. **Issue #14**: `README.md` and `english-proof.md` frame the derivation goal as deriving repetition overhead $k(n)$ and its exponential fit, whereas the mathematical derivation targets the expected success probability mixture formula $\mathrm{E}[p_e]$ given gate count $G$. Furthermore, gate count $G(n)$ relies on simulation or empirical data rather than an internal closed-form derivation in $n$, and the exactness claim must be qualified by the underlying model assumptions.
2. **Issue #16**: `README.md` overstates the formal verification scope by presenting the theorem as a fully verified proof of Grover's algorithm under isotropic noise with a "clean axiom footprint". In reality:
   - The theorem is verified for an arbitrary unit vector $\Phi$ and integer $G$, not a formalized Grover circuit (#8).
   - Multi-gate composition is assumed by definition via `composedMeasure` with a placeholder `rfl` (#6).
   - Sequential gate error dynamics are modeled as a single effective rotation rather than sequential state recurrence (#7).
   - The $d \ge 3$ Poisson second-moment integral identity is axiomatized (`poissonIntegral_cos_sq_d3`) (#9).

## Design Objectives
1. **Clarify Derivation Goal and Downstream Steps** (`README.md`, `english-proof.md`):
   - Explicitly separate the core mathematical derivation (the mixture formula $\mathrm{E}[p_e] = \sigma^{2G} p_\mathrm{ideal} + (1-\sigma^{2G})/N$ for a given state and gate count $G$) from the downstream application (calculating repetition overhead $k(n)$ and fitting an exponential).
   - Note the role of $G(n)$: empirical simulation gate counts vs asymptotic approximations like $\sim \frac{\pi}{4}\sqrt{2^n}$.
   - Qualify exactness: exact within the isotropic model algebra, subject to model assumptions.

2. **Honest Formal Verification Scope and Disclosures** (`README.md`):
   - State the precise verified Lean theorem:
     *"Given the isotropic single-error model with angle distribution `poissonMarginal d (σ^G)` and the axiomatized $d \ge 3$ second-moment identity, the model's expected success probability for an arbitrary unit-vector state equals $\sigma^{2G} \cdot p_\mathrm{ideal} + (1 - \sigma^{2G}) / N$."*
   - Explicitly list the axiom footprint (`#print axioms isotropicGrover_main`):
     - `propext`, `Classical.choice`, `Quot.sound` (standard foundational axioms)
     - `poissonIntegral_cos_sq_d3` (analytic axiom for high-dimensional second moment)
   - Disclose open gaps with explicit links to tracking issues:
     - Issue #6: Composition law unproven / assumed by definition
     - Issue #7: Sequential gate error dynamics vs single effective error
     - Issue #8: Arbitrary unit vector state rather than formalized Grover circuit
     - Issue #9: High-dimensional Poisson integral identity axiomatized for $d \ge 3$
