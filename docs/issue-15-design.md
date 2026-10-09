# Design Document: Issue #15 Refactor Second-Moment Matrix Derivation in §5

## Problem Statement
In `english-proof.md` (§5, lines 159–175), the text previously presented three constraints to pin down the second-moment matrix $M = \mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top]$:
1. **Range**: $\mathbf{e}_2 \in V_\perp \implies M = c P_{V_\perp}$ (noting parenthetically that this also follows from constraint 2).
2. **Rotational symmetry within $V_\perp$**: Invariance under orthogonal transformations fixing $\Phi$ implies $M = c P_{V_\perp}$.
3. **Trace constraint**: $\mathrm{tr}(M) = 1 \implies c = 1/(d-1)$.

Constraint 1 is mathematically redundant with Constraint 2, and the statement that range alone implies $M = c P_{V_\perp}$ is imprecise (range only implies $\mathrm{range}(M) \subseteq V_\perp$ and $M\Phi = 0$).

## Proposed Solution
Refactor §5 to frame the derivation cleanly around two independent constraints, directly matching the structure in `SecondMoment.lean` (`secondMoment_eq_scalar_perp` and `trace_secondMoment_eq_one`):

1. **Subspace symmetry (Schur's Lemma / Orthogonal Invariance)**:
   Since $\mathbf{e}_2$ is uniformly distributed on the unit sphere of the $(d-1)$-dimensional equatorial subspace $V_\perp = \Phi^\perp$, its distribution is supported on $V_\perp$ (so $M\Phi = 0$) and invariant under any orthogonal transformation $R$ acting on $V_\perp$ (i.e., orthogonal $R$ fixing $\Phi$). Hence $M = R M R^\top$ for all such $R$. By Schur's lemma (or symmetry of the spherical measure), the restriction $M|_{V_\perp}$ must be a scalar multiple of the identity on $V_\perp$, fixing $M = c\,P_{V_\perp}$ for some scalar $c \ge 0$.

2. **Normalization (Trace Constraint)**:
   Since $|\mathbf{e}_2|^2 = 1$ identically,
   $$\mathrm{tr}(M) = \mathrm{E}[\mathrm{tr}(\mathbf{e}_2\mathbf{e}_2^\top)] = \mathrm{E}[|\mathbf{e}_2|^2] = 1.$$
   Since $\dim(V_\perp) = d-1$, we have $\mathrm{tr}(c\,P_{V_\perp}) = c(d-1) = 1$, which uniquely fixes $c = \frac{1}{d-1}$.

Therefore:
$$\mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top] = \frac{P_{V_\perp}}{d-1}.$$

## Verification Plan
- Check that the text in `english-proof.md` flows logically and maintains clear typography.
- Verify consistency with `SecondMoment.lean`.
