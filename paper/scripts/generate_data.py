#!/usr/bin/env python3
"""Deterministic figure and table data generator for the PRA manuscript.

Uses Python 3 standard library modules only (`argparse`, `decimal`, `math`,
`pathlib`, `sys`) with cancellation-free `math.log1p` / `math.expm1` and
60-digit `Decimal` trigonometric reduction so all quantities remain accurate
through utility scale (`n = 60`, `N = 2^60`).

Generated files in `paper/data/` (consumed by `pgfplots` and `paper/body.tex`):
1. `fig2_oscillations.dat` (251 rows, `k_over_kideal` in `[0.00, 2.50]`, `M = 1`,
   macro-operator Grover schedule `G(K) = 2K + 1`, `sigma_init = sigma`,
   `gamma = sigma^2`):
   Columns:
     `k_over_kideal  K_n6  p_n6_s1  p_n6_s9999  p_n6_s999  p_n6_s99`
     `K_n10  p_n10_s1  p_n10_s9999  p_n10_s999  p_n10_s99`
     `K_n14  p_n14_s1  p_n14_s9999  p_n14_s999  p_n14_s99`
     `K_n20  p_n20_s1  p_n20_s9999  p_n20_s999  p_n20_s99`
2. `fig2_peaks.dat` (16 rows: `n in {6, 10, 14, 20}` x
   `sigma in {1.0, 0.9999, 0.999, 0.99}`):
   Columns:
     `n  sigma  K_ideal  K_star  k_over_kideal_star  p_star`
3. `fig3a_queries.dat` (47 rows: `n in [4, 50]`, `M = 1`, linear-`n` primitive
   gate counts `G_1q(n,K) = n + K(16n - 20)`, `G_2q(n,K) = K(12n - 18)`,
   `G(n,K) = n + K(28n - 38)`, repeat-until-success expected oracle queries
   `Q(n,K) = K / p_e(n,K)`; `Q_ideal` minimizes `K / p_ideal(n,K)` at `sigma = 1`
   on the identical functional as `Q_opt_*`, while `Q_naive_s1` records the
   single-shot peak `K_ideal / p_ideal(n, K_ideal)`):
   Columns:
     `n  log2N  Q_ideal  Q_classical  Q_opt_s9999  Q_naive_s9999`
     `Q_opt_s999  Q_naive_s999  Q_opt_s99999  Q_naive_s99999  Q_naive_s1`
4. `fig3b_growth_rate.dat` (121 log-spaced rows: `1 - sigma in [1e-6, 2e-1]`,
   analytical per-qubit exponential growth factor `b(sigma, M)` from exact
   equidistant 3-point interpolation `k(n) = a * b^n + c` at `n in {7, 10, 13}`
   for `M in {1, 4, 16}` under `G(n,K) = n + K(28n - 38)`):
   Columns:
     `one_minus_sigma  sigma  b_M1  b_M4  b_M16`
5. `fig4_resource_budgets.dat` (55 rows: `n in [6, 60]`, `M = 1`,
   `K = K_ideal(n)`, heterogeneous gate counts `G_1q = n + K(16n - 20)` and
   `G_2q = K(12n - 18)` with `1 - sigma_1q = alpha * (1 - sigma_2q)`):
   Columns:
     `n  infid2q_k2_a01  infid2q_k2_a001  infid2q_k10_a01  infid2q_k10_a001`
6. `table1_rows.tex` (6 LaTeX rows for `n in {10, 20, 30, 40, 50, 60}` inputted
   directly into `Table I` of `paper/body.tex`):
   8 columns:
     `n & K_ideal & G_1q & G_2q & (1-sigma_2q)[k<=2,a=0.1]`
     `& (1-sigma_2q)[k<=2,a=0.01] & (1-sigma_2q)[k<=10,a=0.1]`
     `& (1-sigma_2q)[k<=10,a=0.01] \\\\`
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from functools import lru_cache
import math
from pathlib import Path
import sys


DEFAULT_OUTPUT_DIR = Path(__file__).resolve().parent.parent / "data"
_DEC_PREC = 64


def _compute_decimal_pi() -> Decimal:
    """Compute pi to `_DEC_PREC` digits via Machin's identity."""
    with localcontext() as ctx:
        ctx.prec = _DEC_PREC + 8

        def atan_inv(m: int) -> Decimal:
            inv_m = Decimal(1) / Decimal(m)
            inv_m2 = inv_m * inv_m
            term = inv_m
            total = inv_m
            k = 1
            eps = Decimal(10) ** (-_DEC_PREC - 4)
            while True:
                term = -term * inv_m2
                k += 2
                step = term / Decimal(k)
                if abs(step) < eps:
                    break
                total += step
            return total

        return Decimal(4) * (Decimal(4) * atan_inv(5) - atan_inv(239))


_PI_DEC: Decimal = _compute_decimal_pi()


@lru_cache(maxsize=4096)
def exact_ideal_prob_and_complement(n: int, M: int, K: int) -> tuple[float, float]:
    """Return `(p_ideal, 1 - p_ideal)` for `M`-target Grover after `K` steps.

    Uses 64-digit `Decimal` range reduction so `1 - p_ideal = cos^2((2K+1)*theta)`
    retains full IEEE-754 float64 precision even at `n = 60` (`1 - p_ideal ~ 1e-21`,
    well below float64 machine epsilon `2.22e-16`).
    """
    if M <= 0:
        return 0.0, 1.0
    two_pow_n = 1 << n
    if M >= two_pow_n:
        return 1.0, 0.0

    # Exact rational angle sin(theta) = 1/2 -> theta = pi/6 (e.g. n=2, M=1 or n=6, M=16)
    if 4 * M == two_pow_n and (2 * K + 1) % 6 == 3:
        return 1.0, 0.0

    with localcontext() as ctx:
        ctx.prec = _DEC_PREC
        eps = Decimal(10) ** (-_DEC_PREC + 6)
        r = Decimal(M) / Decimal(two_pow_n)
        x = r.sqrt()
        # theta = asin(x) = atan(x / sqrt(1 - r)) with 8-fold half-angle reduction
        u = x / (Decimal(1) - r).sqrt()
        for _ in range(8):
            u = u / (Decimal(1) + (Decimal(1) + u * u).sqrt())

        u2 = u * u
        term = u
        atan_u = u
        k = 1
        while True:
            term = -term * u2
            k += 2
            step = term / Decimal(k)
            if abs(step) < eps:
                break
            atan_u += step

        theta = Decimal(256) * atan_u
        alpha = Decimal(2 * K + 1) * theta
        mult = int((alpha / _PI_DEC).to_integral_value())
        rem = alpha - Decimal(mult) * _PI_DEC

        rem2 = rem * rem
        sin_v = rem
        sin_t = rem
        cos_v = Decimal(1)
        cos_t = Decimal(1)
        idx = 1
        while True:
            cos_t = -cos_t * rem2 / Decimal((2 * idx - 1) * (2 * idx))
            sin_t = -sin_t * rem2 / Decimal((2 * idx) * (2 * idx + 1))
            cos_v += cos_t
            sin_v += sin_t
            if abs(cos_t) < eps and abs(sin_t) < eps:
                break
            idx += 1

        return float(sin_v * sin_v), float(cos_v * cos_v)


def grover_half_angle(n: int, M: int = 1) -> float:
    """Return `theta_{n,M} = arcsin(sqrt(M / 2^n))`."""
    return math.asin(math.sqrt(math.ldexp(float(M), -n)))


def ideal_iteration_continuous(n: int, M: int = 1) -> float:
    """Return continuous noiseless peak iteration `K_ideal_cont = pi/(4*theta) - 1/2`."""
    theta = grover_half_angle(n, M)
    return math.pi / (4.0 * theta) - 0.5


def ideal_iteration_int(n: int, M: int = 1) -> int:
    """Return integer Grover iteration count `K_ideal >= 1` maximizing `p_ideal`."""
    return max(1, round(ideal_iteration_continuous(n, M)))


def gate_counts_1q_2q(n: int, K: int) -> tuple[int, int]:
    """Return `(G_1q, G_2q)` for `n`-qubit Grover with linear-`n` MCX decomposition.

    Per Grover iteration: `g_1q(n) = 16n - 20`, `g_2q(n) = 12n - 18`, plus `n`
    initialization Hadamards (`G_init,1q = n`, `G_init,2q = 0`).
    """
    g1 = n + K * (16 * n - 20)
    g2 = K * (12 * n - 18)
    return g1, g2


def optimal_iteration_continuous(gamma: float, n: int, M: int = 1) -> float:
    """Return continuous first-lobe optimal iteration count `K^*(gamma, n, M)`.

    Solves `d/dK [gamma^{2K} (sin^2((2K+1)*theta) - sin^2(theta))] = 0` via the
    exact Proposition 1 identity
      `(2K^* + 1)*theta = (pi - phi - arcsin(sin(phi) * cos(2*theta))) / 2`
    where `kappa = -ln(gamma) / (2*theta)` and `phi = arctan(kappa)`, rewritten
    in cancellation-free form so accuracy is `< 1e-14` for all `gamma in (0, 1]`.
    """
    if not (0.0 < gamma <= 1.0):
        raise ValueError(f"gamma must lie in (0, 1], got {gamma}")
    two_pow_n = 1 << n
    if not (0 < M < two_pow_n):
        raise ValueError(f"M={M} must satisfy 0 < M < 2^n={two_pow_n}")

    theta = grover_half_angle(n, M)
    if gamma == 1.0:
        return math.pi / (4.0 * theta) - 0.5

    neg_ln_gamma = -math.log1p(gamma - 1.0) if gamma > 0.5 else -math.log(gamma)
    kappa = neg_ln_gamma / (2.0 * theta)

    # Switch between direct asin(z) for |z| <= 0.7 and complementary asin(sqrt(1 - z^2))
    # for |z| > 0.7 so full 53-bit precision holds across both kappa -> 0 and kappa -> inf.
    phi = math.atan(kappa)
    sin_phi = kappa / math.hypot(1.0, kappa)
    cos_2t = 1.0 - 2.0 * math.ldexp(float(M), -n)
    z = sin_phi * cos_2t
    if abs(z) <= 0.7:
        two_alpha_star = math.pi - phi - math.asin(z)
    else:
        sin_2t = math.sin(2.0 * theta)
        k2 = kappa * kappa
        rad = math.sqrt((1.0 + k2 * sin_2t * sin_2t) / (1.0 + k2))
        arccos_abs_z = math.asin(min(1.0, rad))
        half_pi_minus_phi = math.atan2(1.0, kappa)
        if cos_2t >= 0.0:
            two_alpha_star = half_pi_minus_phi + arccos_abs_z
        else:
            two_alpha_star = half_pi_minus_phi + (math.pi - arccos_abs_z)

    alpha_star = 0.5 * two_alpha_star
    return (alpha_star / theta - 1.0) * 0.5


def noisy_grover_prob_continuous(
    n: int, M: int, K: float, sigma_init: float, gamma: float
) -> float:
    """Evaluate `p_e(K) = M/N + sigma_init^2 * gamma^{2K} * (sin^2((2K+1)*theta) - M/N)`."""
    r = math.ldexp(float(M), -n)
    theta = grover_half_angle(n, M)
    p_id = math.sin((2.0 * K + 1.0) * theta) ** 2
    if sigma_init <= 0.0 or gamma <= 0.0:
        return r
    ln_w = 2.0 * (math.log(sigma_init) + K * math.log(gamma))
    w = math.exp(ln_w) if ln_w > -750.0 else 0.0
    return r + w * (p_id - r)


def repetition_overhead(
    n: int,
    M: int,
    K: int,
    sigma_eff: float,
    *,
    ln_sigma_eff: float | None = None,
) -> float:
    """Return `k(n, M, K) = ln(1 - p_ideal) / ln(1 - p_e)` without float64 cancellation.

    Uses `math.log1p(-p_e)` when `p_e <= 0.5` (preventing `1.0 - 2^-60 == 1.0`
    division-by-zero) and `1 - p_e = sigma_eff^2 * (1 - p_ideal) + (1 - sigma_eff^2)*(1 - M/N)`
    via `-math.expm1(2 * ln_sigma_eff)` when `p_e > 0.5`.
    """
    if not (0.0 <= sigma_eff <= 1.0):
        raise ValueError(f"sigma_eff must lie in [0, 1], got {sigma_eff}")
    if sigma_eff == 1.0 and (ln_sigma_eff is None or ln_sigma_eff == 0.0):
        return 1.0

    p_id, q_id = exact_ideal_prob_and_complement(n, M, K)
    # Degenerate exact p_ideal == 1 (e.g. n = 2, M = 1, K = 1): float64 epsilon fallback
    if q_id == 0.0:
        q_id = math.ldexp(1.0, -53)
        p_id = 1.0 - q_id

    r = math.ldexp(float(M), -n)
    if ln_sigma_eff is not None:
        two_ln_s = 2.0 * ln_sigma_eff
        s2 = math.exp(two_ln_s) if two_ln_s > -750.0 else 0.0
        one_minus_s2 = -math.expm1(two_ln_s)
    elif sigma_eff == 0.0:
        s2 = 0.0
        one_minus_s2 = 1.0
    else:
        s2 = sigma_eff * sigma_eff
        one_minus_s2 = (1.0 - sigma_eff) * (1.0 + sigma_eff)

    p_e = s2 * p_id + one_minus_s2 * r
    log_q_id = math.log(q_id)
    if p_e <= 0.5:
        log_q_e = math.log1p(-p_e)
    else:
        q_e = s2 * q_id + one_minus_s2 * (1.0 - r)
        log_q_e = math.log(q_e)

    return log_q_id / log_q_e


def solve_infidelity_budget(n: int, k_budget: float, alpha: float, M: int = 1) -> float:
    """Binary-search two-qubit gate infidelity `1 - sigma_2q` for `k(n) == k_budget`.

    Operates in log-infidelity space using `math.log1p` and `math.expm1` so sub-epsilon
    infidelities (`~1e-23` at `n = 60, k = 2`) retain full IEEE-754 precision.
    """
    if k_budget <= 1.0:
        raise ValueError(f"k_budget must exceed 1.0, got {k_budget}")
    if not (0.0 <= alpha <= 1.0):
        raise ValueError(f"alpha must lie in [0, 1], got {alpha}")

    k_id = ideal_iteration_int(n, M)
    g1, g2 = gate_counts_1q_2q(n, k_id)

    lo_ln = -90.0  # exp(-90) ~ 8.2e-40
    hi_ln = -1e-12  # exp(-1e-12) ~ 1 - 1e-12
    for _ in range(100):
        mid_ln = 0.5 * (lo_ln + hi_ln)
        eps2 = math.exp(mid_ln)
        ln_seff = g1 * math.log1p(-alpha * eps2) + g2 * math.log1p(-eps2)
        k_val = repetition_overhead(
            n, M, k_id, math.exp(ln_seff), ln_sigma_eff=ln_seff
        )
        if k_val <= k_budget:
            lo_ln = mid_ln
        else:
            hi_ln = mid_ln

    return math.exp(0.5 * (lo_ln + hi_ln))


def _optimal_query_complexity_primitive(n: int, sigma_g: float, M: int = 1) -> float:
    """Return `min_{1 <= K <= K_ideal} K / p_e(n, M, K)` under `G = n + K(28n - 38)`."""
    k_id = ideal_iteration_int(n, M)
    r = math.ldexp(float(M), -n)
    theta = grover_half_angle(n, M)
    ln_s = math.log1p(sigma_g - 1.0) if sigma_g > 0.5 else math.log(sigma_g)
    g_iter = 28 * n - 38
    gamma = math.exp(g_iter * ln_s) if g_iter * ln_s > -750.0 else 0.0

    if gamma > 0.0:
        k_star = optimal_iteration_continuous(gamma, n, M)
    else:
        k_star = 1.0

    def expected_queries(k_int: int) -> float:
        two_ln_seff = 2.0 * (n + k_int * g_iter) * ln_s
        s2 = math.exp(two_ln_seff) if two_ln_seff > -750.0 else 0.0
        if k_int == k_id:
            p_id, _ = exact_ideal_prob_and_complement(n, M, k_int)
        else:
            p_id = math.sin((2 * k_int + 1) * theta) ** 2
        p_e = r + s2 * (p_id - r)
        return float(k_int) / p_e

    # Unimodal ternary search on [1, ceil(k_star) + 2] plus exact endpoint K_ideal
    left = 1
    right = max(1, min(k_id, int(math.ceil(k_star)) + 2))
    while right - left > 6:
        m1 = left + (right - left) // 3
        m2 = right - (right - left) // 3
        if expected_queries(m1) <= expected_queries(m2):
            right = m2
        else:
            left = m1

    best = expected_queries(k_id)
    for k_cand in range(left, right + 1):
        val = expected_queries(k_cand)
        if val < best:
            best = val
    return best


def _naive_query_complexity_primitive(n: int, sigma_g: float, M: int = 1) -> float:
    """Return `K_ideal / p_e(n, M, K_ideal)` under `G = n + K_ideal*(28n - 38)`."""
    k_id = ideal_iteration_int(n, M)
    r = math.ldexp(float(M), -n)
    p_id, _ = exact_ideal_prob_and_complement(n, M, k_id)
    ln_s = math.log1p(sigma_g - 1.0) if sigma_g > 0.5 else math.log(sigma_g)
    two_ln_seff = 2.0 * (n + k_id * (28 * n - 38)) * ln_s
    s2 = math.exp(two_ln_seff) if two_ln_seff > -750.0 else 0.0
    p_e = r + s2 * (p_id - r)
    return float(k_id) / p_e


def build_fig2_oscillations_and_peaks() -> tuple[str, str]:
    """Build `fig2_oscillations.dat` and `fig2_peaks.dat` contents."""
    ns = (6, 10, 14, 20)
    sigmas = (
        (1.0, "s1"),
        (0.9999, "s9999"),
        (0.999, "s999"),
        (0.99, "s99"),
    )

    osc_header = [
        "# Deterministic Grover oscillation curves for Fig. 2 (M = 1, macro-gate G(K) = 2K + 1).",
        "# Generated by paper/scripts/generate_data.py — do not edit manually.",
    ]
    col_names = ["k_over_kideal"]
    for n in ns:
        col_names.append(f"K_n{n}")
        for _, tag in sigmas:
            col_names.append(f"p_n{n}_{tag}")
    osc_lines = osc_header + ["\t".join(col_names)]

    k_ideals_cont = {n: ideal_iteration_continuous(n, 1) for n in ns}
    num_steps = 250
    for step in range(num_steps + 1):
        u = step * 0.01  # 0.00 .. 2.50
        row = [f"{u:.4f}"]
        for n in ns:
            k_val = u * k_ideals_cont[n]
            row.append(f"{k_val:.6f}")
            for s_val, _ in sigmas:
                p_val = noisy_grover_prob_continuous(n, 1, k_val, s_val, s_val * s_val)
                row.append(f"{p_val:.8f}")
        osc_lines.append("\t".join(row))

    peaks_lines = [
        "# Analytical first-lobe peak locus (K^*, p_e(K^*)) for Fig. 2 (Proposition 1).",
        "# Generated by paper/scripts/generate_data.py — do not edit manually.",
        "n\tsigma\tK_ideal\tK_star\tk_over_kideal_star\tp_star",
    ]
    for n in ns:
        k_id_cont = k_ideals_cont[n]
        for s_val, _ in sigmas:
            gamma = s_val * s_val
            k_star = optimal_iteration_continuous(gamma, n, 1)
            p_star = noisy_grover_prob_continuous(n, 1, k_star, s_val, gamma)
            peaks_lines.append(
                f"{n}\t{s_val:.4f}\t{k_id_cont:.6f}\t{k_star:.6f}\t"
                f"{k_star / k_id_cont:.6f}\t{p_star:.8f}"
            )

    return "\n".join(osc_lines) + "\n", "\n".join(peaks_lines) + "\n"


def build_fig3a_queries() -> str:
    """Build `fig3a_queries.dat` for `n in [4, 50]`, `M = 1`."""
    lines = [
        "# Repeat-until-success expected oracle queries Q(n, K) = K / p_e(n, K) for Fig. 3(a), n in [4, 50], M = 1.",
        "# Q_ideal minimizes K / p_ideal(n, K) at sigma = 1 (Zalka/BBHT baseline); Q_naive_s1 = K_ideal / p_ideal(n, K_ideal).",
        "# Primitive linear-n circuit gate count G(n, K) = n + K*(28n - 38).",
        "# Generated by paper/scripts/generate_data.py — do not edit manually.",
        "\t".join(
            [
                "n",
                "log2N",
                "Q_ideal",
                "Q_classical",
                "Q_opt_s9999",
                "Q_naive_s9999",
                "Q_opt_s999",
                "Q_naive_s999",
                "Q_opt_s99999",
                "Q_naive_s99999",
                "Q_naive_s1",
            ]
        ),
    ]

    for n in range(4, 51):
        k_id = ideal_iteration_int(n, 1)
        p_id, _ = exact_ideal_prob_and_complement(n, 1, k_id)
        q_ideal = _optimal_query_complexity_primitive(n, 1.0, 1)
        q_naive_s1 = float(k_id) / p_id
        q_classical = math.ldexp(1.0, n)

        q_opt_9999 = _optimal_query_complexity_primitive(n, 0.9999, 1)
        q_naive_9999 = _naive_query_complexity_primitive(n, 0.9999, 1)
        q_opt_999 = _optimal_query_complexity_primitive(n, 0.999, 1)
        q_naive_999 = _naive_query_complexity_primitive(n, 0.999, 1)
        q_opt_99999 = _optimal_query_complexity_primitive(n, 0.99999, 1)
        q_naive_99999 = _naive_query_complexity_primitive(n, 0.99999, 1)

        lines.append(
            f"{n}\t{n}\t{q_ideal:.8e}\t{q_classical:.8e}\t"
            f"{q_opt_9999:.8e}\t{q_naive_9999:.8e}\t"
            f"{q_opt_999:.8e}\t{q_naive_999:.8e}\t"
            f"{q_opt_99999:.8e}\t{q_naive_99999:.8e}\t"
            f"{q_naive_s1:.8e}"
        )

    return "\n".join(lines) + "\n"


def build_fig3b_growth_rate() -> str:
    """Build `fig3b_growth_rate.dat` across `1 - sigma in [1e-6, 2e-1]`."""
    lines = [
        "# Analytical per-qubit overhead factor b(sigma, M) for Fig. 3(b), M in {1, 4, 16}.",
        "# Equidistant 3-point fit k(n) = a*b^n + c at n in {7, 10, 13}, G(n,K) = n + K*(28n - 38).",
        "# Generated by paper/scripts/generate_data.py — do not edit manually.",
        "one_minus_sigma\tsigma\tb_M1\tb_M4\tb_M16",
    ]

    anchors = (7, 10, 13)
    dn = anchors[1] - anchors[0]
    num_pts = 120
    log_min = math.log10(1e-6)
    log_max = math.log10(0.2)

    for idx in range(num_pts + 1):
        frac = idx / num_pts
        eps = 10.0 ** (log_min + frac * (log_max - log_min))
        sigma = 1.0 - eps
        b_vals: list[str] = []
        for M in (1, 4, 16):
            ks: list[float] = []
            for n_anc in anchors:
                k_id = ideal_iteration_int(n_anc, M)
                g_tot = n_anc + k_id * (28 * n_anc - 38)
                ln_seff = g_tot * math.log1p(-eps)
                ks.append(
                    repetition_overhead(
                        n_anc, M, k_id, math.exp(ln_seff), ln_sigma_eff=ln_seff
                    )
                )
            b_est = ((ks[2] - ks[1]) / (ks[1] - ks[0])) ** (1.0 / dn)
            b_vals.append(f"{b_est:.6f}")

        lines.append(
            f"{eps:.8e}\t{sigma:.8f}\t{b_vals[0]}\t{b_vals[1]}\t{b_vals[2]}"
        )

    return "\n".join(lines) + "\n"


def _format_tex_sci(val: float, sig_figs: int = 2) -> str:
    """Format positive float `val` in LaTeX scientific notation `$m \\times 10^{e}$`."""
    exp = int(math.floor(math.log10(val)))
    mant = val / (10.0**exp)
    mant_rounded = round(mant, sig_figs)
    if mant_rounded >= 10.0:
        mant_rounded /= 10.0
        exp += 1
    return f"${mant_rounded:.{sig_figs}f} \\times 10^{{{exp}}}$"


def build_fig4_and_table1() -> tuple[str, str]:
    """Build `fig4_resource_budgets.dat` (`n in [6, 60]`) and `table1_rows.tex`."""
    fig4_lines = [
        "# Required 2-qubit gate infidelity (1 - sigma_2q) for Fig. 4, n in [6, 60], M = 1.",
        "# Gate counts: G_1q = n + K*(16n - 20), G_2q = K*(12n - 18), 1 - sigma_1q = alpha*(1 - sigma_2q).",
        "# Generated by paper/scripts/generate_data.py — do not edit manually.",
        "n\tinfid2q_k2_a01\tinfid2q_k2_a001\tinfid2q_k10_a01\tinfid2q_k10_a001",
    ]

    table_Benchmarks = {10, 20, 30, 40, 50, 60}
    table_lines = [
        "% Generated by paper/scripts/generate_data.py — do not edit manually.",
        "% Columns: n & K_ideal & G_1q & G_2q & (1-sigma_2q)[k<=2, alpha=0.1]"
        " & (1-sigma_2q)[k<=2, alpha=0.01] & (1-sigma_2q)[k<=10, alpha=0.1]"
        " & (1-sigma_2q)[k<=10, alpha=0.01] \\\\",
    ]

    for n in range(6, 61):
        e_k2_a01 = solve_infidelity_budget(n, 2.0, 0.1, 1)
        e_k2_a001 = solve_infidelity_budget(n, 2.0, 0.01, 1)
        e_k10_a01 = solve_infidelity_budget(n, 10.0, 0.1, 1)
        e_k10_a001 = solve_infidelity_budget(n, 10.0, 0.01, 1)

        fig4_lines.append(
            f"{n}\t{e_k2_a01:.8e}\t{e_k2_a001:.8e}\t{e_k10_a01:.8e}\t{e_k10_a001:.8e}"
        )

        if n in table_Benchmarks:
            k_id = ideal_iteration_int(n, 1)
            g1, g2 = gate_counts_1q_2q(n, k_id)
            k_str = f"${k_id}$" if k_id < 1000 else _format_tex_sci(float(k_id), 2)
            g1_str = _format_tex_sci(float(g1), 2)
            g2_str = _format_tex_sci(float(g2), 2)
            table_lines.append(
                f"{n} & {k_str} & {g1_str} & {g2_str} & "
                f"{_format_tex_sci(e_k2_a01, 2)} & {_format_tex_sci(e_k2_a001, 2)} & "
                f"{_format_tex_sci(e_k10_a01, 2)} & {_format_tex_sci(e_k10_a001, 2)} \\\\"
            )

    return "\n".join(fig4_lines) + "\n", "\n".join(table_lines) + "\n"


def generate_all_payloads() -> dict[str, str]:
    """Compute all deterministic `.dat` and `.tex` payloads in memory."""
    fig2_osc, fig2_peaks = build_fig2_oscillations_and_peaks()
    fig3a = build_fig3a_queries()
    fig3b = build_fig3b_growth_rate()
    fig4, table1 = build_fig4_and_table1()
    return {
        "fig2_oscillations.dat": fig2_osc,
        "fig2_peaks.dat": fig2_peaks,
        "fig3a_queries.dat": fig3a,
        "fig3b_growth_rate.dat": fig3b,
        "fig4_resource_budgets.dat": fig4,
        "table1_rows.tex": table1,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate or verify deterministic figure/table data for the PRA manuscript."
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="Target data directory (default: paper/data)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify on-disk files match generated payloads byte-for-byte without modifying disk",
    )
    args = parser.parse_args(argv)

    payloads = generate_all_payloads()
    out_dir: Path = args.output_dir

    if args.check:
        mismatches: list[str] = []
        for fname, expected in payloads.items():
            fpath = out_dir / fname
            if not fpath.is_file():
                mismatches.append(f"MISSING: {fpath}")
                continue
            actual = fpath.read_text(encoding="utf-8")
            if actual != expected:
                mismatches.append(f"STALE: {fpath}")

        if mismatches:
            for msg in mismatches:
                print(msg, file=sys.stderr)
            print(
                f"FAIL: {len(mismatches)} data file(s) out of sync; run "
                "`python3 -B paper/scripts/generate_data.py`",
                file=sys.stderr,
            )
            return 1

        print(f"OK: all {len(payloads)} data files in {out_dir} are up to date")
        return 0

    out_dir.mkdir(parents=True, exist_ok=True)
    for fname, content in payloads.items():
        (out_dir / fname).write_text(content, encoding="utf-8")
    print(f"Wrote {len(payloads)} deterministic data files to {out_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
