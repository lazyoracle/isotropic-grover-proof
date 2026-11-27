#!/usr/bin/env python3
"""Unit tests for `paper/scripts/generate_data.py`."""

from __future__ import annotations

import io
import math
from pathlib import Path
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

sys.path.insert(0, str(Path(__file__).resolve().parent))
import generate_data as gd  # noqa: E402


class GenerateDataTests(unittest.TestCase):
    def test_optimal_iteration_continuous_zero_derivative_and_ideal_limit(self) -> None:
        for n in (6, 10, 14, 20, 40):
            for M in (1, 4):
                if M >= (1 << n):
                    continue
                theta = math.asin(math.sqrt(math.ldexp(float(M), -n)))
                k_ideal_cont = math.pi / (4.0 * theta) - 0.5

                # Approaches K_ideal as gamma -> 1 (since K_ideal - K^* ~ (1 - gamma)/(4*theta^2))
                self.assertAlmostEqual(
                    gd.optimal_iteration_continuous(1.0, n, M),
                    k_ideal_cont,
                    places=10,
                )
                near_one_gamma = 1.0 - min(1e-12, 1e-11 * theta * theta)
                if near_one_gamma < 1.0:
                    self.assertAlmostEqual(
                        gd.optimal_iteration_continuous(near_one_gamma, n, M),
                        k_ideal_cont,
                        places=9,
                    )

                for gamma in (0.99, 0.999, 0.9999, 0.99999):
                    with self.subTest(n=n, M=M, gamma=gamma):
                        k_star = gd.optimal_iteration_continuous(gamma, n, M)
                        self.assertGreater(k_star, 0.0)
                        self.assertLessEqual(k_star, k_ideal_cont)

                        def pe_func(k_val: float) -> float:
                            return gd.noisy_grover_prob_continuous(
                                n, M, k_val, 1.0, gamma
                            )

                        # Scale central-difference step to peak width
                        h_k = 1e-5 * max(1.0, k_star)
                        deriv_num = (pe_func(k_star + h_k) - pe_func(k_star - h_k)) / (
                            2.0 * h_k
                        )
                        self.assertLess(abs(deriv_num), 1e-10)
                        step_check = 1e-2 * max(1.0, k_star)
                        self.assertGreaterEqual(
                            pe_func(k_star), pe_func(k_star + step_check)
                        )
                        self.assertGreaterEqual(
                            pe_func(k_star), pe_func(max(0.0, k_star - step_check))
                        )

    def test_repetition_overhead_precision_and_no_underflow_at_n60(self) -> None:
        n = 60
        M = 1
        theta = math.asin(math.sqrt(math.ldexp(1.0, -n)))
        k_ideal = max(1, round(math.pi / (4.0 * theta) - 0.5))

        # At sigma_eff = 0.0, p_e = 2^-60 (where naive 1.0 - p_e == 1.0 in float64!)
        k_zero = gd.repetition_overhead(n, M, k_ideal, 0.0)
        self.assertTrue(math.isfinite(k_zero))
        self.assertGreater(k_zero, 1e18)

        k_mid = gd.repetition_overhead(n, M, k_ideal, 0.5)
        k_high = gd.repetition_overhead(n, M, k_ideal, 0.999999)
        k_unit = gd.repetition_overhead(n, M, k_ideal, 1.0)

        for val in (k_mid, k_high, k_unit):
            self.assertTrue(math.isfinite(val))
            self.assertGreater(val, 0.0)

        self.assertAlmostEqual(k_unit, 1.0, places=12)
        self.assertGreater(k_zero, k_mid)
        self.assertGreater(k_mid, k_high)
        self.assertGreater(k_high, k_unit)

        # Also check degenerate p_ideal == 1 at n = 2, M = 1, K = 1
        self.assertEqual(gd.repetition_overhead(2, 1, 1, 1.0), 1.0)
        k_n2_noisy = gd.repetition_overhead(2, 1, 1, 0.9)
        self.assertGreater(k_n2_noisy, 1.0)

    def test_resource_budget_solver_recovers_target_overhead_up_to_n60(self) -> None:
        for n in (10, 20, 40, 60):
            theta = math.asin(math.sqrt(math.ldexp(1.0, -n)))
            k_ideal = max(1, round(math.pi / (4.0 * theta) - 0.5))
            g1 = n + k_ideal * (16 * n - 20)
            g2 = k_ideal * (12 * n - 18)
            for k_budget in (2.0, 10.0):
                for alpha in (0.1, 0.01):
                    with self.subTest(n=n, k_budget=k_budget, alpha=alpha):
                        infid2q = gd.solve_infidelity_budget(n, k_budget, alpha)
                        self.assertGreater(infid2q, 0.0)
                        self.assertLess(infid2q, 1.0)
                        ln_seff = g1 * math.log1p(-alpha * infid2q) + g2 * math.log1p(-infid2q)
                        achieved = gd.repetition_overhead(
                            n, 1, k_ideal, math.exp(ln_seff), ln_sigma_eff=ln_seff
                        )
                        self.assertAlmostEqual(
                            achieved / k_budget, 1.0, places=9
                        )

    def test_generate_files_deterministic_and_check_mode_detects_stale_files(self) -> None:
        expected_files = (
            "fig2_oscillations.dat",
            "fig2_peaks.dat",
            "fig3a_queries.dat",
            "fig3b_growth_rate.dat",
            "fig4_resource_budgets.dat",
            "table1_rows.tex",
        )
        with tempfile.TemporaryDirectory() as td:
            out_dir = Path(td)
            out, err = io.StringIO(), io.StringIO()
            with redirect_stdout(out), redirect_stderr(err):
                rc_gen = gd.main(["--output-dir", str(out_dir)])
            self.assertEqual(rc_gen, 0)

            for fname in expected_files:
                fpath = out_dir / fname
                self.assertTrue(fpath.is_file(), f"Missing generated file {fname}")
                text = fpath.read_text(encoding="utf-8")
                self.assertTrue(text.strip())
                if fname.endswith(".dat"):
                    data_lines = [
                        ln for ln in text.splitlines() if ln.strip() and not ln.startswith("#")
                    ]
                    self.assertGreater(len(data_lines), 2, fname)
                    # First non-comment line is column header; remaining rows must be finite floats
                    num_cols = len(data_lines[0].split())
                    for row in data_lines[1:]:
                        parts = row.split()
                        self.assertEqual(len(parts), num_cols, fname)
                        for cell in parts:
                            val = float(cell)
                            self.assertTrue(math.isfinite(val), f"Non-finite {cell} in {fname}")

            # Clean --check must exit 0
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                self.assertEqual(gd.main(["--output-dir", str(out_dir), "--check"]), 0)

            # Mutating a file must make --check fail (stale file detection)
            target = out_dir / "fig3b_growth_rate.dat"
            orig = target.read_text(encoding="utf-8")
            target.write_text(orig + "# stale edit\n", encoding="utf-8")
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                self.assertNotEqual(gd.main(["--output-dir", str(out_dir), "--check"]), 0)

            # Restoring and deleting a file must also make --check fail
            target.write_text(orig, encoding="utf-8")
            (out_dir / "table1_rows.tex").unlink()
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                self.assertNotEqual(gd.main(["--output-dir", str(out_dir), "--check"]), 0)

    def test_fig3a_strict_query_monotonicity_across_fidelities(self) -> None:
        content = gd.build_fig3a_queries()
        data_lines = [
            ln for ln in content.splitlines() if ln.strip() and not ln.startswith("#")
        ]
        headers = data_lines[0].split()
        rows = data_lines[1:]
        self.assertEqual(len(rows), 47)  # n = 4 .. 50

        for row_str in rows:
            cols = dict(zip(headers, row_str.split()))
            n = int(cols["n"])
            q_ideal = float(cols["Q_ideal"])
            q_opt_99999 = float(cols["Q_opt_s99999"])
            q_opt_9999 = float(cols["Q_opt_s9999"])
            q_opt_999 = float(cols["Q_opt_s999"])
            q_naive_99999 = float(cols["Q_naive_s99999"])
            q_naive_9999 = float(cols["Q_naive_s9999"])
            q_naive_999 = float(cols["Q_naive_s999"])

            with self.subTest(n=n):
                self.assertAlmostEqual(
                    q_ideal / gd._optimal_query_complexity_primitive(n, 1.0, 1),
                    1.0,
                    places=7,
                )
                self.assertLess(q_ideal, q_opt_99999)
                self.assertLess(q_opt_99999, q_opt_9999)
                self.assertLess(q_opt_9999, q_opt_999)
                self.assertLessEqual(q_opt_999, q_naive_999)
                self.assertLessEqual(q_opt_9999, q_naive_9999)
                self.assertLessEqual(q_opt_99999, q_naive_99999)


if __name__ == "__main__":
    unittest.main()
