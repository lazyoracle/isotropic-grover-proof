#!/usr/bin/env python3
"""Unit tests for `scripts/check_markdown_math.py`."""

from __future__ import annotations

from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_markdown_math as cmm  # noqa: E402


class CheckMarkdownMathTests(unittest.TestCase):
    def _check_md(self, content: str) -> list[str]:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "sample.md"
            path.write_text(content, encoding="utf-8")
            return cmm.check_offline(path)

    def test_valid_inline_dd_and_fence(self) -> None:
        md = (
            "Inline $`\\sigma \\in [0, 1]`$ and (`code $x$`).\n\n"
            "$$\n"
            "P(\\mathbf{y}, \\xi) = \\frac{1 - \\lVert\\mathbf{y}\\rVert^2}"
            "{\\lVert\\mathbf{y} - \\xi\\rVert^d}, \\qquad "
            "\\mathbf{y} \\in B^d,\\mspace{5mu} \\xi \\in S^{d-1}.\n"
            "$$\n\n"
            "```math\n"
            "\\begin{aligned}\n"
            "a &= b \\\\[4pt]\n"
            "c &= \\|d\\| + \\{1\\}\n"
            "\\end{aligned}\n"
            "```\n"
        )
        self.assertEqual(self._check_md(md), [])

    def test_rejects_medspace_and_thickspace(self) -> None:
        for bad_cmd in ("\\medspace", "\\thickspace"):
            with self.subTest(cmd=bad_cmd):
                errs = self._check_md(f"Inline $`a {bad_cmd} b`$.\n")
                self.assertTrue(
                    any("non-standard or unknown LaTeX command" in e for e in errs),
                    errs,
                )

    def test_rejects_dd_block_interrupts_backticks_and_html_tags(self) -> None:
        cases = {
            "blank_line": "\n$$\na = 1\n\nb = 2\n$$\n",
            "bullet_interrupt": "\n$$\na = 1\n- b = 2\n$$\n",
            "ordered_interrupt": "\n$$\na = 1\n1. b = 2\n$$\n",
            "ordered_paren_interrupt": "\n$$\na = 1\n2) b = 2\n$$\n",
            "blockquote_interrupt": "\n$$\na = 1\n> b = 2\n$$\n",
            "heading_interrupt": "\n$$\na = 1\n# heading\n$$\n",
            "backtick_in_dd": "\n$$\na = `x`\n$$\n",
            "html_open_tag_in_dd": "\n$$\nx<y>z\n$$\n",
            "html_close_tag_in_dd": "\n$$\nx</y>z\n$$\n",
            "html_comment_in_dd": "\n$$\nx<!--y-->z\n$$\n",
        }
        for name, md in cases.items():
            with self.subTest(case=name):
                errs = self._check_md(md)
                self.assertTrue(errs, f"Expected offline error for {name}")

    def test_allows_spaced_less_than_in_dd(self) -> None:
        errs = self._check_md("Text.\n\n$$\n0 < \\sigma < 1\n$$\n\nAfter.\n")
        self.assertEqual(errs, [])

    def test_rejects_pipes_in_gfm_tables_with_or_without_leading_pipe(self) -> None:
        with_outer = "| Col A | Col B |\n| :--- | :--- |\n| 1 | $`|\\psi\\rangle`$ |\n"
        without_outer = "Col A | Col B\n--- | ---\n1 | $`|\\psi\\rangle`$\n"
        header_pipe = "Col A | $`|\\psi\\rangle`$\n--- | ---\n1 | $`x`$\n"
        for name, md in (
            ("with_outer", with_outer),
            ("without_outer", without_outer),
            ("header_pipe", header_pipe),
        ):
            with self.subTest(case=name):
                errs = self._check_md(md)
                self.assertTrue(any("GFM table row" in e for e in errs), errs)

        valid_without_outer = (
            "Col A | Col B\n--- | ---\n1 | $`\\vert\\psi\\rangle`$\n\n"
            "Outside table $`|\\psi\\rangle`$ is allowed.\n"
        )
        self.assertEqual(self._check_md(valid_without_outer), [])

    def test_rejects_core_offline_violations(self) -> None:
        cases = {
            "plain_inline": "Hello $x + y$ world.\n",
            "inline_dd": "$$a = b$$\n",
            "indented_dd": "1. Item:\n   $$\n   a = b\n   $$\n",
            "dd_stripped_comma": "\n$$\na\\,b\n$$\n",
            "fence_bare_eol_bs": "```math\n\\begin{aligned}\na &= b \\\\\nc &= d\n\\end{aligned}\n```\n",
            "indented_fence": "1. Item:\n\n   ```math\n   a = b\n   ```\n",
            "texttt_in_math": "Inline $`\\texttt{foo}`$.\n",
            "underscore_in_mathrm": "Inline $`\\mathrm{Grover.p_succ}`$.\n",
            "unbalanced_brace": "Inline $`\\frac{1{2}`$.\n",
            "unbalanced_left_right": "Inline $`\\left( x + 1`$.\n",
            "unbalanced_env": "```math\n\\begin{aligned}\na &= b\n\\end{cases}\n```\n",
            "unicode_in_math": "Inline $`Ψ = 1`$.\n",
        }
        for name, md in cases.items():
            with self.subTest(case=name):
                self.assertTrue(self._check_md(md), f"Expected error for {name}")

    def test_gh_api_auditor_and_span_count_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "doc.md"
            path.write_text("Two spans: $`x`$ and $`y`$.\n", encoding="utf-8")

            fake_proc = mock.Mock(
                returncode=0,
                stdout='<p>Two spans: <math-renderer class="js-inline-math">$x$</math-renderer> and y.</p>',
                stderr="",
            )
            with mock.patch.object(cmm.subprocess, "run", return_value=fake_proc):
                errs, count = cmm.check_gh_api(path)
            self.assertEqual(count, 1)
            self.assertTrue(
                any("!= offline math span count (2)" in e for e in errs),
                errs,
            )


if __name__ == "__main__":
    unittest.main()
