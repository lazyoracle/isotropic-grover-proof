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

    def _assert_invalid(self, cases: dict[str, str], expected_substr: str = "") -> None:
        for name, md in cases.items():
            with self.subTest(case=name):
                errs = self._check_md(md)
                self.assertTrue(errs, f"Expected error for {name}")
                if expected_substr:
                    self.assertTrue(any(expected_substr in e for e in errs), errs)

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
        self._assert_invalid(
            {cmd: f"Inline $`a {cmd} b`$.\n" for cmd in ("\\medspace", "\\thickspace")},
            "non-standard or unknown LaTeX command",
        )

    def test_rejects_dd_block_interrupts_backticks_and_html_tags(self) -> None:
        self._assert_invalid(
            {
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
        )

    def test_allows_spaced_less_than_in_dd(self) -> None:
        self.assertEqual(self._check_md("Text.\n\n$$\n0 < \\sigma < 1\n$$\n\nAfter.\n"), [])

    def test_rejects_pipes_in_gfm_tables_with_or_without_leading_pipe(self) -> None:
        self._assert_invalid(
            {
                "with_outer": "| Col A | Col B |\n| :--- | :--- |\n| 1 | $`|\\psi\\rangle`$ |\n",
                "without_outer": "Col A | Col B\n--- | ---\n1 | $`|\\psi\\rangle`$\n",
                "header_pipe": "Col A | $`|\\psi\\rangle`$\n--- | ---\n1 | $`x`$\n",
            },
            "GFM table row",
        )
        valid_without_outer = (
            "Col A | Col B\n--- | ---\n1 | $`\\vert\\psi\\rangle`$\n\n"
            "Outside table $`|\\psi\\rangle`$ is allowed.\n"
        )
        self.assertEqual(self._check_md(valid_without_outer), [])

    def test_rejects_core_offline_violations(self) -> None:
        self._assert_invalid(
            {
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
        )

    def test_rejects_unescaped_dollar_percent_and_single_eol_backslash_in_math(self) -> None:
        self._assert_invalid(
            {
                "inline_unescaped_dollar": "Inline $`a $ b`$.\n",
                "dd_unescaped_dollar": "\n$$\na = 1, \\text{ where } $b = 2$\n$$\n",
                "inline_unescaped_percent": "Inline $`\\frac{1}{100%}`$.\n",
                "dd_escaped_percent_stripped": "\n$$\n\\frac{1}{100\\%}\n$$\n",
                "dd_single_eol_backslash": "\n$$\na \\\nb\n$$\n",
                "fence_single_eol_backslash": "```math\na \\\nb\n```\n",
            }
        )
        valid = (
            "Inline $`100\\% + \\$1`$ is valid.\n\n"
            "$$\n"
            "a = 1 \\\\\n"
            "b = 2\n"
            "$$\n"
        )
        self.assertEqual(self._check_md(valid), [])

    def test_exact_backtick_runs_and_leaked_latex_commands(self) -> None:
        valid = (
            "See ` ``` ` and `` ($`\\sigma \\in [0, 1)`$) `` in the file.\n"
        )
        self.assertEqual(self._check_md(valid), [])
        self._assert_invalid(
            {
                "mismatched_backticks_hiding_math": "`` ```$x$ `\n",
                "misnested_single_backtick_escape": "Broken `($`\\sigma \\in [0, 1)`$)`.\n",
                "raw_latex_command_in_prose": "Prose with leaked \\sigma command.\n",
            }
        )

    def test_commonmark_fence_open_and_close_rules(self) -> None:
        valid = (
            "```math``` fences are inline code spans.\n\n"
            "    ```python\n"
            "    x = $1$\n\n"
            "```math\n"
            "a = b\n"
            "   `````   \n\n"
            "````markdown\n"
            "```math\n"
            "$not_checked$\n"
            "```\n"
            "````\n\n"
            "2. Outer\n"
            "   - Inner:\n"
            "     ```markdown\n"
            "     $$\n"
            "     ...\n"
            "     $$\n"
            "     ```\n"
        )
        self.assertEqual(self._check_md(valid), [])
        self._assert_invalid(
            {
                "inline_triple_bt_does_not_open_fence": (
                    "```math``` fences start a paragraph.\nNext line plain $x$.\n"
                ),
                "lazy_para_4sp_not_indented_code": "Paragraph\n    continuation $x$\n",
                "close_fence_4sp_does_not_close": "```python\nx = 1\n    ```\n",
                "close_fence_wrong_char": "```python\nx = 1\n~~~\n",
                "close_fence_trailing_text": "```python\nx = 1\n``` extra\n",
                "nested_list_indented_math_fence": (
                    "2. Outer\n   - Inner:\n     ```math\n     a = b\n     ```\n"
                ),
            }
        )

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

            bad_html_proc = mock.Mock(
                returncode=0,
                stdout=(
                    '<p><math-renderer class="js-inline-math">$a $ b$</math-renderer>'
                    '<math-renderer class="js-inline-math">$\\frac{1}{100%}$</math-renderer></p>'
                ),
                stderr="",
            )
            with mock.patch.object(cmm.subprocess, "run", return_value=bad_html_proc):
                errs2, count2 = cmm.check_gh_api(path, expected_span_count=2)
            self.assertEqual(count2, 2)
            self.assertTrue(any("unescaped '$'" in e for e in errs2), errs2)
            self.assertTrue(any("unescaped '%'" in e for e in errs2), errs2)


if __name__ == "__main__":
    unittest.main()
