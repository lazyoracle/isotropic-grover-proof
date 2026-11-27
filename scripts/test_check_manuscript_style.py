#!/usr/bin/env python3
"""Unit tests for `scripts/check_manuscript_style.py`."""

from __future__ import annotations

import io
from pathlib import Path
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_manuscript_style as cms  # noqa: E402


REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = REPO_ROOT / "IsotropicGroverProof"


class CheckManuscriptStyleTests(unittest.TestCase):
    def _check_tex(
        self,
        files: dict[str, str],
        *,
        entry_files: list[str] | None = None,
        lean_dir: Path | None = None,
    ) -> list[str]:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            written: dict[str, Path] = {}
            for rel, content in files.items():
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(content, encoding="utf-8")
                written[rel] = p
            targets = (
                [written[name] for name in entry_files]
                if entry_files is not None
                else list(written.values())
            )
            return cms.check_files(targets, lean_dir=lean_dir)

    def test_clean_modular_manuscript_and_lean_audit_pass(self) -> None:
        files = {
            "main.tex": (
                "% Main entry file\n"
                "\\documentclass[aps,pra,twocolumn]{revtex4-2}\n"
                "\\begin{document}\n"
                "\\affiliation{ETS de Ingenier\\'ia, Madrid, Spain}\n"
                "\\email{author@example.org}\n"
                "\\input{body}\n"
                "\\input{supplement_body}\n"
                "\\end{document}\n"
            ),
            "body.tex": (
                "\\section{Model and Exact Moments}\\label{sec:model}\n"
                "We formulate the pure-state error model on the unit sphere before "
                "deriving its second moments in Sec.~\\ref{sec:moments}.\n\n"
                "\\subsection{Spherical Geometry}\\label{sec:moments}\n"
                "As illustrated in Fig.~\\ref{fig:sphere} and summarized in "
                "Table~\\ref{tab:budgets}, the expected success probability satisfies\n"
                "\\begin{equation}\n"
                "p_e = \\sigma^{2G} p_{\\mathrm{ideal}} + \\frac{1 - \\sigma^{2G}}{N}, "
                "\\label{eq:mixture}\n"
                "\\end{equation}\n"
                "where $N = 2^n$ is the Hilbert-space dimension. Combining multi-step "
                "reflections with Eq.~\\eqref{eq:mixture} yields\n"
                "\\begin{align}\n"
                "a &= b + c \\\\[4pt]\n"
                "d &= \\left\\{ x \\right. \\label{eq:piece}.\n"
                "\\end{align}\n"
                "For unnumbered identities we also write\n"
                "\\begin{equation*}\n"
                "u = v. \\notag\n"
                "\\end{equation*}\n"
                "\\input{figures/fig1}\n"
                "\\begin{table}[t]\n"
                "\\caption{Resource budgets across register sizes.}\\label{tab:budgets}\n"
                "\\end{table}\n"
            ),
            "figures/fig1.tex": (
                "\\begin{figure}[t]\n"
                "\\caption{Tangent-normal decomposition on the real unit sphere.}\n"
                "\\label{fig:sphere}\n"
                "\\end{figure}\n"
            ),
            "supplement_body.tex": (
                "\\section{Formalization Architecture}\\label{sec:supp}\n"
                "The machine-checked Lean 4 development verifies Eq.~\\eqref{eq:mixture} "
                "and Eq.~\\eqref{eq:piece} with zero custom axioms.\n\n"
                "\\subsection{Verified Declarations}\\label{sec:supp-decls}\n"
                "Key theorems include \\texttt{IsotropicGrover.isotropicGrover\\_main}, "
                "\\texttt{IsotropicGrover.noisyTrajectoryHet\\_bilinear}, "
                "\\texttt{circuitFidelity\\_eq\\_prod\\_count}, "
                "\\texttt{noisyMultiGroverHet\\_succProb}, "
                "\\texttt{Circuit.size}, \\texttt{Circuit.count}, and "
                "\\texttt{Grover.p\\_succ} in \\texttt{Sequential.lean}, checked via "
                "\\texttt{lake build --wfail}.\n"
            ),
        }
        errs = self._check_tex(files, lean_dir=LEAN_DIR)
        self.assertEqual(errs, [])

    def test_rejects_banned_hype_and_llm_words_in_prose_and_captions(self) -> None:
        banned_samples = [
            "novel",
            "Novel",
            "delve",
            "pivotal",
            "underscore",
            "underscores",
            "groundbreaking",
            "unprecedented",
            "paradigm",
            "tapestry",
            "testament",
            "leverage",
            "leveraging",
            "seamlessly",
            "elucidate",
            "unravel",
            "Moreover",
            "notably",
            "Importantly",
            "interestingly",
            "Remarkably",
            "strikingly",
            "In conclusion",
        ]
        for word in banned_samples:
            with self.subTest(word=word):
                prose_errs = self._check_tex({"a.tex": f"This result is {word} for search.\n"})
                self.assertTrue(prose_errs, f"Expected banned word error for {word!r} in prose")
                cap_errs = self._check_tex(
                    {
                        "b.tex": (
                            "See Fig.~\\ref{fig:x}.\n"
                            "\\begin{figure}\n"
                            f"\\caption{{{word} oscillation regime.}}\\label{{fig:x}}\n"
                            "\\end{figure}\n"
                        )
                    }
                )
                self.assertTrue(cap_errs, f"Expected banned word error for {word!r} in caption")

        # Multi-word phrase split across newline
        split_errs = self._check_tex({"split.tex": "In\nconclusion, the bound holds.\n"})
        self.assertTrue(split_errs)

    def test_ignores_banned_words_in_comments_cite_keys_url_and_bibitem(self) -> None:
        clean = (
            "% A novel groundbreaking paradigm comment; delve, moreover, in conclusion.\n"
            "Prior work~\\cite{NovelParadigm2026,DelveLeverage2025} studied search "
            "at \\url{https://example.org/novel-paradigm}.\n"
            "\\begin{thebibliography}{9}\n"
            "\\bibitem{Novel2026} J. Doe, A novel groundbreaking paradigm.\n"
            "\\end{thebibliography}\n"
        )
        self.assertEqual(self._check_tex({"clean.tex": clean}), [])

        # Escaped percent \% does NOT start a comment, so banned word after \% is caught
        after_escaped_pct = "Error rates below 5\\% remain a novel regime.\n"
        self.assertTrue(self._check_tex({"pct.tex": after_escaped_pct}))

    def test_rejects_british_spellings_and_second_person_pronouns(self) -> None:
        bad_tokens = [
            "analyse",
            "analysing",
            "analysed",
            "modelling",
            "modelled",
            "behaviour",
            "characterises",
            "parameterises",
            "acknowledgements",
            "towards",
            "realisations",
            "initialisation",
            "fulfil",
            "you",
            "your",
            "You",
            "Your",
        ]
        for tok in bad_tokens:
            with self.subTest(token=tok):
                errs = self._check_tex({"doc.tex": f"Here {tok} appears in running prose.\n"})
                self.assertTrue(errs, f"Expected error for {tok!r}")

        # American spellings and valid English words must pass cleanly
        american = (
            "Our numerical analyses analyze the behavior modeled by this initialization "
            "and characterization toward fulfilling the cancellation bound in the "
            "acknowledgments.\n"
        )
        self.assertEqual(self._check_tex({"us.tex": american}), [])

    def test_ignores_british_and_pronouns_in_affiliation_email_bibitem_and_url(self) -> None:
        tex = (
            "\\affiliation{Centre for Quantum Behaviour,\n"
            "  harbour Road, Youville, UK}\n"
            "\\email{your.name@behaviour-modelling.ac.uk}\n"
            "Code is archived at \\url{https://github.com/you/behaviour-modelling}.\n\n"
            "\\bibitem{Fowler2012} A. Fowler, Surface codes: Towards practical quantum "
            "behaviour and initialisation.\n"
        )
        self.assertEqual(self._check_tex({"meta.tex": tex}), [])

    def test_equation_hygiene_rules(self) -> None:
        invalid_cases = {
            "inline_dd": "The identity is $$a = b.$$ Here $a$ is real.\n",
            "block_dd": "The identity is\n$$\na = b.\n$$\n",
            "bracket_display": "The identity is\n\\[\na = b.\n\\]\n",
            "blank_above_equation": (
                "The channel evaluates to\n\n"
                "\\begin{equation}\n"
                "a = b.\n"
                "\\end{equation}\n"
            ),
            "blank_above_align": (
                "The steps simplify to\n\n"
                "\\begin{align}\n"
                "a &= b.\n"
                "\\end{align}\n"
            ),
            "blank_inside_equation": (
                "The channel evaluates to\n"
                "\\begin{equation}\n"
                "a = b,\n\n"
                "\\end{equation}\n"
            ),
            "blank_inside_align": (
                "The steps simplify to\n"
                "\\begin{align}\n"
                "a &= b \\\\\n\n"
                "c &= d.\n"
                "\\end{align}\n"
            ),
            "missing_punct_plain": (
                "The channel evaluates to\n"
                "\\begin{equation}\n"
                "a = b\n"
                "\\end{equation}\n"
            ),
            "missing_punct_with_label": (
                "See Eq.~\\eqref{eq:bad} where\n"
                "\\begin{equation}\n"
                "a = b \\label{eq:bad}\n"
                "\\end{equation}\n"
            ),
            "missing_punct_with_notag": (
                "The channel evaluates to\n"
                "\\begin{align}\n"
                "a &= b \\notag\n"
                "\\end{align}\n"
            ),
            "null_right_dot_not_punct": (
                "The piecewise expression is\n"
                "\\begin{equation}\n"
                "f(x) = \\left\\{ x \\right.\n"
                "\\end{equation}\n"
            ),
        }
        for name, tex in invalid_cases.items():
            with self.subTest(case=name):
                errs = self._check_tex({"eq.tex": tex})
                self.assertTrue(errs, f"Expected equation hygiene error for {name}")

        valid_eqs = (
            "Using Eqs.~\\eqref{eq:before} and \\eqref{eq:after}, we write\n"
            "\\begin{equation}\n"
            "a = b, \\label{eq:after}\n"
            "\\end{equation}\n"
            "where $a$ equals $b$, and therefore\n"
            "\\begin{equation}\n"
            "c = d \\label{eq:before}.\n"
            "\\end{equation}\n"
            "In multi-line form,\n"
            "\\begin{align}\n"
            "x &= y \\notag \\\\[4pt]\n"
            "z &= w, \\notag\n"
            "\\end{align}\n"
            "while\n"
            "\\begin{align*}\n"
            "p &= q \\notag .\n"
            "\\end{align*}\n"
        )
        self.assertEqual(self._check_tex({"valid_eq.tex": valid_eqs}), [])

    def test_cross_references_uncited_floats_and_naked_sections(self) -> None:
        # Uncited fig and tab labels
        uncited_fig = (
            "\\begin{figure}\n"
            "\\caption{Uncited schematic.}\\label{fig:orphan}\n"
            "\\end{figure}\n"
        )
        self.assertTrue(
            any("fig:orphan" in e for e in self._check_tex({"f.tex": uncited_fig}))
        )

        uncited_tab = (
            "\\begin{table}\n"
            "\\caption{Uncited table.}\\label{tab:orphan}\n"
            "\\end{table}\n"
        )
        self.assertTrue(
            any("tab:orphan" in e for e in self._check_tex({"t.tex": uncited_tab}))
        )

        # Undefined \ref and \eqref
        undef_ref = "As shown in Sec.~\\ref{sec:missing} and Eq.~\\eqref{eq:missing}.\n"
        ref_errs = self._check_tex({"r.tex": undef_ref})
        self.assertTrue(any("sec:missing" in e for e in ref_errs))
        self.assertTrue(any("eq:missing" in e for e in ref_errs))

        # Entry file resolving \input{...} cross-file labels automatically
        input_files = {
            "entry.tex": "See Fig.~\\ref{fig:ext}.\n\\input{sub/fig_ext}\n",
            "sub/fig_ext.tex": (
                "\\begin{figure}\\caption{Plot.}\\label{fig:ext}\\end{figure}\n"
            ),
        }
        self.assertEqual(
            self._check_tex(input_files, entry_files=["entry.tex"]), []
        )

        # Duplicate \label inside \input-expanded child files must be caught
        dup_same_child = {
            "entry.tex": "See Eq.~\\eqref{eq:dup}.\n\\input{child}\n",
            "child.tex": (
                "First:\n\\begin{equation}\na = b.\\label{eq:dup}\n\\end{equation}\n"
                "Second:\n\\begin{equation}\nc = d.\\label{eq:dup}\n\\end{equation}\n"
            ),
        }
        dup_same_errs = self._check_tex(dup_same_child, entry_files=["entry.tex"])
        self.assertTrue(
            any("duplicate label 'eq:dup'" in e for e in dup_same_errs),
            dup_same_errs,
        )

        dup_across_children = {
            "entry.tex": "See Eq.~\\eqref{eq:shared}.\n\\input{c1}\n\\input{c2}\n",
            "c1.tex": "First:\n\\begin{equation}\na = b.\\label{eq:shared}\n\\end{equation}\n",
            "c2.tex": "Second:\n\\begin{equation}\nc = d.\\label{eq:shared}\n\\end{equation}\n",
        }
        dup_across_errs = self._check_tex(
            dup_across_children, entry_files=["entry.tex"]
        )
        self.assertTrue(
            any("duplicate label 'eq:shared'" in e for e in dup_across_errs),
            dup_across_errs,
        )

        dup_entry_and_child = {
            "entry.tex": (
                "\\section{Intro}\\label{sec:dup}\n"
                "Lead-in prose citing Sec.~\\ref{sec:dup}.\n"
                "\\input{sub}\n"
            ),
            "sub.tex": "\\section{Second}\\label{sec:dup}\nMore prose.\n",
        }
        dup_ec_errs = self._check_tex(
            dup_entry_and_child, entry_files=["entry.tex"]
        )
        self.assertTrue(
            any("duplicate label 'sec:dup'" in e for e in dup_ec_errs),
            dup_ec_errs,
        )

        # Naked \section followed directly by \subsection without lead-in prose
        naked = (
            "\\section{Complexity Analysis}\\label{sec:comp}\n\n"
            "\\subsection{Repetition Overhead}\\label{sec:rep}\n"
            "Here we derive the overhead.\n"
        )
        naked_errs = self._check_tex({"naked.tex": naked})
        self.assertTrue(naked_errs, "Expected error for naked section-to-subsection jump")

    def test_lean_declaration_audit_rejects_nonexistent_identifiers(self) -> None:
        bad_cases = (
            (
                "IsotropicGrover.nonexistent_thm",
                "Theorem \\texttt{IsotropicGrover.nonexistent\\_thm} does not exist.\n",
            ),
            (
                "nonexistent_lemma_xyz",
                "Lemma \\texttt{nonexistent\\_lemma\\_xyz} is missing.\n",
            ),
            (
                "Grover.nonexistent_fn",
                "External \\texttt{Grover.nonexistent\\_fn} is missing.\n",
            ),
            ("UnknownCapNs.size", "Bogus \\texttt{UnknownCapNs.size} must fail.\n"),
            (
                "c.nonexistent_proj",
                "Bogus \\texttt{c.nonexistent\\_proj} must fail.\n",
            ),
        )
        for expected_ident, snippet in bad_cases:
            with self.subTest(ident=expected_ident):
                errs = self._check_tex(
                    {"supplement_body.tex": snippet}, lean_dir=LEAN_DIR
                )
                self.assertTrue(any(expected_ident in e for e in errs), errs)

    def test_lean_audit_instances_variable_projections_and_standalone_cli_tools(
        self,
    ) -> None:
        valid_supp = (
            "Instance \\texttt{perpSphereMeasure\\_isProbMeasure} (also qualified as "
            "\\texttt{IsotropicGrover.perpSphereMeasure\\_isProbMeasure}), projections "
            "\\texttt{c.size}, \\texttt{c.count}, \\texttt{c.eval}, "
            "\\texttt{gates.length}, and \\texttt{S.card}, and tools "
            "\\texttt{elan}, \\texttt{lake}, \\texttt{git}, \\texttt{latexmk}, "
            "and \\texttt{python3} are all valid.\n"
        )
        self.assertEqual(
            self._check_tex({"supplement_body.tex": valid_supp}, lean_dir=LEAN_DIR),
            [],
        )

    def test_display_math_text_macro_preserves_masked_cite_and_catches_bad_prose(
        self,
    ) -> None:
        clean_eq = (
            "The identity reads\n"
            "\\begin{equation}\n"
            "a = b \\quad \\text{(see Ref.~\\cite{Novel2026} at "
            "\\url{https://example.org/behaviour})}.\n"
            "\\end{equation}\n"
        )
        self.assertEqual(self._check_tex({"eq_cite.tex": clean_eq}), [])

        bad_eq = (
            "The identity reads\n"
            "\\begin{equation}\n"
            "a = b \\quad \\text{for novel behaviour}.\n"
            "\\end{equation}\n"
        )
        bad_errs = self._check_tex({"eq_bad.tex": bad_eq})
        self.assertTrue(any("novel" in e for e in bad_errs), bad_errs)
        self.assertTrue(any("behaviour" in e for e in bad_errs), bad_errs)

    def test_rejects_latin_shorthands_and_contractions_in_prose(self) -> None:
        for bad in (
            "e.g.,",
            "etc.",
            "viz.",
            "cf.",
            "don't",
            "it's",
            "we'll",
            "can't",
            "won't",
            "isn't",
            "aren't",
            "doesn't",
        ):
            with self.subTest(bad=bad):
                errs = self._check_tex({"shorthand.tex": f"We avoid {bad} in prose.\n"})
                self.assertTrue(errs, f"Expected style error for {bad!r}")

        # Allowed: 'i.e.,' and standard possessives such as "Grover's"
        allowed = (
            "Grover's search rotates the state, i.e., amplifies the marked amplitude.\n"
        )
        self.assertEqual(self._check_tex({"allowed.tex": allowed}), [])

    def test_cli_main_exit_code_and_file_line_format(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            good = Path(td) / "good.tex"
            good.write_text("Plain factual physics prose.\n", encoding="utf-8")
            out, err = io.StringIO(), io.StringIO()
            with redirect_stdout(out), redirect_stderr(err):
                rc_good = cms.main(["--lean-dir", str(LEAN_DIR), str(good)])
            self.assertEqual(rc_good, 0)

            bad = Path(td) / "bad.tex"
            bad.write_text("Line one.\nThis novel approach delves deep.\n", encoding="utf-8")
            out2, err2 = io.StringIO(), io.StringIO()
            with redirect_stdout(out2), redirect_stderr(err2):
                rc_bad = cms.main([str(bad)])
            self.assertNotEqual(rc_bad, 0)
            combined = out2.getvalue() + err2.getvalue()
            self.assertIn(f"{bad}:2:", combined)


if __name__ == "__main__":
    unittest.main()
