#!/usr/bin/env python3
"""Lint Physical Review A LaTeX manuscript sources for author style & hygiene.

Enforces the codified rules in `notes/author-style-guide.md` and Section 6 of
`notes/issue-41-design.md` using Python 3 standard library modules only:
1. Banned hype/LLM lexicon (case-insensitive) in prose and captions, ignoring
   `%` comments, `\\cite{...}` keys, `\\url{...}`, and `\\bibitem` entries.
2. American English spelling (rejecting British `-ise`/`-our`/`-re`/`-ll-`
   slips and `towards`/`acknowledgements`/`fulfil`) and zero second-person
   pronouns (`you`/`your`), ignoring `\\affiliation{...}`, `\\email{...}`,
   `\\bibitem`, `\\cite{...}`, and `\\url{...}`.
3. Display-equation hygiene: forbids `$$...$$`, `\\[...\\]`, `eqnarray`, blank
   lines immediately above or inside display math environments, and display
   equations lacking terminal `,` or `.` (allowing `\\label{...}` or `\\notag`
   either before or after the terminal `,` or `.`).
4. Multi-file cross-reference, section-signpost, and Lean 4 declaration audit:
   rejects uncited `\\label{fig:...}` / `\\label{tab:...}`, undefined
   `\\ref{...}` / `\\eqref{...}` across modular `.tex` files (including
   `\\input{...}` targets), naked `\\section{...}` -> `\\subsection{...}` jumps
   without lead-in prose, and nonexistent Lean declarations inside
   `\\texttt{...}` when `--lean-dir` is supplied.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
from typing import NamedTuple


BANNED_HYPE_WORDS: frozenset[str] = frozenset(
    {
        # Hype adjectives & nouns
        "novel",
        "groundbreaking",
        "unprecedented",
        "revolutionary",
        "transformative",
        "pivotal",
        "paramount",
        "cornerstone",
        "cornerstones",
        "paradigm",
        "paradigms",
        "game-changer",
        "game-changers",
        "tapestry",
        "tapestries",
        "testament",
        "realm",
        "realms",
        "landscape",
        "landscapes",
        "synergy",
        "synergies",
        "synergistic",
        "holistic",
        "holistically",
        # LLM filler verbs & adverbs
        "delve",
        "delves",
        "delved",
        "delving",
        "underscore",
        "underscores",
        "underscored",
        "underscoring",
        "leverage",
        "leverages",
        "leveraged",
        "leveraging",
        "elucidate",
        "elucidates",
        "elucidated",
        "elucidating",
        "unravel",
        "unravels",
        "unraveled",
        "unravelled",
        "unraveling",
        "unravelling",
        "foster",
        "fosters",
        "fostered",
        "fostering",
        "bolster",
        "bolsters",
        "bolstered",
        "bolstering",
        "seamlessly",
        "intricate",
        "intricacies",
        # Mechanical filler transitions
        "moreover",
        "notably",
        "importantly",
        "interestingly",
        "remarkably",
        "strikingly",
        "crucially",
    }
)

BANNED_HYPE_PHRASES: tuple[tuple[str, ...], ...] = (
    ("in", "conclusion"),
    ("shed", "light"),
    ("sheds", "light"),
    ("shedding", "light"),
    ("game", "changer"),
    ("game", "changers"),
)

BRITISH_SPELLINGS: frozenset[str] = frozenset(
    {
        "analyse",
        "analysing",
        "analysed",
        "modelling",
        "modelled",
        "behaviour",
        "behaviours",
        "behavioural",
        "characterise",
        "characterises",
        "characterised",
        "characterising",
        "characterisation",
        "characterisations",
        "parameterise",
        "parameterises",
        "parameterised",
        "parameterising",
        "parameterisation",
        "parameterisations",
        "parametrise",
        "parametrises",
        "parametrised",
        "parametrising",
        "parametrisation",
        "acknowledgement",
        "acknowledgements",
        "towards",
        "realise",
        "realises",
        "realised",
        "realising",
        "realisation",
        "realisations",
        "initialise",
        "initialises",
        "initialised",
        "initialising",
        "initialisation",
        "initialisations",
        "fulfil",
        "fulfils",
        "colour",
        "colours",
        "coloured",
        "colouring",
        "centre",
        "centres",
        "centred",
        "centring",
        "favour",
        "favours",
        "favoured",
        "favouring",
        "favourable",
        "honour",
        "honours",
        "honoured",
        "neighbour",
        "neighbours",
        "neighbouring",
        "normalise",
        "normalises",
        "normalised",
        "normalising",
        "normalisation",
        "optimise",
        "optimises",
        "optimised",
        "optimising",
        "optimisation",
        "optimisations",
        "minimise",
        "minimises",
        "minimised",
        "minimising",
        "minimisation",
        "maximise",
        "maximises",
        "maximised",
        "maximising",
        "maximisation",
        "generalise",
        "generalises",
        "generalised",
        "generalising",
        "generalisation",
        "generalisations",
        "specialise",
        "specialises",
        "specialised",
        "specialising",
        "specialisation",
        "factorise",
        "factorises",
        "factorised",
        "factorising",
        "factorisation",
        "diagonalise",
        "diagonalises",
        "diagonalised",
        "diagonalising",
        "diagonalisation",
        "summarise",
        "summarises",
        "summarised",
        "summarising",
        "utilise",
        "utilises",
        "utilised",
        "utilising",
        "utilisation",
        "emphasise",
        "emphasises",
        "emphasised",
        "emphasising",
        "recognise",
        "recognises",
        "recognised",
        "recognising",
        "organise",
        "organises",
        "organised",
        "organising",
        "organisation",
        "stabilise",
        "stabilises",
        "stabilised",
        "stabilising",
        "stabilisation",
        "depolarise",
        "depolarises",
        "depolarised",
        "depolarising",
        "depolarisation",
        "labelled",
        "labelling",
        "cancelled",
        "cancelling",
        "travelled",
        "travelling",
        "grey",
    }
)

SECOND_PERSON_PRONOUNS: frozenset[str] = frozenset(
    {"you", "your", "yours", "yourself", "yourselves"}
)

FORBIDDEN_CONTRACTIONS: frozenset[str] = frozenset(
    {
        "don't",
        "doesn't",
        "didn't",
        "can't",
        "won't",
        "wouldn't",
        "shouldn't",
        "couldn't",
        "isn't",
        "aren't",
        "wasn't",
        "weren't",
        "hasn't",
        "haven't",
        "hadn't",
        "it's",
        "we're",
        "we've",
        "we'll",
        "they're",
        "they've",
        "they'll",
        "you're",
        "you've",
        "you'll",
        "let's",
        "that's",
        "there's",
        "here's",
        "what's",
    }
)

_LATIN_SHORTHAND_RE = re.compile(
    r"(?<![A-Za-z])(?:e\.g\.|etc\.|viz\.|cf\.)", flags=re.IGNORECASE
)
_CONTRACTION_RE = re.compile(
    r"(?<![A-Za-z])(?:"
    + "|".join(re.escape(c) for c in sorted(FORBIDDEN_CONTRACTIONS))
    + r")(?![A-Za-z])",
    flags=re.IGNORECASE,
)

DISPLAY_MATH_ENVS: frozenset[str] = frozenset(
    {
        "equation",
        "equation*",
        "align",
        "align*",
        "gather",
        "gather*",
        "multline",
        "multline*",
    }
)

IGNORED_PROSE_COMMANDS: frozenset[str] = frozenset(
    {
        "cite",
        "citep",
        "citet",
        "citeauthor",
        "citeyear",
        "nocite",
        "label",
        "ref",
        "eqref",
        "pageref",
        "autoref",
        "cref",
        "Cref",
        "url",
        "email",
        "affiliation",
        "input",
        "include",
        "bibliography",
        "bibliographystyle",
        "documentclass",
        "usepackage",
        "texttt",
        "mathtt",
        "mathrm",
        "operatorname",
        "DeclarePairedDelimiter",
        "newtheorem",
        "renewcommand",
        "newcommand",
        "providecommand",
        "pgfplotsset",
        "definecolor",
    }
)

CURATED_EXTERNAL_QUALIFIED: frozenset[str] = frozenset(
    {
        "Measure.haar",
        "Measure.dirac",
        "Measure.map",
        "Metric.sphere",
        "Classical.choice",
        "Quot.sound",
        "Circuit.size",
        "Circuit.count",
        "Circuit.size_eq_sum_count",
        "Circuit.eval",
        "Circuit.evolve",
        "Circuit.identity",
        "Circuit.gate",
        "Circuit.seq",
        "Circuit.H",
        "Circuit.X",
        "Circuit.Y",
        "Circuit.Z",
        "Circuit.S",
        "Circuit.T",
        "Circuit.CNOT",
        "Circuit.SWAP",
        "Circuit.TOFF",
        "Grover.p_succ",
        "Grover.p_succ_eq_sin_sq",
        "Grover.oracleUnitary",
        "Grover.diffuserUnitary",
        "Grover.groverMatrix",
        "Grover.groverState",
        "Grover.halfAngle",
        "Grover.groverAngle",
        "CPTPMap.ofUnitary",
        "MState.pure",
        "MState.uniform",
        "MState.exp_val",
        "Ket.basis",
        "Finset.univ",
        "Finset.card",
        "Set.Icc",
        "Set.Ico",
        "Set.Ioo",
        "Prod.snd",
        "Prod.fst",
        "Matrix.single",
        "Real.arcsin",
        "Real.sqrt",
        "Real.sin",
        "Real.cos",
        "Real.pi",
        "Module.finrank",
        "Qubit.H",
        "PrimitiveGate.x",
        "PrimitiveGate.y",
        "PrimitiveGate.z",
        "PrimitiveGate.h",
        "PrimitiveGate.s",
        "PrimitiveGate.t",
        "PrimitiveGate.cnot",
        "PrimitiveGate.swap",
        "PrimitiveGate.toffoli",
        "QuantumComputation.Circuits.ResourceCounting",
        "QuantumComputation.Algorithms.Grover",
    }
)

CURATED_EXTERNAL_UNQUALIFIED: frozenset[str] = frozenset(
    {
        # Libraries, packages, & namespaces
        "Lean",
        "Lake",
        "Mathlib",
        "Physlib",
        "QuantumInfo",
        "QuantumComputation",
        "IsotropicGroverProof",
        "IsotropicGrover",
        "Grover",
        # Core types & structures
        "Circuit",
        "PrimitiveGate",
        "QRegister",
        "Wire",
        "Qubit",
        "Ket",
        "MState",
        "CPTPMap",
        "POVM",
        "HermitianMat",
        "Measure",
        "Metric",
        "EuclideanSpace",
        "Submodule",
        "Module",
        "Finset",
        "Fin",
        "Matrix",
        "Set",
        "Real",
        "Complex",
        "List",
        "Prod",
        "ZMod",
        "Type",
        "Prop",
        "Nat",
        # Axioms, tactics, & keywords
        "propext",
        "sorry",
        "rfl",
        "by",
        "simp",
        "rw",
        "ext",
        "fun",
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "noncomputable",
        "namespace",
        "import",
        # Gate labels & external functions used unqualified in Lean modules
        "CNOT",
        "SWAP",
        "TOFF",
        "MCX",
        "hadamardUnitary",
        "uniform_superposition",
        "compProjObs",
        "intervalIntegral",
        "IsProbabilityMeasure",
        "Fintype",
        "MeasurableSpace",
        "ContinuousOn",
        "IsClosed",
    }
)

CLI_TOOL_NAMES: frozenset[str] = frozenset(
    {
        "elan",
        "lake",
        "lean",
        "git",
        "gh",
        "bash",
        "sh",
        "zsh",
        "python",
        "python3",
        "latexmk",
        "pdflatex",
        "xelatex",
        "lualatex",
        "bibtex",
        "biber",
        "pdfinfo",
        "pdftoppm",
    }
)

CLI_COMMAND_PREFIXES: tuple[str, ...] = (
    "lake ",
    "elan ",
    "git ",
    "bash ",
    "sh ",
    "python",
    "latexmk",
    "pdflatex",
    "bibtex",
    "pdfinfo",
    "pdftoppm",
    "cd ",
    "ln ",
    "mkdir ",
    "rm ",
    "cp ",
    "ls ",
    "export ",
    "PATH=",
)

CURATED_DOT_FIELDS: frozenset[str] = frozenset(
    {
        "size",
        "count",
        "eval",
        "evolve",
        "length",
        "card",
        "val",
        "vec",
        "re",
        "im",
        "m",
        "mats",
        "measure",
        "exp_val",
        "prod",
        "map",
        "fst",
        "snd",
    }
)

FILE_EXTENSIONS: tuple[str, ...] = (
    ".lean",
    ".tex",
    ".pdf",
    ".bib",
    ".bst",
    ".cls",
    ".sty",
    ".py",
    ".sh",
    ".md",
    ".toml",
    ".yml",
    ".yaml",
    ".dat",
    ".log",
    ".aux",
    ".bbl",
    ".png",
)


class LeanIndex(NamedTuple):
    local_decls: frozenset[str]
    module_names: frozenset[str]
    qualified_external: frozenset[str]
    unqualified_external: frozenset[str]
    dot_fields: frozenset[str]


def _strip_latex_comment_line(line: str) -> str:
    """Strip unescaped `%` comment from a single line while preserving `\\%`."""
    bs = 0
    for idx, ch in enumerate(line):
        if ch == "\\":
            bs += 1
            continue
        if ch == "%" and bs % 2 == 0:
            return line[:idx]
        bs = 0
    return line


def _strip_comments_preserve_lines(raw_text: str) -> tuple[list[str], str]:
    """Return `(raw_lines, comment_stripped_text)` with identical line counts."""
    raw_lines = raw_text.splitlines()
    stripped_lines = [_strip_latex_comment_line(ln) for ln in raw_lines]
    return raw_lines, "\n".join(stripped_lines)


def _line_offsets(text: str) -> list[int]:
    """Return starting character index of each 0-based line."""
    offsets = [0]
    for idx, ch in enumerate(text):
        if ch == "\n":
            offsets.append(idx + 1)
    return offsets


def _pos_to_line(pos: int, offsets: list[int]) -> int:
    """Convert 0-based character index `pos` to 1-based line number via binary search."""
    lo, hi = 0, len(offsets) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if offsets[mid] <= pos:
            lo = mid + 1
        else:
            hi = mid - 1
    return hi + 1


def _extract_delimited(
    text: str, start: int, open_ch: str = "{", close_ch: str = "}"
) -> tuple[str | None, int]:
    """Given `text[start] == open_ch`, return `(inner, index_after_close_ch)`."""
    n = len(text)
    if start >= n or text[start] != open_ch:
        return None, start
    depth = 0
    i = start
    while i < n:
        ch = text[i]
        if ch == "\\":
            i += 2 if (i + 1 < n and text[i + 1] != "\n") else 1
            continue
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return text[start + 1 : i], i + 1
        i += 1
    return None, n


def _mask_slice(buf: list[str], start: int, end: int) -> None:
    """Replace non-newline characters in `buf[start:end]` with spaces."""
    for i in range(start, min(end, len(buf))):
        if buf[i] != "\n":
            buf[i] = " "


def _skip_ws(text: str, pos: int) -> int:
    n = len(text)
    while pos < n and text[pos].isspace():
        pos += 1
    return pos


def _mask_macro_definitions(text: str) -> str:
    """Mask `\\newcommand`, `\\renewcommand`, `\\providecommand` bodies."""
    buf = list(text)
    for m in re.finditer(r"\\(?:re|provide)?newcommand\*?(?![A-Za-z])", text):
        pos = _skip_ws(text, m.end())
        # Name argument: either {\cmd} or \cmd
        if pos < len(text) and text[pos] == "{":
            _, pos = _extract_delimited(text, pos, "{", "}")
        elif pos < len(text) and text[pos] == "\\":
            pos += 1
            while pos < len(text) and text[pos].isalpha():
                pos += 1
        # Optional [nargs] and [default]
        for _ in range(2):
            pos = _skip_ws(text, pos)
            if pos < len(text) and text[pos] == "[":
                _, pos = _extract_delimited(text, pos, "[", "]")
        pos = _skip_ws(text, pos)
        if pos < len(text) and text[pos] == "{":
            _, end_pos = _extract_delimited(text, pos, "{", "}")
            _mask_slice(buf, m.start(), end_pos)
    return "".join(buf)


def _unmask_text_macros_in_math(buf: list[str], math_text: str, base_offset: int) -> None:
    """Restore prose inside `\\text{...}` / `\\textrm{...}` within a masked math span."""
    for m in re.finditer(r"\\text(?:rm|bf|it)?\s*\{", math_text):
        brace_idx = m.end() - 1
        inner, _ = _extract_delimited(math_text, brace_idx, "{", "}")
        if inner is not None:
            for k, ch in enumerate(inner):
                buf[base_offset + brace_idx + 1 + k] = ch


def _prepare_prose_text(comment_stripped: str) -> str:
    """Mask comments, citations, affiliations, emails, URLs, bibitems, code, and algebra."""
    buf = list(comment_stripped)
    n = len(comment_stripped)

    # 1. Mask thebibliography environments
    for m in re.finditer(
        r"\\begin\s*\{thebibliography\}.*?\\end\s*\{thebibliography\}",
        comment_stripped,
        flags=re.DOTALL,
    ):
        _mask_slice(buf, m.start(), m.end())

    # 2. Mask standalone \bibitem entries up to blank line, next \bibitem, or \end{...}
    for m in re.finditer(
        r"\\bibitem\b.*?(?=\n[ \t]*\n|\\bibitem\b|\\end\s*\{|\Z)",
        comment_stripped,
        flags=re.DOTALL,
    ):
        _mask_slice(buf, m.start(), m.end())

    # 3. Mask verbatim / lstlisting environments and \verb|...|
    for m in re.finditer(
        r"\\begin\s*\{(?:verbatim|lstlisting)\}.*?\\end\s*\{(?:verbatim|lstlisting)\}",
        comment_stripped,
        flags=re.DOTALL,
    ):
        _mask_slice(buf, m.start(), m.end())
    for m in re.finditer(r"\\verb([^A-Za-z\s]).*?\1", comment_stripped):
        _mask_slice(buf, m.start(), m.end())

    # 4. Mask \hyperref[target] bracket target (keep {visible text})
    for m in re.finditer(r"\\hyperref\s*\[", comment_stripped):
        _, end_br = _extract_delimited(comment_stripped, m.end() - 1, "[", "]")
        _mask_slice(buf, m.start(), end_br)

    # 5. Mask first {url} argument of \href{url}{text} (keep {text})
    for m in re.finditer(r"\\href(?![A-Za-z])", comment_stripped):
        pos = _skip_ws(comment_stripped, m.end())
        if pos < n and comment_stripped[pos] == "{":
            _, after_url = _extract_delimited(comment_stripped, pos, "{", "}")
            _mask_slice(buf, m.start(), after_url)

    # 6. Mask ignored commands with optional [...] and {arg}
    cmd_pattern = re.compile(
        r"\\(" + "|".join(sorted(IGNORED_PROSE_COMMANDS)) + r")\*?(?![A-Za-z])"
    )
    for m in cmd_pattern.finditer(comment_stripped):
        pos = _skip_ws(comment_stripped, m.end())
        while pos < n and comment_stripped[pos] == "[":
            _, pos = _extract_delimited(comment_stripped, pos, "[", "]")
            pos = _skip_ws(comment_stripped, pos)
        if pos < n and comment_stripped[pos] == "{":
            _, end_pos = _extract_delimited(comment_stripped, pos, "{", "}")
            _mask_slice(buf, m.start(), end_pos)
        else:
            _mask_slice(buf, m.start(), m.end())

    # 7. Mask display math environments (preserving \text{...} from already-masked buf)
    pre_disp = "".join(buf)
    env_alt = "|".join(re.escape(e) for e in sorted(DISPLAY_MATH_ENVS))
    for m in re.finditer(
        rf"\\begin\s*\{{({env_alt})\}}(.*?)\\end\s*\{{\1\}}",
        pre_disp,
        flags=re.DOTALL,
    ):
        _mask_slice(buf, m.start(), m.end())
        _unmask_text_macros_in_math(buf, pre_disp[m.start(2) : m.end(2)], m.start(2))

    # 8. Mask inline $...$ math (preserving \text{...} inside math)
    work = "".join(buf)
    i = 0
    while i < n:
        if work[i] == "\\":
            i += 2
            continue
        if work[i] == "$":
            # Skip $$ if present (caught by equation hygiene)
            if i + 1 < n and work[i + 1] == "$":
                i += 2
                continue
            j = i + 1
            while j < n:
                if work[j] == "\\":
                    j += 2
                    continue
                if work[j] == "$":
                    inner_math = work[i + 1 : j]
                    _mask_slice(buf, i, j + 1)
                    _unmask_text_macros_in_math(buf, inner_math, i + 1)
                    j += 1
                    break
                j += 1
            i = j
            continue
        i += 1

    # 9. Strip remaining control-sequence names (preserving braced prose like \caption{...})
    current = "".join(buf)
    for m in re.finditer(r"\\[A-Za-z@]+\*?|\\[^A-Za-z\n]", current):
        _mask_slice(buf, m.start(), m.end())

    return "".join(buf)


def _check_prose_lexicon(path: Path, comment_stripped: str, offsets: list[int]) -> list[str]:
    """Check banned hype words/phrases, British spellings, and 2nd-person pronouns."""
    errors: list[str] = []
    prose = _prepare_prose_text(comment_stripped)

    tokens: list[tuple[str, str, int]] = []  # (lower, raw, line_no)
    for m in re.finditer(r"[A-Za-z]+(?:-[A-Za-z]+)*", prose):
        raw_word = m.group(0)
        low = raw_word.lower()
        line_no = _pos_to_line(m.start(), offsets)
        tokens.append((low, raw_word, line_no))

        if low in BANNED_HYPE_WORDS:
            errors.append(
                f"{path}:{line_no}: banned hype/LLM word '{raw_word}' in prose/caption"
            )
        elif "-" in low:
            for part in low.split("-"):
                if part in BANNED_HYPE_WORDS:
                    errors.append(
                        f"{path}:{line_no}: banned hype/LLM word '{raw_word}' in prose/caption"
                    )
                    break

        if low in BRITISH_SPELLINGS:
            errors.append(
                f"{path}:{line_no}: British spelling '{raw_word}'; use APS American English"
            )
        elif "-" in low:
            for part in low.split("-"):
                if part in BRITISH_SPELLINGS:
                    errors.append(
                        f"{path}:{line_no}: British spelling '{raw_word}'; use APS American English"
                    )
                    break

        if low in SECOND_PERSON_PRONOUNS:
            errors.append(
                f"{path}:{line_no}: forbidden second-person pronoun '{raw_word}' in prose"
            )

    # Multi-word banned phrases (even across line wraps)
    for idx in range(len(tokens)):
        for phrase in BANNED_HYPE_PHRASES:
            plen = len(phrase)
            if idx + plen <= len(tokens):
                window = tuple(tokens[idx + k][0] for k in range(plen))
                if window == phrase:
                    line_no = tokens[idx][2]
                    joined = " ".join(tokens[idx + k][1] for k in range(plen))
                    errors.append(
                        f"{path}:{line_no}: banned filler phrase '{joined}' in prose/caption"
                    )

    # Latin shorthands (e.g., etc., viz., cf.) and informal contractions
    for m in _LATIN_SHORTHAND_RE.finditer(prose):
        line_no = _pos_to_line(m.start(), offsets)
        errors.append(
            f"{path}:{line_no}: forbidden Latin shorthand '{m.group(0)}' in prose; "
            "write out 'for example', 'such as', or 'compare'"
        )
    for m in _CONTRACTION_RE.finditer(prose):
        line_no = _pos_to_line(m.start(), offsets)
        errors.append(
            f"{path}:{line_no}: forbidden contraction '{m.group(0)}' in prose"
        )

    return errors


_TRAILING_EQ_HOUSEKEEPING_RE = re.compile(
    r"(?:"
    r"\s+"
    r"|\\label\s*\{[^{}]*\}"
    r"|\\tag\*?\s*\{[^{}]*\}"
    r"|\\(?:notag|nonumber)(?![A-Za-z])"
    r"|\\[,;!]"
    r"|\\(?:quad|qquad|thinspace|negthinspace)(?![A-Za-z])"
    r")+$"
)
_NULL_DELIMITER_DOT_RE = re.compile(r"\\(?:left|right|middle|[bB]igg?[lr])\s*\.$")


def _equation_has_terminal_punctuation(body: str) -> bool:
    """Return True iff display math `body` ends with sentence `,` or `.`."""
    trimmed = body
    while True:
        nxt = _TRAILING_EQ_HOUSEKEEPING_RE.sub("", trimmed)
        if nxt == trimmed:
            break
        trimmed = nxt

    if not trimmed:
        return False
    if trimmed.endswith(","):
        return True
    if trimmed.endswith("."):
        return not bool(_NULL_DELIMITER_DOT_RE.search(trimmed))
    return False


def _check_equation_hygiene(
    path: Path,
    raw_lines: list[str],
    comment_stripped: str,
    offsets: list[int],
) -> list[str]:
    """Check `$$`, `\\[...\\]`, blank lines around/in equations, and terminal `,`/`.`."""
    errors: list[str] = []

    # Mask verbatim/texttt before checking math delimiters
    scan_buf = list(comment_stripped)
    for m in re.finditer(
        r"\\begin\s*\{(?:verbatim|lstlisting)\}.*?\\end\s*\{(?:verbatim|lstlisting)\}",
        comment_stripped,
        flags=re.DOTALL,
    ):
        _mask_slice(scan_buf, m.start(), m.end())
    for m in re.finditer(r"\\verb([^A-Za-z\s]).*?\1", comment_stripped):
        _mask_slice(scan_buf, m.start(), m.end())
    scan_text = "".join(scan_buf)

    # 1. Reject unescaped $$ (preceded by an even number of backslashes)
    i = 0
    n = len(scan_text)
    while i < n:
        if scan_text[i] == "\\":
            bs = 0
            while i < n and scan_text[i] == "\\":
                bs += 1
                i += 1
            if i < n and scan_text[i] in ("[", "]") and bs % 2 == 1:
                line_no = _pos_to_line(i - 1, offsets)
                delim = "\\" + scan_text[i]
                errors.append(
                    f"{path}:{line_no}: forbidden '{delim}' display math delimiter; "
                    "use \\begin{equation} or \\begin{align}"
                )
            if bs % 2 == 1 and i < n and scan_text[i] == "$":
                i += 1
                continue
            continue

        if scan_text[i] == "$" and i + 1 < n and scan_text[i + 1] == "$":
            line_no = _pos_to_line(i, offsets)
            errors.append(
                f"{path}:{line_no}: forbidden '$$' display math delimiter; "
                "use \\begin{equation} or \\begin{align}"
            )
            i += 2
            continue
        i += 1

    # 2. Reject eqnarray / eqnarray*
    for m in re.finditer(r"\\begin\s*\{(eqnarray\*?)\}", scan_text):
        line_no = _pos_to_line(m.start(), offsets)
        errors.append(
            f"{path}:{line_no}: forbidden '\\begin{{{m.group(1)}}}' environment; use align"
        )

    # 3. Display math environments: blank lines & terminal punctuation
    env_alt = "|".join(re.escape(e) for e in sorted(DISPLAY_MATH_ENVS))
    for m in re.finditer(
        rf"\\begin\s*\{{({env_alt})\}}(.*?)\\end\s*\{{\1\}}",
        scan_text,
        flags=re.DOTALL,
    ):
        env_name = m.group(1)
        body = m.group(2)
        begin_line = _pos_to_line(m.start(), offsets)
        end_line = _pos_to_line(m.end() - 1, offsets)

        # Check blank line immediately above \begin{env} (skipping pure %-comment lines)
        prev_idx = begin_line - 2  # 0-based index of line above begin_line
        while (
            prev_idx >= 0
            and raw_lines[prev_idx].strip() != ""
            and _strip_latex_comment_line(raw_lines[prev_idx]).strip() == ""
        ):
            prev_idx -= 1
        if prev_idx >= 0 and raw_lines[prev_idx].strip() == "":
            errors.append(
                f"{path}:{begin_line}: blank line immediately before '\\begin{{{env_name}}}'; "
                "integrate display equation into host sentence"
            )

        # Check blank lines inside \begin{env}...\end{env}
        for line_idx in range(begin_line, end_line - 1):
            if raw_lines[line_idx].strip() == "":
                errors.append(
                    f"{path}:{line_idx + 1}: blank line inside '\\begin{{{env_name}}}...\\end{{{env_name}}}'"
                )

        # Check terminal ',' or '.'
        if not _equation_has_terminal_punctuation(body):
            errors.append(
                f"{path}:{end_line}: display equation '\\begin{{{env_name}}}' missing "
                "terminal ',' or '.' punctuation"
            )

        # Check blank line after \end{env} followed by lowercase continuation (e.g. 'where ...')
        next_idx = end_line  # 0-based index of line immediately after \end{env}
        saw_blank_after = False
        while next_idx < len(raw_lines):
            if raw_lines[next_idx].strip() == "":
                saw_blank_after = True
                next_idx += 1
                continue
            stripped_next = _strip_latex_comment_line(raw_lines[next_idx]).lstrip()
            if stripped_next == "":
                next_idx += 1
                continue
            if saw_blank_after and stripped_next[0].islower():
                errors.append(
                    f"{path}:{end_line + 1}: blank line after '\\end{{{env_name}}}' "
                    "before lowercase sentence continuation"
                )
            break

    return errors


def _check_section_lead_ins(
    path: Path, comment_stripped: str, offsets: list[int]
) -> list[str]:
    """Reject naked `\\section{...}` followed directly by `\\subsection{...}`."""
    errors: list[str] = []
    masked = _mask_macro_definitions(comment_stripped)
    headings: list[tuple[str, int, int]] = []  # (kind, start_pos, after_heading_pos)

    for m in re.finditer(r"\\(section|subsection)\*?(?![A-Za-z])", masked):
        kind = m.group(1)
        pos = _skip_ws(masked, m.end())
        if pos < len(masked) and masked[pos] == "[":
            _, pos = _extract_delimited(masked, pos, "[", "]")
            pos = _skip_ws(masked, pos)
        if pos < len(masked) and masked[pos] == "{":
            _, after_pos = _extract_delimited(masked, pos, "{", "}")
        else:
            after_pos = m.end()
        headings.append((kind, m.start(), after_pos))

    for idx in range(len(headings) - 1):
        kind, _, sec_end = headings[idx]
        next_kind, sub_start, _ = headings[idx + 1]
        if kind == "section" and next_kind == "subsection":
            between = masked[sec_end:sub_start]
            between = re.sub(r"\\label\s*\{[^{}]*\}", " ", between)
            between = re.sub(r"\\[A-Za-z@]+\*?(?:\s*\{[^{}]*\})?", " ", between)
            if not re.search(r"[A-Za-z]{2,}", between):
                sub_line = _pos_to_line(sub_start, offsets)
                errors.append(
                    f"{path}:{sub_line}: naked \\section followed directly by "
                    "\\subsection without lead-in prose"
                )

    return errors


def _strip_lean_comments(lean_src: str) -> str:
    """Remove `-- ...` line comments and nested `/- ... -/` block comments."""
    out: list[str] = []
    i = 0
    n = len(lean_src)
    block_depth = 0
    while i < n:
        if block_depth > 0:
            if lean_src[i : i + 2] == "/-":
                block_depth += 1
                i += 2
            elif lean_src[i : i + 2] == "-/":
                block_depth -= 1
                i += 2
            else:
                if lean_src[i] == "\n":
                    out.append("\n")
                i += 1
            continue

        if lean_src[i : i + 2] == "/-":
            block_depth = 1
            i += 2
            continue
        if lean_src[i : i + 2] == "--":
            while i < n and lean_src[i] != "\n":
                i += 1
            continue
        if lean_src[i] == '"':
            i += 1
            while i < n and lean_src[i] != '"':
                if lean_src[i] == "\\":
                    i += 2
                else:
                    i += 1
            i += 1
            out.append(" ")
            continue
        out.append(lean_src[i])
        i += 1
    return "".join(out)


_LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+([^\s({:\[]+)",
    flags=re.MULTILINE,
)


def build_lean_index(lean_dir: Path) -> LeanIndex:
    """Index declarations and referenced symbols across `lean_dir/*.lean`."""
    decls: set[str] = set()
    modules: set[str] = set()
    qual_ext: set[str] = set(CURATED_EXTERNAL_QUALIFIED)
    unqual_ext: set[str] = set(CURATED_EXTERNAL_UNQUALIFIED)
    dot_fields: set[str] = set(CURATED_DOT_FIELDS)

    lean_files = sorted(lean_dir.rglob("*.lean"))
    root_lean = lean_dir.with_suffix(".lean")
    if root_lean.is_file():
        lean_files.append(root_lean)

    for lf in lean_files:
        modules.add(lf.stem)
        clean = _strip_lean_comments(lf.read_text(encoding="utf-8"))
        for m in _LEAN_DECL_RE.finditer(clean):
            name = m.group(1)
            decls.add(name)
            if "." in name:
                decls.add(name.split(".")[-1])

        for qm in re.finditer(r"\b([A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+)\b", clean):
            qual_ext.add(qm.group(1))

        for dm in re.finditer(r"\.([A-Za-z_][A-Za-z0-9_']*)\b", clean):
            dot_fields.add(dm.group(1))

    return LeanIndex(
        local_decls=frozenset(decls),
        module_names=frozenset(modules),
        qualified_external=frozenset(qual_ext),
        unqualified_external=frozenset(unqual_ext | modules),
        dot_fields=frozenset(dot_fields),
    )


def _unescape_texttt_lean(raw: str) -> str:
    """Normalize LaTeX escapes inside `\\texttt{...}` to raw Lean text."""
    s = raw.strip()
    s = s.replace("\\_", "_")
    s = s.replace("\\#", "#")
    s = s.replace("\\&", "&")
    s = s.replace("\\%", "%")
    s = s.replace("$\\mathbb{C}$", "ℂ").replace("\\mathbb{C}", "ℂ")
    s = s.replace("$\\mathbb{R}$", "ℝ").replace("\\mathbb{R}", "ℝ")
    s = s.replace("$\\mathbb{N}$", "ℕ").replace("\\mathbb{N}", "ℕ")
    s = s.replace("~", " ")
    s = " ".join(s.split())
    return s


_LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'ℂℝℕ₀₁₂₃₄₅₆₇₈₉]*(?:\.[A-Za-z_][A-Za-z0-9_'ℂℝℕ₀₁₂₃₄₅₆₇₈₉]*)*$")
_GIT_REV_RE = re.compile(r"^[0-9a-f]{7,40}$")
_VERSION_RE = re.compile(r"^v?\d+\.\d+(?:\.\d+)*(?:[-+][A-Za-z0-9._-]+)?$")


def _audit_single_lean_ident(ident: str, index: LeanIndex) -> str | None:
    """Return an error reason if `ident` is an unknown Lean declaration, else None."""
    if ident.startswith("IsotropicGrover."):
        member = ident[len("IsotropicGrover.") :]
        if member in index.local_decls:
            return None
        return f"unknown IsotropicGrover declaration '{ident}'"

    if ident.startswith("IsotropicGroverProof."):
        sub = ident[len("IsotropicGroverProof.") :]
        if sub in index.module_names or sub in index.local_decls:
            return None
        return f"unknown IsotropicGroverProof module/declaration '{ident}'"

    if "." in ident:
        if ident in index.qualified_external or ident in index.local_decls:
            return None
        parts = ident.split(".")
        head = parts[0]
        # Allow term/variable dot-projections such as c.size, gates.length, S.card
        if (head[0].islower() or len(head) == 1) and all(
            seg in index.dot_fields for seg in parts[1:]
        ):
            return None
        return f"unknown qualified Lean declaration '{ident}'"

    # Single-character variables/gate symbols (X, Y, Z, H, S, T, c, n, etc.)
    if len(ident) <= 1:
        return None

    if ident in index.local_decls or ident in index.unqualified_external:
        return None

    return f"unknown Lean declaration '{ident}'"


def _check_lean_declarations(
    path: Path, comment_stripped: str, offsets: list[int], index: LeanIndex
) -> list[str]:
    """Verify Lean identifiers inside `\\texttt{...}` against `index`."""
    errors: list[str] = []
    masked = _mask_macro_definitions(comment_stripped)

    for m in re.finditer(r"\\texttt\s*\{", masked):
        brace_pos = m.end() - 1
        inner, _ = _extract_delimited(masked, brace_pos, "{", "}")
        if inner is None:
            continue
        line_no = _pos_to_line(m.start(), offsets)
        text = _unescape_texttt_lean(inner)
        if not text:
            continue

        # Ignore CLI tool names, commands, flags, file paths, versions, URLs, git hashes
        first_tok = text.split()[0]
        if first_tok in CLI_TOOL_NAMES or any(
            text.startswith(pfx) for pfx in CLI_COMMAND_PREFIXES
        ):
            continue
        if text.startswith("-") or "/" in text or ":" in text and "://" in text:
            continue
        if any(text.endswith(ext) for ext in FILE_EXTENSIONS):
            continue
        if _GIT_REV_RE.match(text) or _VERSION_RE.match(text):
            continue

        # Handle `#print axioms Foo` or `#check @Foo`
        cmd_m = re.match(r"^#(?:print\s+axioms|check)\s+@?(\S+)$", text)
        if cmd_m:
            target = cmd_m.group(1)
            if _LEAN_IDENT_RE.match(target):
                reason = _audit_single_lean_ident(target, index)
                if reason:
                    errors.append(f"{path}:{line_no}: {reason}")
            continue

        # Multi-token Lean expression/type signature: audit explicit IsotropicGrover.* refs
        if not _LEAN_IDENT_RE.match(text):
            for qm in re.finditer(
                r"\bIsotropicGrover\.[A-Za-z_][A-Za-z0-9_'ℂℝℕ₀₁₂₃₄₅₆₇₈₉]*", text
            ):
                reason = _audit_single_lean_ident(qm.group(0), index)
                if reason:
                    errors.append(f"{path}:{line_no}: {reason}")
            continue

        reason = _audit_single_lean_ident(text, index)
        if reason:
            errors.append(f"{path}:{line_no}: {reason}")

    return errors


def _resolve_input_target(base_file: Path, raw_target: str) -> Path | None:
    """Resolve `\\input{raw_target}` relative to `base_file.parent` (or parent root)."""
    target = raw_target.strip()
    if not target:
        return None
    candidates_rel = [Path(target)]
    if not Path(target).suffix:
        candidates_rel.append(Path(target + ".tex"))

    search_dirs = [base_file.parent]
    if base_file.parent.parent.is_dir():
        search_dirs.append(base_file.parent.parent)

    for d in search_dirs:
        for rel in candidates_rel:
            cand = (d / rel).resolve()
            if cand.is_file() and cand.suffix == ".tex":
                return cand
    return None


def _collect_labels_and_refs(
    path: Path, comment_stripped: str, offsets: list[int]
) -> tuple[list[tuple[str, int]], list[tuple[str, int, bool]]]:
    """Return `(labels, refs)` where refs are `(key, line_no, is_strict_ref)`."""
    masked = _mask_macro_definitions(comment_stripped)
    labels: list[tuple[str, int]] = []
    refs: list[tuple[str, int, bool]] = []

    for m in re.finditer(r"\\label\s*\{([^{}]+)\}", masked):
        key = m.group(1).strip()
        if key:
            labels.append((key, _pos_to_line(m.start(), offsets)))

    for m in re.finditer(
        r"\\(ref|eqref|pageref|autoref|cref|Cref)\s*\{([^{}]+)\}", masked
    ):
        cmd = m.group(1)
        is_strict = cmd in ("ref", "eqref")
        line_no = _pos_to_line(m.start(), offsets)
        for part in m.group(2).split(","):
            key = part.strip()
            if key:
                refs.append((key, line_no, is_strict))

    for m in re.finditer(r"\\hyperref\s*\[([^\[\]]+)\]", masked):
        key = m.group(1).strip()
        if key:
            refs.append((key, _pos_to_line(m.start(), offsets), False))

    return labels, refs


def check_files(paths: list[Path], lean_dir: Path | None = None) -> list[str]:
    """Validate `paths` and return `file:line: message` diagnostics."""
    errors: list[str] = []
    lean_index = build_lean_index(lean_dir) if lean_dir is not None else None

    explicit_resolved: dict[Path, Path] = {}
    ordered_explicit: list[Path] = []
    for p in paths:
        if not p.is_file():
            errors.append(f"{p}:1: file not found")
            continue
        rp = p.resolve()
        if rp not in explicit_resolved:
            explicit_resolved[rp] = p
            ordered_explicit.append(rp)

    # Expand \input / \include targets recursively for cross-file label/ref pooling
    all_pool_files: list[Path] = list(ordered_explicit)
    seen_pool: set[Path] = set(ordered_explicit)
    parsed_cache: dict[Path, tuple[list[str], str, list[int]]] = {}

    queue_idx = 0
    while queue_idx < len(all_pool_files):
        rp = all_pool_files[queue_idx]
        queue_idx += 1
        raw_text = rp.read_text(encoding="utf-8")
        raw_lines, stripped = _strip_comments_preserve_lines(raw_text)
        offsets = _line_offsets(stripped)
        parsed_cache[rp] = (raw_lines, stripped, offsets)

        for im in re.finditer(r"\\(?:input|include)\s*\{([^{}]+)\}", stripped):
            resolved_child = _resolve_input_target(rp, im.group(1))
            if resolved_child is not None and resolved_child not in seen_pool:
                seen_pool.add(resolved_child)
                all_pool_files.append(resolved_child)

    defined_labels: dict[str, tuple[Path, int]] = {}
    explicit_float_labels: list[tuple[str, Path, int]] = []
    explicit_strict_refs: list[tuple[str, Path, int]] = []
    referenced_keys: set[str] = set()

    for rp in all_pool_files:
        display_path = explicit_resolved.get(rp, rp)
        raw_lines, stripped, offsets = parsed_cache[rp]
        labels, refs = _collect_labels_and_refs(display_path, stripped, offsets)

        for key, line_no in labels:
            if key in defined_labels and rp in explicit_resolved:
                prev_path, prev_line = defined_labels[key]
                errors.append(
                    f"{display_path}:{line_no}: duplicate label '{key}' "
                    f"(already defined at {prev_path}:{prev_line})"
                )
            else:
                defined_labels[key] = (display_path, line_no)
            if rp in explicit_resolved and key.startswith(("fig:", "tab:")):
                explicit_float_labels.append((key, display_path, line_no))

        for key, line_no, is_strict in refs:
            referenced_keys.add(key)
            if rp in explicit_resolved and is_strict:
                explicit_strict_refs.append((key, display_path, line_no))

        if rp in explicit_resolved:
            errors.extend(_check_prose_lexicon(display_path, stripped, offsets))
            errors.extend(
                _check_equation_hygiene(display_path, raw_lines, stripped, offsets)
            )
            errors.extend(_check_section_lead_ins(display_path, stripped, offsets))
            if lean_index is not None:
                errors.extend(
                    _check_lean_declarations(
                        display_path, stripped, offsets, lean_index
                    )
                )

    for key, path_ref, line_no in explicit_strict_refs:
        if key not in defined_labels:
            errors.append(
                f"{path_ref}:{line_no}: undefined cross-reference '{key}'"
            )

    for key, path_lbl, line_no in explicit_float_labels:
        if key not in referenced_keys:
            errors.append(
                f"{path_lbl}:{line_no}: uncited figure/table label '{key}' "
                "(must be referenced via \\ref)"
            )

    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check LaTeX manuscript files for author style, equation hygiene, "
        "cross-references, and Lean 4 declaration accuracy."
    )
    parser.add_argument(
        "--lean-dir",
        type=Path,
        default=None,
        help="Optional Lean source directory (e.g., IsotropicGroverProof) for \\texttt{...} audit",
    )
    parser.add_argument("files", nargs="+", type=Path, help="LaTeX .tex files to lint")
    args = parser.parse_args(argv)

    if args.lean_dir is not None and not args.lean_dir.is_dir():
        print(f"ERROR: Lean directory not found: {args.lean_dir}", file=sys.stderr)
        return 1

    errors = check_files(args.files, lean_dir=args.lean_dir)
    if errors:
        for err in errors:
            print(err, file=sys.stderr)
        print(
            f"FAIL: {len(errors)} manuscript style violation(s) across {len(args.files)} file(s)",
            file=sys.stderr,
        )
        return 1

    print(f"OK: {len(args.files)} LaTeX file(s) passed manuscript style checks (0 errors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
