#!/usr/bin/env python3
"""Validate GitHub Flavored Markdown (GFM) math blocks and inline spans.

Supports two validation layers:
1. Offline structural & MathJax-LaTeX lint (default, fast, zero network/deps):
   - Enforces `$`...`$` raw-code inline math delimiters (forbids plain `$...$`
     so `cmark-gfm` never strips `\\,`/`\\|`/`\\{` or turns `_..._` into `<em>`).
   - Forbids raw `|` inside `$`...`$` on GFM table rows (use `\\vert`, `\\lVert`,
     `\\rVert` so table cell splitting never breaks inline math).
   - Enforces that `$$` appears only at column 0 as a standalone `$$` line
     surrounded by blank lines; forbids blank lines, Markdown block-interrupting
     prefixes, backticks, HTML-tag-like `<...` sequences, and `\\<ascii-punct>`
     (other than EOL `\\\\`) inside `$$...$$` where `cmark-gfm` strips or splits.
   - Inside ```` ```math ```` blocks, forbids bare trailing `\\\\` at end of line
     (requiring `\\\\[4pt]` etc. so GitHub's math filter does not emit `\\\\\\`).
   - Validates every math span/block for pure ASCII, balanced `{}` /
     `\\begin`–`\\end` / `\\left`–`\\right` / paired delimiters, zero `\\texttt`,
     zero `_` inside `\\mathrm`/`\\text`/`\\operatorname`, and standard MathJax v3
     LaTeX command names.
2. Live GitHub `/markdown` API verification (`--gh-api`):
   - Renders each file via `gh api /markdown -f mode=gfm` and verifies:
     * Zero `<pre lang="math">` fallbacks,
     * Zero `$` or `\\` characters in HTML text outside `<math-renderer>`,
       `<code>`, and `<pre>`,
     * Zero child HTML tags (`<em`, `<code`, `<br`, etc.), `\\\\\\`, `\\texttt`,
       `\\mathrm{..._...}`, or stripped-backslash artifacts inside any
       `<math-renderer>`, plus full LaTeX validation of every rendered math node.
"""

from __future__ import annotations

import argparse
from html.parser import HTMLParser
from pathlib import Path
import re
import subprocess
import sys
from typing import NamedTuple


STANDARD_MATHJAX_COMMANDS: frozenset[str] = frozenset(
    {
        # Greek letters
        "alpha",
        "beta",
        "gamma",
        "delta",
        "epsilon",
        "varepsilon",
        "zeta",
        "eta",
        "theta",
        "vartheta",
        "iota",
        "kappa",
        "lambda",
        "mu",
        "nu",
        "xi",
        "pi",
        "varpi",
        "rho",
        "varrho",
        "sigma",
        "varsigma",
        "tau",
        "upsilon",
        "phi",
        "varphi",
        "chi",
        "psi",
        "omega",
        "Gamma",
        "Delta",
        "Theta",
        "Lambda",
        "Xi",
        "Pi",
        "Sigma",
        "Upsilon",
        "Phi",
        "Psi",
        "Omega",
        # Fonts & styles
        "mathrm",
        "mathbf",
        "mathbb",
        "mathcal",
        "mathit",
        "mathsf",
        "mathfrak",
        "mathscr",
        "operatorname",
        "text",
        "textbf",
        "textit",
        "textrm",
        "displaystyle",
        "textstyle",
        "scriptstyle",
        "scriptscriptstyle",
        # Accents & decorations
        "hat",
        "widehat",
        "tilde",
        "widetilde",
        "bar",
        "overline",
        "underline",
        "vec",
        "dot",
        "ddot",
        "boxed",
        # Fractions, roots, environments
        "frac",
        "tfrac",
        "dfrac",
        "binom",
        "sqrt",
        "begin",
        "end",
        # Delimiters & sizing
        "left",
        "right",
        "middle",
        "big",
        "Big",
        "bigg",
        "Bigg",
        "bigl",
        "bigr",
        "Bigl",
        "Bigr",
        "biggl",
        "biggr",
        "Biggl",
        "Biggr",
        "langle",
        "rangle",
        "lfloor",
        "rfloor",
        "lceil",
        "rceil",
        "lvert",
        "rvert",
        "lVert",
        "rVert",
        "vert",
        "Vert",
        "lbrace",
        "rbrace",
        # Big operators & trig/log functions
        "sum",
        "prod",
        "coprod",
        "int",
        "iint",
        "iiint",
        "oint",
        "bigcup",
        "bigcap",
        "bigoplus",
        "bigotimes",
        "sin",
        "cos",
        "tan",
        "cot",
        "sec",
        "csc",
        "arcsin",
        "arccos",
        "arctan",
        "sinh",
        "cosh",
        "tanh",
        "log",
        "ln",
        "exp",
        "lim",
        "sup",
        "inf",
        "min",
        "max",
        "arg",
        "det",
        "dim",
        "ker",
        "hom",
        "deg",
        "gcd",
        "Pr",
        # Relations, arrows, binary operators, misc symbols
        "in",
        "notin",
        "ni",
        "subset",
        "subseteq",
        "supset",
        "supseteq",
        "cup",
        "cap",
        "setminus",
        "emptyset",
        "varnothing",
        "forall",
        "exists",
        "neg",
        "land",
        "lor",
        "implies",
        "iff",
        "to",
        "rightarrow",
        "leftarrow",
        "leftrightarrow",
        "longrightarrow",
        "longleftarrow",
        "longleftrightarrow",
        "Rightarrow",
        "Leftarrow",
        "Leftrightarrow",
        "Longrightarrow",
        "mapsto",
        "longmapsto",
        "uparrow",
        "downarrow",
        "ne",
        "neq",
        "le",
        "leq",
        "ge",
        "geq",
        "ll",
        "gg",
        "approx",
        "sim",
        "simeq",
        "cong",
        "equiv",
        "propto",
        "perp",
        "parallel",
        "mid",
        "nmid",
        "cdot",
        "cdots",
        "ldots",
        "dots",
        "vdots",
        "ddots",
        "times",
        "div",
        "pm",
        "mp",
        "circ",
        "bullet",
        "star",
        "ast",
        "oplus",
        "ominus",
        "otimes",
        "oslash",
        "odot",
        "dagger",
        "ddagger",
        "top",
        "bot",
        "partial",
        "nabla",
        "infty",
        "ell",
        "Re",
        "Im",
        "wp",
        "aleph",
        "blacksquare",
        "square",
        "triangle",
        # Spacing
        "quad",
        "qquad",
        "thinspace",
        "negthinspace",
        "negmedspace",
        "negthickspace",
        "enspace",
        "mspace",
        "kern",
        "phantom",
        "hphantom",
        "vphantom",
    }
)

ALLOWED_ENVIRONMENTS: frozenset[str] = frozenset(
    {
        "aligned",
        "cases",
        "matrix",
        "pmatrix",
        "bmatrix",
        "vmatrix",
        "Vmatrix",
        "array",
    }
)

TEXT_LIKE_MACROS: tuple[str, ...] = (
    "mathrm",
    "text",
    "textbf",
    "textit",
    "textrm",
    "operatorname",
    "mathit",
    "mathbf",
    "mathsf",
)

PAIRED_MACRO_DELIMITERS: tuple[tuple[str, str], ...] = (
    ("bigl", "bigr"),
    ("Bigl", "Bigr"),
    ("biggl", "biggr"),
    ("Biggl", "Biggr"),
    ("lVert", "rVert"),
    ("lvert", "rvert"),
    ("lbrace", "rbrace"),
    ("lfloor", "rfloor"),
    ("lceil", "rceil"),
)


class MathSpan(NamedTuple):
    kind: str  # "inline", "display_dd", "display_fence"
    line: int
    tex: str


def _extract_braced_arg(tex: str, brace_pos: int) -> tuple[str | None, int]:
    """Given `tex[brace_pos] == '{'`, return `(inner, index_after_closing_brace)`."""
    if brace_pos >= len(tex) or tex[brace_pos] != "{":
        return None, brace_pos
    depth = 0
    i = brace_pos
    while i < len(tex):
        ch = tex[i]
        if ch == "\\":
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return tex[brace_pos + 1 : i], i + 1
        i += 1
    return None, len(tex)


def validate_tex_expression(tex: str, context: str) -> list[str]:
    """Validate LaTeX syntax, delimiter balance, and MathJax v3 commands."""
    errors: list[str] = []

    if not tex.strip():
        errors.append(f"{context}: empty math expression")
        return errors

    # 1. Pure ASCII check (catches raw Lean Unicode like Ψ, σ, ℝ, ≃ₗᵢ inside math)
    for ch in tex:
        if ord(ch) > 127:
            errors.append(
                f"{context}: non-ASCII character {ch!r} (U+{ord(ch):04X}) inside math; "
                "use standard LaTeX macros instead"
            )
            break

    # 2. Forbidden substrings
    if "\\texttt" in tex:
        errors.append(f"{context}: forbidden \\texttt inside math (use Markdown `code` outside math)")
    if "\\\\\\" in tex:
        errors.append(f"{context}: triple backslash '\\\\\\' inside math")
    if re.search(r"\\simeq\s*_\s*\{\\ell\s*i\}", tex):
        errors.append(f"{context}: Lean isometry notation \\simeq_{{\\ell i}} inside math")

    # 3. No underscores (raw or escaped) inside \mathrm{...}, \text{...}, \operatorname{...}, etc.
    macro_pat = re.compile(r"\\(" + "|".join(TEXT_LIKE_MACROS) + r")\s*\{")
    for m in macro_pat.finditer(tex):
        macro_name = m.group(1)
        brace_idx = m.end() - 1
        arg, _ = _extract_braced_arg(tex, brace_idx)
        if arg is not None and "_" in arg:
            errors.append(
                f"{context}: underscore inside \\{macro_name}{{{arg}}} "
                "(move Lean identifier outside math or use proper LaTeX subscript)"
            )

    # 4. Token-level scan for balanced {}, \begin/\end, \left/\right, and command allowlist
    brace_depth = 0
    env_stack: list[tuple[str, int]] = []
    left_right_stack: list[tuple[int, int]] = []  # (brace_depth, len(env_stack))
    macro_counts: dict[str, int] = {}

    i = 0
    n = len(tex)
    while i < n:
        ch = tex[i]
        if ch == "\\":
            if i + 1 >= n:
                errors.append(f"{context}: trailing single backslash at end of math")
                break
            nxt = tex[i + 1]
            if nxt.isalpha():
                j = i + 1
                while j < n and tex[j].isalpha():
                    j += 1
                cmd = tex[i + 1 : j]
                macro_counts[cmd] = macro_counts.get(cmd, 0) + 1

                if cmd not in STANDARD_MATHJAX_COMMANDS:
                    errors.append(f"{context}: non-standard or unknown LaTeX command '\\{cmd}'")

                if cmd in ("begin", "end"):
                    k = j
                    while k < n and tex[k].isspace():
                        k += 1
                    if k >= n or tex[k] != "{":
                        errors.append(f"{context}: '\\{cmd}' missing '{{environment}}'")
                        i = j
                        continue
                    env_name, after_env = _extract_braced_arg(tex, k)
                    if env_name is None:
                        errors.append(f"{context}: unclosed '{{' in '\\{cmd}'")
                        i = j
                        continue
                    if env_name not in ALLOWED_ENVIRONMENTS:
                        errors.append(f"{context}: unsupported math environment '{env_name}'")
                    if cmd == "begin":
                        env_stack.append((env_name, brace_depth))
                    else:
                        if not env_stack:
                            errors.append(f"{context}: unmatched '\\end{{{env_name}}}'")
                        else:
                            open_env, open_depth = env_stack.pop()
                            if open_env != env_name:
                                errors.append(
                                    f"{context}: '\\begin{{{open_env}}}' closed by '\\end{{{env_name}}}'"
                                )
                            elif open_depth != brace_depth:
                                errors.append(
                                    f"{context}: unbalanced '{{}}' inside '\\begin{{{open_env}}}'"
                                )
                    i = after_env
                    continue

                if cmd == "left":
                    left_right_stack.append((brace_depth, len(env_stack)))
                elif cmd == "right":
                    if not left_right_stack:
                        errors.append(f"{context}: unmatched '\\right'")
                    else:
                        lr_depth, lr_env = left_right_stack.pop()
                        if lr_depth != brace_depth or lr_env != len(env_stack):
                            errors.append(
                                f"{context}: '\\left' and '\\right' at mismatched nesting depth"
                            )

                i = j
                continue
            else:
                # Escaped non-letter (e.g. \\, \,, \;, \!, \{, \}, \|, \_)
                if nxt == "_":
                    errors.append(
                        f"{context}: escaped underscore '\\_' inside math "
                        "(move code identifier outside math)"
                    )
                i += 2
                continue

        if ch == "{":
            brace_depth += 1
        elif ch == "}":
            brace_depth -= 1
            if brace_depth < 0:
                errors.append(f"{context}: unmatched closing '}}'")
                brace_depth = 0
        i += 1

    if brace_depth != 0:
        errors.append(f"{context}: unbalanced '{{' (unclosed depth {brace_depth})")
    for open_env, _ in env_stack:
        errors.append(f"{context}: unclosed '\\begin{{{open_env}}}'")
    if left_right_stack:
        errors.append(f"{context}: {len(left_right_stack)} unclosed '\\left' delimiter(s)")

    for left_cmd, right_cmd in PAIRED_MACRO_DELIMITERS:
        lc = macro_counts.get(left_cmd, 0)
        rc = macro_counts.get(right_cmd, 0)
        if lc != rc:
            errors.append(
                f"{context}: mismatched '\\{left_cmd}' ({lc}) vs '\\{right_cmd}' ({rc})"
            )

    return errors


def _is_gfm_table_delimiter_row(line: str) -> bool:
    """Return True if `line` is a GFM pipe-table delimiter row (with or without outer `|`)."""
    stripped = line.strip()
    if "|" not in stripped:
        return False
    cells = stripped.strip("|").split("|")
    return bool(cells) and all(re.match(r"^\s*:?-+:?\s*$", cell) for cell in cells)


def _scan_inline_line(
    line: str,
    line_no: int,
    path: Path,
    spans: list[MathSpan],
    errors: list[str],
    *,
    is_table_row: bool = False,
) -> None:
    """Scan a non-fenced, non-display-math line for `$`...`$` and illegal plain `$`."""
    is_table_row = is_table_row or line.lstrip().startswith("|")
    i = 0
    n = len(line)
    while i < n:
        ch = line[i]

        # Check `$` followed immediately by backtick(s): GitHub `$`...`$` inline math
        if ch == "$" and i + 1 < n and line[i + 1] == "`":
            # Count opening backticks
            bt_start = i + 1
            bt_end = bt_start
            while bt_end < n and line[bt_end] == "`":
                bt_end += 1
            bt_len = bt_end - bt_start
            if bt_len != 1:
                errors.append(
                    f"{path}:{line_no}: inline math must use single backtick $`...`$"
                )
            close_seq = "`" * bt_len
            close_idx = line.find(close_seq, bt_end)
            if close_idx == -1:
                errors.append(f"{path}:{line_no}: unclosed backtick in $`...`$ inline math")
                return
            after_bt = close_idx + bt_len
            if after_bt >= n or line[after_bt] != "$":
                errors.append(
                    f"{path}:{line_no}: $` code span not closed with matching `$"
                )
                i = after_bt
                continue
            tex = line[bt_end:close_idx]
            if tex.startswith(" ") and tex.endswith(" ") and len(tex) >= 2:
                errors.append(
                    f"{path}:{line_no}: avoid both leading and trailing spaces inside $`...`$"
                )
            if is_table_row and "|" in tex:
                errors.append(
                    f"{path}:{line_no}: raw '|' inside $`...`$ in GFM table row splits table cells; "
                    "use \\vert, \\lVert, or \\rVert"
                )
            spans.append(MathSpan("inline", line_no, tex))
            i = after_bt + 1
            continue

        # Normal Markdown code span `...` (not preceded by `$`)
        if ch == "`":
            bt_end = i
            while bt_end < n and line[bt_end] == "`":
                bt_end += 1
            bt_len = bt_end - i
            close_seq = "`" * bt_len
            close_idx = line.find(close_seq, bt_end)
            if close_idx == -1:
                errors.append(f"{path}:{line_no}: unclosed Markdown backtick code span")
                return
            i = close_idx + bt_len
            continue

        # Any other `$` outside code spans is forbidden (plain `$...$` or inline `$$`)
        if ch == "$":
            snippet = line.strip()
            if len(snippet) > 100:
                snippet = snippet[:97] + "..."
            if i + 1 < n and line[i + 1] == "$":
                errors.append(
                    f"{path}:{line_no}: `$$` must appear only at column 0 on its own line: {snippet}"
                )
            else:
                errors.append(
                    f"{path}:{line_no}: plain `$...$` inline math or stray `$` is forbidden "
                    f"(use $`...`$): {snippet}"
                )
            return

        i += 1


def _collect_offline(path: Path) -> tuple[list[str], list[MathSpan]]:
    """Run offline structural and LaTeX checks and return `(errors, spans)`."""
    errors: list[str] = []
    spans: list[MathSpan] = []
    lines = path.read_text(encoding="utf-8").splitlines()

    in_fence = False
    fence_marker = ""
    fence_indent = 0
    fence_is_math = False
    fence_start_line = 0
    fence_lines: list[str] = []

    in_dd_block = False
    dd_start_line = 0
    dd_lines: list[str] = []

    in_table = False

    for idx, line in enumerate(lines):
        line_no = idx + 1

        # 1. Inside fenced code block (```math or ```lean / ```bash / etc.)
        if in_fence:
            stripped = line.lstrip(" ")
            if stripped.startswith(fence_marker) and stripped.strip() == fence_marker:
                if fence_is_math:
                    spans.append(
                        MathSpan("display_fence", fence_start_line, "\n".join(fence_lines))
                    )
                in_fence = False
                fence_marker = ""
                fence_is_math = False
                fence_lines = []
                continue

            if fence_is_math:
                # Strip up to fence_indent leading spaces
                dedented = line[min(fence_indent, len(line) - len(line.lstrip(" "))) :]
                if re.search(r"\\\\\s*$", dedented):
                    errors.append(
                        f"{path}:{line_no}: bare trailing '\\\\' inside ```math block "
                        "(GitHub turns EOL '\\\\' into '\\\\\\'; use '\\\\[4pt]')"
                    )
                fence_lines.append(dedented)
            continue

        # 2. Inside top-level $$ ... $$ display block
        if in_dd_block:
            if line == "$$":
                if idx + 1 < len(lines) and lines[idx + 1].strip() != "":
                    errors.append(
                        f"{path}:{line_no}: closing `$$` must be followed by a blank line"
                    )
                spans.append(MathSpan("display_dd", dd_start_line, "\n".join(dd_lines)))
                in_dd_block = False
                dd_lines = []
                continue

            if line.strip() == "":
                errors.append(
                    f"{path}:{line_no}: blank line inside `$$...$$` display block "
                    "terminates the paragraph in CommonMark"
                )
            if re.match(r"^\s*(?:[-+*]\s|\d+[.)]\s|>|#)", line):
                errors.append(
                    f"{path}:{line_no}: continuation line inside `$$...$$` starts with a "
                    "Markdown block-interrupting marker (list, blockquote, or heading)"
                )
            if "`" in line:
                errors.append(
                    f"{path}:{line_no}: backtick `` ` `` inside `$$...$$` is parsed as "
                    "`<code>` by CommonMark"
                )
            if re.search(r"<[A-Za-z/!]", line):
                errors.append(
                    f"{path}:{line_no}: HTML-tag-like `<...` inside `$$...$$` is silently "
                    "stripped by GFM's sanitizer (put a space after `<` or use `\\langle`)"
                )

            if "$$" in line:
                errors.append(
                    f"{path}:{line_no}: `$$` inside display block must be on its own column-0 line"
                )

            # Inside top-level $$...$$, cmark-gfm strips \<ascii-punct> EXCEPT exact EOL `\\`!
            line_without_eol_break = re.sub(r"\\\\$", "", line)
            bad_esc = re.search(r"\\([^A-Za-z\s])", line_without_eol_break)
            if bad_esc:
                esc_seq = "\\" + bad_esc.group(1)
                errors.append(
                    f"{path}:{line_no}: `{esc_seq}` inside `$$...$$` is stripped by cmark-gfm "
                    "(use named MathJax macros like \\thinspace, \\mspace{4mu}, \\mspace{5mu}, "
                    "\\quad, \\negthinspace, \\lVert/\\rVert, \\lbrace/\\rbrace, "
                    "```math with \\:/\\;, or EOL `\\\\` without trailing spaces)"
                )
            if re.search(r"\\\\[ \t]+$", line):
                errors.append(
                    f"{path}:{line_no}: trailing spaces after EOL `\\\\` inside `$$...$$`"
                )

            dd_lines.append(line)
            continue

        # 3. Check for opening fenced code block (up to 3 spaces indentation, or inside list items)
        m_fence = re.match(r"^( *)(`{3,}|~{3,})(.*)$", line)
        if m_fence:
            in_table = False
            fence_indent = len(m_fence.group(1))
            fence_marker = m_fence.group(2)
            info = m_fence.group(3).strip()
            in_fence = True
            fence_is_math = info == "math"
            fence_start_line = line_no
            fence_lines = []
            if fence_is_math and fence_indent > 0:
                errors.append(
                    f"{path}:{line_no}: indented ```math block (indent {fence_indent}); "
                    "GitHub's MathFilter leaves `<pre lang=\"math\">` unrendered inside `<li>` "
                    "elements that also contain inline math — place display math at column 0"
                )
            continue

        # 4. Check for standalone column-0 `$$` opening line
        if line == "$$":
            in_table = False
            if idx > 0 and lines[idx - 1].strip() != "":
                errors.append(
                    f"{path}:{line_no}: opening `$$` must be preceded by a blank line"
                )
            in_dd_block = True
            dd_start_line = line_no
            dd_lines = []
            continue

        # 5. Track GFM pipe tables (with or without leading/trailing `|`)
        if in_table:
            if (
                line.strip() == ""
                or "|" not in line
                or re.match(r"^\s*(?:[-+*]\s|\d+[.)]\s|>|#)", line)
            ):
                in_table = False

        is_table_header = (
            not in_table
            and line.strip() != ""
            and "|" in line
            and idx + 1 < len(lines)
            and _is_gfm_table_delimiter_row(lines[idx + 1])
        )
        if _is_gfm_table_delimiter_row(line) and idx > 0 and "|" in lines[idx - 1]:
            in_table = True

        # 6. Ordinary Markdown line: scan inline code spans, `$`...`$`, and forbidden `$`
        _scan_inline_line(
            line,
            line_no,
            path,
            spans,
            errors,
            is_table_row=in_table or is_table_header,
        )

    if in_fence:
        errors.append(f"{path}:{fence_start_line}: unclosed fenced code block `{fence_marker}`")
    if in_dd_block:
        errors.append(f"{path}:{dd_start_line}: unclosed `$$` display math block")

    for span in spans:
        ctx = f"{path}:{span.line} ({span.kind})"
        errors.extend(validate_tex_expression(span.tex, ctx))

    return errors, spans


def check_offline(path: Path) -> list[str]:
    """Run offline structural and LaTeX checks on a Markdown file."""
    errors, _ = _collect_offline(path)
    return errors


class _GFMMathHTMLAuditor(HTMLParser):
    """Audit live HTML returned by `gh api /markdown -f mode=gfm`."""

    def __init__(self, path: Path, raw_html: str) -> None:
        super().__init__(convert_charrefs=True)
        self.path = path
        self.raw_lines = raw_html.splitlines()
        self.errors: list[str] = []
        self.tag_stack: list[str] = []
        self.math_depth = 0
        self.code_or_pre_depth = 0
        self.current_math_line = 0
        self.current_math_chunks: list[str] = []
        self.math_node_count = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attr_dict = dict(attrs)
        line_no, _ = self.getpos()

        if tag == "pre" and attr_dict.get("lang") == "math":
            self.errors.append(
                f"{self.path}:HTML:{line_no}: `<pre lang=\"math\">` was not converted to `<math-renderer>`"
            )

        if self.math_depth > 0:
            self.errors.append(
                f"{self.path}:HTML:{line_no}: nested HTML tag `<{tag}>` inside `<math-renderer>`"
            )

        self.tag_stack.append(tag)
        if tag == "math-renderer":
            self.math_depth += 1
            if self.math_depth == 1:
                self.current_math_line = line_no
                self.current_math_chunks = []
                self.math_node_count += 1
        elif tag in ("code", "pre"):
            self.code_or_pre_depth += 1

    def handle_endtag(self, tag: str) -> None:
        line_no, _ = self.getpos()
        if tag == "math-renderer" and self.math_depth > 0:
            self.math_depth -= 1
            if self.math_depth == 0:
                full_text = "".join(self.current_math_chunks)
                self._audit_math_renderer_content(full_text, self.current_math_line)
                self.current_math_chunks = []
        elif tag in ("code", "pre") and self.code_or_pre_depth > 0:
            self.code_or_pre_depth -= 1

        if self.tag_stack and self.tag_stack[-1] == tag:
            self.tag_stack.pop()
        elif tag in self.tag_stack:
            while self.tag_stack and self.tag_stack[-1] != tag:
                self.tag_stack.pop()
            if self.tag_stack:
                self.tag_stack.pop()
        else:
            self.errors.append(f"{self.path}:HTML:{line_no}: unexpected closing `</{tag}>`")

    def handle_data(self, data: str) -> None:
        line_no, _ = self.getpos()
        if self.math_depth > 0:
            self.current_math_chunks.append(data)
            return

        if self.code_or_pre_depth == 0:
            if "$" in data:
                snippet = " ".join(data.split())
                if len(snippet) > 90:
                    snippet = snippet[:87] + "..."
                self.errors.append(
                    f"{self.path}:HTML:{line_no}: leaked `$` in rendered HTML text: {snippet!r}"
                )
            if "\\" in data:
                snippet = " ".join(data.split())
                if len(snippet) > 90:
                    snippet = snippet[:87] + "..."
                self.errors.append(
                    f"{self.path}:HTML:{line_no}: leaked `\\` in rendered HTML text: {snippet!r}"
                )

    def _audit_math_renderer_content(self, content: str, html_line: int) -> None:
        ctx = f"{self.path}:HTML:{html_line} (<math-renderer>)"
        for bad_tag in ("<em", "<code", "<br"):
            if bad_tag in content:
                self.errors.append(f"{ctx}: contains `{bad_tag}` inside `<math-renderer>`")

        stripped = content.strip()
        if stripped.startswith("$$") and stripped.endswith("$$") and len(stripped) >= 4:
            tex = stripped[2:-2]
        elif stripped.startswith("$") and stripped.endswith("$") and len(stripped) >= 2:
            tex = stripped[1:-1]
        else:
            self.errors.append(f"{ctx}: unexpected delimiter wrapper in `<math-renderer>`: {stripped[:60]!r}")
            tex = stripped

        # Detect classic cmark-gfm backslash-stripping artifacts inside <math-renderer>
        artifact_patterns: tuple[tuple[str, str], ...] = (
            (r"\\(?:sin|cos|tan|arcsin|arccos|log|ln)(?:\^\d+)?!", "stripped `\\!` after trig/log"),
            (r"\[\s*,\s*\]", "stripped `[\\,]` -> `[,]`"),
            (r",\s*;", "stripped `\\;` -> `,;`"),
            (r"(?<!\\)\\\[\d", "stripped `\\\\[...]` -> `\\[`"),
            (r"(?<!\\)\\ ", "stripped mid-line `\\\\` -> `\\ `"),
            (r"(?<!\\),\s*d\\(?:theta|mu|nu|xi|delta)", "stripped `\\,d...` -> `,d...`"),
        )
        for pat, desc in artifact_patterns:
            if re.search(pat, tex):
                self.errors.append(f"{ctx}: cmark-gfm backslash-stripping artifact ({desc}): {tex.strip()[:90]!r}")

        self.errors.extend(validate_tex_expression(tex, ctx))


def check_gh_api(
    path: Path, expected_span_count: int | None = None
) -> tuple[list[str], int]:
    """Render `path` via `gh api /markdown -f mode=gfm` and audit the HTML."""
    if expected_span_count is None:
        _, offline_spans = _collect_offline(path)
        expected_span_count = len(offline_spans)

    res = subprocess.run(
        ["gh", "api", "/markdown", "-f", "mode=gfm", "-F", f"text=@{path}"],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        return (
            [f"{path}: `gh api /markdown` failed (exit {res.returncode}): {res.stderr.strip()}"],
            0,
        )

    html = res.stdout
    errors: list[str] = []

    # Also check raw `<math-renderer>...</math-renderer>` blocks for `<em`, `<code`, `<br`
    for m in re.finditer(r"<math-renderer\b[^>]*>(.*?)</math-renderer>", html, flags=re.DOTALL):
        raw_inner = m.group(1)
        line_no = html.count("\n", 0, m.start()) + 1
        for bad in ("<em", "<code", "<br", "\\\\\\", "\\texttt"):
            if bad in raw_inner:
                errors.append(
                    f"{path}:HTML:{line_no}: raw `<math-renderer>` contains `{bad}`: "
                    f"{raw_inner.strip()[:90]!r}"
                )

    auditor = _GFMMathHTMLAuditor(path, html)
    auditor.feed(html)
    errors.extend(auditor.errors)

    if auditor.math_node_count != expected_span_count:
        errors.append(
            f"{path}: rendered `<math-renderer>` count ({auditor.math_node_count}) "
            f"!= offline math span count ({expected_span_count})"
        )

    return errors, auditor.math_node_count


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check Markdown files for GFM + MathJax rendering defects."
    )
    parser.add_argument("files", nargs="+", type=Path, help="Markdown files to validate")
    parser.add_argument(
        "--offline",
        action="store_true",
        default=True,
        help="Run offline structural & LaTeX checks (enabled by default)",
    )
    parser.add_argument(
        "--gh-api",
        action="store_true",
        help="Also render via `gh api /markdown -f mode=gfm` and audit live GFM HTML",
    )
    args = parser.parse_args(argv)

    total_errors = 0
    for path in args.files:
        if not path.is_file():
            print(f"ERROR: file not found: {path}", file=sys.stderr)
            total_errors += 1
            continue

        offline_errors, offline_spans = _collect_offline(path)
        gh_errors: list[str] = []
        math_nodes = 0
        if args.gh_api:
            gh_errors, math_nodes = check_gh_api(
                path, expected_span_count=len(offline_spans)
            )

        file_errors = offline_errors + gh_errors
        if file_errors:
            for err in file_errors:
                print(f"FAIL: {err}", file=sys.stderr)
            print(
                f"SUMMARY {path}: {len(offline_errors)} offline error(s)"
                + (
                    f", {len(gh_errors)} live GFM HTML error(s) across {math_nodes} <math-renderer> node(s)"
                    if args.gh_api
                    else ""
                ),
                file=sys.stderr,
            )
            total_errors += len(file_errors)
        else:
            mode_msg = (
                f"offline + live GFM HTML ({math_nodes} <math-renderer> nodes)"
                if args.gh_api
                else "offline"
            )
            print(f"OK {path}: 0 errors ({mode_msg})")

    return 1 if total_errors > 0 else 0


if __name__ == "__main__":
    raise SystemExit(main())
