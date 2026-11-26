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
from collections import Counter
from html.parser import HTMLParser
from pathlib import Path
import re
import subprocess
import sys
from typing import NamedTuple


STANDARD_MATHJAX_COMMANDS: frozenset[str] = frozenset(
    (
        # Greek letters
        "alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota "
        "kappa lambda mu nu xi pi varpi rho varrho sigma varsigma tau upsilon "
        "phi varphi chi psi omega Gamma Delta Theta Lambda Xi Pi Sigma Upsilon "
        "Phi Psi Omega "
        # Fonts & styles
        "mathrm mathbf mathbb mathcal mathit mathsf mathfrak mathscr "
        "operatorname text textbf textit textrm displaystyle textstyle "
        "scriptstyle scriptscriptstyle "
        # Accents & decorations
        "hat widehat tilde widetilde bar overline underline vec dot ddot boxed "
        # Fractions, roots, environments
        "frac tfrac dfrac binom sqrt begin end "
        # Delimiters & sizing
        "left right middle big Big bigg Bigg bigl bigr Bigl Bigr biggl biggr "
        "Biggl Biggr langle rangle lfloor rfloor lceil rceil lvert rvert lVert "
        "rVert vert Vert lbrace rbrace "
        # Big operators & trig/log functions
        "sum prod coprod int iint iiint oint bigcup bigcap bigoplus bigotimes "
        "sin cos tan cot sec csc arcsin arccos arctan sinh cosh tanh log ln exp "
        "lim sup inf min max arg det dim ker hom deg gcd Pr "
        # Relations, arrows, binary operators, misc symbols
        "in notin ni subset subseteq supset supseteq cup cap setminus emptyset "
        "varnothing forall exists neg land lor implies iff to rightarrow "
        "leftarrow leftrightarrow longrightarrow longleftarrow "
        "longleftrightarrow Rightarrow Leftarrow Leftrightarrow Longrightarrow "
        "mapsto longmapsto uparrow downarrow ne neq le leq ge geq ll gg approx "
        "sim simeq cong equiv propto perp parallel mid nmid cdot cdots ldots "
        "dots vdots ddots times div pm mp circ bullet star ast oplus ominus "
        "otimes oslash odot dagger ddagger top bot partial nabla infty ell Re "
        "Im wp aleph blacksquare square triangle "
        # Spacing
        "quad qquad thinspace negthinspace negmedspace negthickspace enspace "
        "mspace kern phantom hphantom vphantom"
    ).split()
)

ALLOWED_ENVIRONMENTS: frozenset[str] = frozenset(
    "aligned cases matrix pmatrix bmatrix vmatrix Vmatrix array".split()
)

TEXT_LIKE_MACROS: tuple[str, ...] = tuple(
    "mathrm text textbf textit textrm operatorname mathit mathbf mathsf".split()
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

_TEXT_MACRO_RE = re.compile(r"\\(" + "|".join(TEXT_LIKE_MACROS) + r")\s*\{")
_LEAN_ISOMETRY_RE = re.compile(r"\\simeq\s*_\s*\{\\ell\s*i\}")
_TABLE_DELIM_CELL_RE = re.compile(r"^\s*:?-+:?\s*$")
_BLOCK_INTERRUPT_RE = re.compile(r"^\s*(?:[-+*]\s|\d+[.)]\s|>|#)")
_FENCE_OPEN_RE = re.compile(r"^( {0,3})(?:(`{3,})([^`]*)|(~{3,})(.*))$")
_FENCE_CLOSE_RE = re.compile(r"^( {0,3})(`{3,}|~{3,})[ \t]*$")
_LIST_ITEM_RE = re.compile(r"^( {0,3})([-+*]|\d{1,9}[.)])(?:( +)(.*)|()())$")
_ATX_HEADING_RE = re.compile(r"^ {0,3}#{1,6}(?:[ \t]+|$)")
_THEMATIC_BREAK_RE = re.compile(
    r"^ {0,3}(?:-[ \t]*-[ \t]*-[-\s]*|\*[ \t]*\*[ \t]*\*[\*\s]*|_[ \t]*_[ \t]*_[_\s]*)$"
)
_RAW_MATH_RENDERER_RE = re.compile(
    r"<math-renderer\b[^>]*>(.*?)</math-renderer>", flags=re.DOTALL
)
_ARTIFACT_PATTERNS: tuple[tuple[re.Pattern[str], str], ...] = (
    (
        re.compile(r"\\(?:sin|cos|tan|arcsin|arccos|log|ln)(?:\^\d+)?!"),
        "stripped `\\!` after trig/log",
    ),
    (re.compile(r"\[\s*,\s*\]"), "stripped `[\\,]` -> `[,]`"),
    (re.compile(r",\s*;"), "stripped `\\;` -> `,;`"),
    (re.compile(r"(?<!\\)\\\[\d"), "stripped `\\\\[...]` -> `\\[`"),
    (re.compile(r"(?<!\\)\\ "), "stripped mid-line `\\\\` -> `\\ `"),
    (
        re.compile(r"(?<!\\),\s*d\\(?:theta|mu|nu|xi|delta)"),
        "stripped `\\,d...` -> `,d...`",
    ),
)


class MathSpan(NamedTuple):
    kind: str  # "inline", "display_dd", "display_fence"
    line: int
    tex: str


def _truncate(text: str, limit: int = 90) -> str:
    return text[: limit - 3] + "..." if len(text) > limit else text


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
    bad_ch = next((ch for ch in tex if ord(ch) > 127), None)
    if bad_ch is not None:
        errors.append(
            f"{context}: non-ASCII character {bad_ch!r} (U+{ord(bad_ch):04X}) inside math; "
            "use standard LaTeX macros instead"
        )

    # 2. Forbidden substrings
    if "\\texttt" in tex:
        errors.append(
            f"{context}: forbidden \\texttt inside math (use Markdown `code` outside math)"
        )
    if "\\\\\\" in tex:
        errors.append(f"{context}: triple backslash '\\\\\\' inside math")
    if _LEAN_ISOMETRY_RE.search(tex):
        errors.append(f"{context}: Lean isometry notation \\simeq_{{\\ell i}} inside math")

    # 3. No underscores (raw or escaped) inside \mathrm{...}, \text{...}, \operatorname{...}, etc.
    for m in _TEXT_MACRO_RE.finditer(tex):
        arg, _ = _extract_braced_arg(tex, m.end() - 1)
        if arg is not None and "_" in arg:
            errors.append(
                f"{context}: underscore inside \\{m.group(1)}{{{arg}}} "
                "(move Lean identifier outside math or use proper LaTeX subscript)"
            )

    # 4. Token-level scan for balanced {}, \begin/\end, \left/\right, and command allowlist
    brace_depth = 0
    env_stack: list[tuple[str, int]] = []
    left_right_stack: list[tuple[int, int]] = []  # (brace_depth, len(env_stack))
    macro_counts: Counter[str] = Counter()

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
                macro_counts[cmd] += 1

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
                    elif not env_stack:
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

            # Escaped non-letter (e.g. \\, \,, \;, \!, \{, \}, \|, \_)
            if nxt in ("\n", "\r"):
                errors.append(
                    f"{context}: trailing single backslash before newline inside math"
                )
                i += 1
                continue
            if nxt == "_":
                errors.append(
                    f"{context}: escaped underscore '\\_' inside math "
                    "(move code identifier outside math)"
                )
            i += 2
            continue

        if ch == "$":
            errors.append(f"{context}: unescaped '$' inside math expression")
        elif ch == "%":
            errors.append(
                f"{context}: unescaped '%' inside math expression "
                "(starts a TeX comment; escape as '\\%' or remove)"
            )
        elif ch == "{":
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
        lc, rc = macro_counts[left_cmd], macro_counts[right_cmd]
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
    return bool(cells) and all(_TABLE_DELIM_CELL_RE.match(cell) for cell in cells)


def _scan_backtick_run(line: str, bt_start: int) -> tuple[int, int]:
    """Return `(backtick_len, closing_index_or_neg1)` for an exact-length backtick run."""
    n = len(line)
    bt_end = bt_start
    while bt_end < n and line[bt_end] == "`":
        bt_end += 1
    bt_len = bt_end - bt_start

    j = bt_end
    while j < n:
        if line[j] != "`":
            j += 1
            continue
        run_end = j
        while run_end < n and line[run_end] == "`":
            run_end += 1
        if run_end - j == bt_len:
            return bt_len, j
        j = run_end
    return bt_len, -1


def _match_fence_open(subline: str) -> tuple[int, str, str] | None:
    """Match a CommonMark §4.5 opening fence on `subline` (0-3 spaces indent)."""
    m = _FENCE_OPEN_RE.match(subline)
    if not m:
        return None
    rel_indent = len(m.group(1))
    if m.group(2) is not None:
        return rel_indent, m.group(2), m.group(3).strip()
    return rel_indent, m.group(4), m.group(5).strip()


def _is_closing_fence(subline: str, fence_marker: str) -> bool:
    """Return True if `subline` is a CommonMark §4.5 closing fence for `fence_marker`."""
    m = _FENCE_CLOSE_RE.match(subline)
    if not m:
        return False
    seq = m.group(2)
    return seq[0] == fence_marker[0] and len(seq) >= len(fence_marker)


def _starts_container_block(subline: str) -> bool:
    """Return True if `subline` (with 0-3 leading spaces) starts a block construct."""
    return bool(
        _match_fence_open(subline)
        or _LIST_ITEM_RE.match(subline)
        or _ATX_HEADING_RE.match(subline)
        or _THEMATIC_BREAK_RE.match(subline)
        or re.match(r"^ {0,3}>", subline)
    )


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
            bt_len, close_idx = _scan_backtick_run(line, i + 1)
            if bt_len != 1:
                errors.append(f"{path}:{line_no}: inline math must use single backtick $`...`$")
            if close_idx == -1:
                errors.append(f"{path}:{line_no}: unclosed backtick in $`...`$ inline math")
                return
            after_bt = close_idx + bt_len
            if after_bt >= n or line[after_bt] != "$":
                errors.append(f"{path}:{line_no}: $` code span not closed with matching `$")
                i = after_bt
                continue
            tex = line[i + 1 + bt_len : close_idx]
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
            bt_len, close_idx = _scan_backtick_run(line, i)
            if close_idx == -1:
                errors.append(f"{path}:{line_no}: unclosed Markdown backtick code span")
                return
            i = close_idx + bt_len
            continue

        # Any other `$` outside code spans is forbidden (plain `$...$` or inline `$$`)
        if ch == "$":
            snippet = _truncate(line.strip(), 100)
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

        if ch == "\\" and i + 1 < n:
            if line[i + 1].isalpha():
                j = i + 1
                while j < n and line[j].isalpha():
                    j += 1
                cmd = line[i:j]
                snippet = _truncate(line.strip(), 100)
                errors.append(
                    f"{path}:{line_no}: raw LaTeX command `{cmd}` outside math/code span: {snippet}"
                )
                return
            if line[i + 1] == "`":
                i += 2
                continue

        i += 1


def _collect_offline(path: Path) -> tuple[list[str], list[MathSpan]]:
    """Run offline structural and LaTeX checks and return `(errors, spans)`."""
    errors: list[str] = []
    spans: list[MathSpan] = []
    lines = path.read_text(encoding="utf-8").splitlines()

    in_fence = False
    fence_marker = ""
    fence_indent = 0
    fence_container_indent = 0
    fence_is_math = False
    fence_start_line = 0
    fence_lines: list[str] = []

    in_dd_block = False
    dd_start_line = 0
    dd_lines: list[str] = []

    list_indents: list[int] = []
    in_paragraph = False
    in_indented_code = False
    indented_code_base = 0
    in_table = False

    for idx, line in enumerate(lines):
        line_no = idx + 1
        lead = len(line) - len(line.lstrip(" "))
        is_blank = line.strip() == ""

        # 1. Inside fenced code block (```math or ```lean / ```bash / etc.)
        if in_fence:
            if not is_blank and lead < fence_container_indent:
                errors.append(
                    f"{path}:{fence_start_line}: unclosed fenced code block `{fence_marker}`"
                )
                if fence_is_math:
                    spans.append(
                        MathSpan("display_fence", fence_start_line, "\n".join(fence_lines))
                    )
                in_fence = False
                fence_marker = ""
                fence_is_math = False
                fence_lines = []
            else:
                sub_fence = line[min(fence_container_indent, len(line)) :]
                if not is_blank and _is_closing_fence(sub_fence, fence_marker):
                    if fence_is_math:
                        spans.append(
                            MathSpan("display_fence", fence_start_line, "\n".join(fence_lines))
                        )
                    in_fence = False
                    fence_marker = ""
                    fence_is_math = False
                    fence_lines = []
                    in_paragraph = False
                    continue

                if fence_is_math:
                    dedented = line[min(fence_indent, lead) :]
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
                in_paragraph = False
                continue

            if is_blank:
                errors.append(
                    f"{path}:{line_no}: blank line inside `$$...$$` display block "
                    "terminates the paragraph in CommonMark"
                )
            if _BLOCK_INTERRUPT_RE.match(line):
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

            # Inside top-level $$...$$, cmark-gfm strips \<ascii-punct> and single EOL `\`
            # (preserving only exact EOL `\\` without trailing spaces).
            line_without_eol_bs = re.sub(r"(?<!\\)\\\\$", "", line)
            bad_esc = re.search(r"\\([^A-Za-z\s]|$)", line_without_eol_bs)
            if bad_esc:
                if bad_esc.group(1) == "":
                    errors.append(
                        f"{path}:{line_no}: trailing single `\\` at end of line inside `$$...$$` "
                        "is stripped by cmark-gfm (use `\\\\` for line breaks)"
                    )
                else:
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

        # 3. Inside CommonMark §4.4 indented code block (4+ spaces beyond container)
        if in_indented_code:
            if is_blank or lead >= indented_code_base:
                continue
            in_indented_code = False

        if is_blank:
            in_paragraph = False
            in_table = False
            continue

        # Pop exited list-item containers
        if list_indents and lead < list_indents[-1]:
            outer_base = max((ind for ind in list_indents if ind <= lead), default=0)
            if not in_paragraph or _starts_container_block(line[outer_base:]):
                while list_indents and lead < list_indents[-1]:
                    list_indents.pop()

        container_indent = list_indents[-1] if list_indents else 0
        sub = line[min(container_indent, len(line)) :]

        if not in_table and _THEMATIC_BREAK_RE.match(sub):
            in_paragraph = False
            in_table = False
            continue

        # Track CommonMark §5.2 list-item indentation
        matched_list = False
        saw_empty_or_code_list_item = False
        while (m_list := _LIST_ITEM_RE.match(sub)) is not None:
            matched_list = True
            in_table = False
            marker_lead = len(m_list.group(1))
            marker_tok = m_list.group(2)
            spaces_after = len(m_list.group(3) or "")
            rest = m_list.group(4) or ""
            padding = 1 if (rest == "" or spaces_after >= 5) else spaces_after
            item_indent = container_indent + marker_lead + len(marker_tok) + padding
            list_indents.append(item_indent)
            container_indent = item_indent
            if rest != "" and spaces_after >= 5:
                in_indented_code = True
                indented_code_base = container_indent + 4
                in_paragraph = False
                saw_empty_or_code_list_item = True
                break
            if rest == "":
                in_paragraph = False
                saw_empty_or_code_list_item = True
                break
            sub = line[min(container_indent, len(line)) :]
        if saw_empty_or_code_list_item:
            continue
        if not matched_list and not in_paragraph and lead >= container_indent + 4:
            in_indented_code = True
            indented_code_base = container_indent + 4
            in_table = False
            continue

        # 4. Check for opening fenced code block (CommonMark §4.5: 0-3 spaces relative to container)
        fence_open = _match_fence_open(sub)
        if fence_open is not None:
            rel_indent, fence_marker, fence_info = fence_open
            in_table = False
            in_paragraph = False
            fence_container_indent = container_indent
            fence_indent = container_indent + rel_indent
            in_fence = True
            info_words = fence_info.split()
            fence_is_math = bool(info_words) and info_words[0] == "math"
            fence_start_line = line_no
            fence_lines = []
            if fence_is_math and fence_indent > 0:
                errors.append(
                    f"{path}:{line_no}: indented ```math block (indent {fence_indent}); "
                    "GitHub's MathFilter leaves `<pre lang=\"math\">` unrendered inside `<li>` "
                    "elements that also contain inline math — place display math at column 0"
                )
            continue

        # 5. Check for standalone column-0 `$$` opening line
        if line == "$$":
            list_indents.clear()
            in_table = False
            in_paragraph = False
            if idx > 0 and lines[idx - 1].strip() != "":
                errors.append(
                    f"{path}:{line_no}: opening `$$` must be preceded by a blank line"
                )
            in_dd_block = True
            dd_start_line = line_no
            dd_lines = []
            continue

        # 6. Track GFM pipe tables (with or without leading/trailing `|`)
        if in_table and ("|" not in line or _BLOCK_INTERRUPT_RE.match(line)):
            in_table = False

        is_table_header = (
            not in_table
            and "|" in line
            and idx + 1 < len(lines)
            and _is_gfm_table_delimiter_row(lines[idx + 1])
        )
        if _is_gfm_table_delimiter_row(line) and idx > 0 and "|" in lines[idx - 1]:
            in_table = True

        # 7. Ordinary Markdown line: scan inline code spans, `$`...`$`, and forbidden `$`
        _scan_inline_line(
            line,
            line_no,
            path,
            spans,
            errors,
            is_table_row=in_table or is_table_header,
        )
        in_paragraph = not bool(_ATX_HEADING_RE.match(sub))

    if in_fence:
        errors.append(f"{path}:{fence_start_line}: unclosed fenced code block `{fence_marker}`")
    if in_dd_block:
        errors.append(f"{path}:{dd_start_line}: unclosed `$$` display math block")

    for span in spans:
        errors.extend(validate_tex_expression(span.tex, f"{path}:{span.line} ({span.kind})"))

    return errors, spans


def check_offline(path: Path) -> list[str]:
    """Run offline structural and LaTeX checks on a Markdown file."""
    errors, _ = _collect_offline(path)
    return errors


class _GFMMathHTMLAuditor(HTMLParser):
    """Audit live HTML returned by `gh api /markdown -f mode=gfm`."""

    def __init__(self, path: Path) -> None:
        super().__init__(convert_charrefs=True)
        self.path = path
        self.errors: list[str] = []
        self.tag_stack: list[str] = []
        self.math_depth = 0
        self.code_or_pre_depth = 0
        self.current_math_line = 0
        self.current_math_chunks: list[str] = []
        self.math_node_count = 0

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        line_no, _ = self.getpos()

        if tag == "pre" and dict(attrs).get("lang") == "math":
            self.errors.append(
                f'{self.path}:HTML:{line_no}: `<pre lang="math">` was not converted to `<math-renderer>`'
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
                self._audit_math_renderer_content(
                    "".join(self.current_math_chunks), self.current_math_line
                )
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
            for leaked in ("$", "\\"):
                if leaked in data:
                    snippet = _truncate(" ".join(data.split()), 90)
                    self.errors.append(
                        f"{self.path}:HTML:{line_no}: leaked `{leaked}` in rendered HTML text: {snippet!r}"
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
            self.errors.append(
                f"{ctx}: unexpected delimiter wrapper in `<math-renderer>`: {stripped[:60]!r}"
            )
            tex = stripped

        for pat, desc in _ARTIFACT_PATTERNS:
            if pat.search(tex):
                self.errors.append(
                    f"{ctx}: cmark-gfm backslash-stripping artifact ({desc}): {tex.strip()[:90]!r}"
                )

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
    for m in _RAW_MATH_RENDERER_RE.finditer(html):
        raw_inner = m.group(1)
        line_no = html.count("\n", 0, m.start()) + 1
        for bad in ("<em", "<code", "<br", "\\\\\\", "\\texttt"):
            if bad in raw_inner:
                errors.append(
                    f"{path}:HTML:{line_no}: raw `<math-renderer>` contains `{bad}`: "
                    f"{raw_inner.strip()[:90]!r}"
                )

    auditor = _GFMMathHTMLAuditor(path)
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
        gh_errors, math_nodes = (
            check_gh_api(path, expected_span_count=len(offline_spans))
            if args.gh_api
            else ([], 0)
        )

        file_errors = offline_errors + gh_errors
        if file_errors:
            for err in file_errors:
                print(f"FAIL: {err}", file=sys.stderr)
            gh_summary = (
                f", {len(gh_errors)} live GFM HTML error(s) across {math_nodes} <math-renderer> node(s)"
                if args.gh_api
                else ""
            )
            print(
                f"SUMMARY {path}: {len(offline_errors)} offline error(s){gh_summary}",
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
