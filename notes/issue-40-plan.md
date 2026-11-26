# Fix GFM Math Rendering in `english-proof.md` and `README.md` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Eliminate every GFM/MathJax rendering defect in `english-proof.md` and `README.md`, verified directly against GitHub's production `/markdown` renderer and Lean `#check`.

**Architecture:** Task 1 builds a reusable validation script `scripts/check_markdown_math.py` that renders Markdown files via `gh api /markdown` (`mode=gfm`) and audits every `<math-renderer>` and surrounding HTML text (confirming RED on the existing 50 broken lines), then converts all inline/display math in `english-proof.md` and `README.md` to GFM-safe `` $`...`$ `` inline spans, standalone top-level `$$\n...\n$$` blocks, and ```` ```math ```` blocks inside lists, with all Lean identifiers moved outside math mode into backtick code spans (GREEN).

**Tech Stack:** GitHub Flavored Markdown (`gh api /markdown`), MathJax LaTeX subset, Python 3 (`scripts/check_markdown_math.py`), Lean 4 (`lake env lean`).

**Spec:** `notes/issue-40-design.md`

## Global Constraints

- **Worktree isolation:** Work strictly inside `/home/anurag/isotropic-grover-proof/.claude/worktrees/issue-40`. Never modify `/home/anurag/isotropic-grover-proof` directly.
- **Mathematical & Lean fidelity:** Preserve 100% of the mathematical content, derivations, parameter-domain statements, and Lean declaration cross-references in `english-proof.md` and `README.md` without deleting or watering down any equations or explanations.
- **No `\texttt` or Lean underscores inside math:** Zero `\texttt` commands and zero underscores inside `\mathrm{...}` / `\text{...}` in any math span; cite Lean names in Markdown `` `...` `` outside math mode.
- **No `docs/` directory:** Never create a top-level `docs/` directory.

## Review Focus

- Trailing `\\` inside ```` ```math ```` blocks: GitHub's ```` ```math ```` filter turns bare EOL `\\` into `\\\`; always use `\\[4pt]` (or unindented top-level `$$\n...\n$$` outside lists) and assert zero `\\\` substrings inside `<math-renderer>`!
- Literal backticks inside `` $`...`$ ``: never use `` ` `` inside `` $`...`$ `` (use `'` for derivatives like `\tilde{G}_0'`).
- Escaped norms/sets/thin-spaces preserved: confirm `\|`, `\{`, `\}`, `\,`, `\!` survive intact inside `<math-renderer>` (which `` $`...`$ `` and top-level `$$\n...\n$$` preserve automatically, whereas plain `$...$` stripped them!).
- Equation labels/citations previously written as `\qquad (\texttt{lemma\_name})` inside `$$...$$`: move the Lean citation right below or beside the display block in prose (e.g. `(verified as` `` `lemma_name` `` `)`), keeping the display equation pure math.
- CI integration: invoke `python3 scripts/check_markdown_math.py --offline english-proof.md README.md` (offline structural lint with no GitHub token needed, plus `--gh-api` live GitHub GFM verification locally) so regressions are caught automatically.

---

### Task 1: Add GFM Math Validator (`scripts/check_markdown_math.py`) and Fix All Math Blocks in `english-proof.md` and `README.md`

**Files:**
- Create: `scripts/check_markdown_math.py`
- Modify: `english-proof.md`
- Modify: `README.md`
- Modify: `.github/workflows/lean_action_ci.yml` (add fast `python3 scripts/check_markdown_math.py english-proof.md README.md` lint step)

**Interfaces:**
- Consumes: Existing `english-proof.md` and `README.md`
- Produces: Zero-defect GFM-rendered `english-proof.md` and `README.md` verified by both `scripts/check_markdown_math.py --gh-api` (against GitHub's live `/markdown` API) and `scripts/check_markdown_math.py` (offline CI structural guard).

- [ ] **Step 1: Write `scripts/check_markdown_math.py` and confirm it catches all existing GFM math failures (RED)**

Create `scripts/check_markdown_math.py` supporting:
1. Offline structural checks (default, runs in CI without network):
   - No plain `$...$` inline math that isn't `` $`...`$ `` (enforcing `` $`...`$ `` uniformly for inline math so `cmark-gfm` never strips `\,`/`\|`/`\{` or eats `_..._`),
   - All `$$` lines appear only at column 0 as standalone `$$` lines (never indented inside lists and never sharing a line with equation text),
   - Inside ```` ```math ```` blocks, no bare trailing `\\` at end of line (require `\\[...]` if multi-line),
   - Inside every math span/block: balanced `{}` and `\begin{...}`/`\end{...}` and `\left`/`\right`, zero `\texttt`, and zero `_` inside `\mathrm{...}`/`\text{...}`.
2. `--gh-api` mode (live GitHub GFM HTML verification via `gh api /markdown -f mode=gfm`):
   - Zero `$` or `\` characters anywhere in rendered HTML text outside `<math-renderer>`, `<code>`, and `<pre>`,
   - Zero `<em`, `<code`, `<br`, `\\\`, `\texttt`, or `\mathrm{..._...}` inside any `<math-renderer>` element.

Run `python3 scripts/check_markdown_math.py --gh-api english-proof.md README.md` and confirm RED failure listing the existing broken spans.

- [ ] **Step 2: Fix all math blocks and inline spans in `english-proof.md` and `README.md` (GREEN)**

Update `english-proof.md` and `README.md`:
1. Convert all inline math `$...$` to `` $`...`$ `` (restoring any `\|`, `\{`, `\}`, `\,` where needed and removing any `\_` / `\texttt{...}` from inside math, placing Lean names in `` `...` `` outside math).
2. Convert all top-level display math to standalone `$$\n...\n$$` blocks surrounded by blank lines, and convert all list-indented display math to properly indented ```` ```math ```` blocks (using `\\[4pt]` for multi-line alignments).
3. Move parenthetical Lean theorem citations like `\qquad (\texttt{harmonicExtension\_eval})` out of `$$...$$` into clean prose/captions using Markdown backticks `` `harmonicExtension_eval` ``, and write `\mathrm{Grover.p\_succ}(K, 2^n)` in math as `p_{\mathrm{succ}}(K, 2^n)` (paired in prose with `` `Grover.p_succ` ``).
4. Add a fast step `- name: Check Markdown math formatting` running `python3 scripts/check_markdown_math.py english-proof.md README.md` near the top of `.github/workflows/lean_action_ci.yml` so CI permanently guards against GFM math regressions.

- [ ] **Step 3: Run live GitHub GFM verification, offline check, Lean `#check` audit, and `lake build --wfail`**

Run:
```bash
python3 scripts/check_markdown_math.py english-proof.md README.md
python3 scripts/check_markdown_math.py --gh-api english-proof.md README.md
PATH="$HOME/.elan/bin:$PATH" lake build --wfail
```
Plus verify all cited `IsotropicGrover.*` identifiers in `english-proof.md` and `README.md` via `PATH="$HOME/.elan/bin:$PATH" lake env lean --stdin`.
Expected: 0 errors across all checks!

- [ ] **Step 4: Commit**

```bash
git add scripts/check_markdown_math.py english-proof.md README.md .github/workflows/lean_action_ci.yml notes/issue-40-design.md notes/issue-40-plan.md
git commit -m "docs: fix all GFM math rendering in english-proof.md and README.md and add CI lint"
```
