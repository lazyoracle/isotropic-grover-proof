# Issue #40 Design Document: Fix GitHub Flavored Markdown (GFM) Math Rendering in `english-proof.md` and `README.md`

## Empirical Root Cause Analysis (`gh api /markdown`)
Rendering the current `english-proof.md` and `README.md` through GitHub's live GFM pipeline (`gh api /markdown -f mode=gfm`) exposed **47 broken math lines in `english-proof.md`** and **3 broken math lines in `README.md`**, caused by five `cmark-gfm` + MathJax interactions:

1. **CommonMark `_` emphasis consuming inline `$...$` spans:** Whenever an inline `$...$` span contains `}_` followed later by `_\` or `_{` (e.g., `$\mathbf{e}_2 \sim \mu_\perp(\Psi)$`, `$\mathrm{E}[\mathbf{e}_2\mathbf{e}_2^\top] = \frac{P_\perp}{d-1}$`), `cmark-gfm` parses `_..._` as `<em>...</em>` (`$\mathbf{e}<em>2 \sim \mu</em>\perp(\Psi)$`), aborting math mode completely.
2. **Parenthesized closing `$...$)` (`($\sigma \in [0, 1)$)`):** Adjacent `)$)` prevents `cmark-gfm` from recognizing the closing `$` delimiter, leaking raw `$` text into HTML.
3. **Single-line / indented `$$...$$` display blocks:** Multi-line `$$\begin{aligned} ... \end{aligned}$$` where `$$` shares a line with `\begin{aligned}`, as well as indented `$$` blocks inside numbered/bulleted lists, fail `cmark-gfm`'s block-math parser and render as raw paragraph text with `_` turned into italics and `\\` collapsed to `\`.
4. **CommonMark backslash unescaping inside `$...$`:** Inside standard `$...$`, `cmark-gfm` strips `\,` → `,`, `\|` → `|`, `\{` → `{`, and `\_` → `_` *before* MathJax runs.
5. **Lean identifiers inside math (`\texttt{norm\_ketToReal}`, `\mathrm{Grover.p\_succ}`):** Unescaped underscores inside `\texttt` or `\mathrm` trigger MathJax subscript errors or unintended subscripts (`p_s` + `ucc`).

## Solution Design

1. **Use GitHub's Raw-Code Inline Math Delimiter (`` $`...`$ ``) Everywhere:**
   - GitHub's official `` $`...`$ `` syntax parses as a CommonMark code span first and emits `<math-renderer class="js-inline-math">$...$</math-renderer>` with **zero** backslash unescaping, **zero** `_` emphasis interference, and full support inside `**bold**`, headings, GFM tables, and `($`\sigma \in [0, 1)`$)`.

2. **Use Standalone Top-Level `$$` Blocks and ```` ```math ```` Inside Lists:**
   - At top level (column 0), format display math as standalone fenced blocks surrounded by blank lines:
     ```markdown
     $$
     ...
     $$
     ```
   - When a display equation is indented inside a numbered or bulleted list item (where indented `$$` fails in `cmark-gfm`), use an indented ```` ```math ```` fenced block (using `\\[4pt]` rather than bare trailing `\\` at end-of-line so GitHub's `math` fence filter does not emit `\\\`).

3. **Separate Lean Code Identifiers from Mathematical Notation:**
   - Remove all `\texttt{...}` and Lean underscores (`Grover.p\_succ`, `norm\_ketToReal`, `P\_perp\_apply`, `MState.uniform`, etc.) from inside math spans.
   - Cite Lean declarations in standard Markdown code spans (`` `...` ``) outside math delimiters, and use clean mathematical notation ($p_{\mathrm{succ}}(K, 2^n)$, $\operatorname{succProb}(n, \mathbf{v}, w)$, $\hat{\mathbf{e}}_i$, $U :: \mathit{rest}$, etc.) inside math mode.

4. **Live `gh api /markdown` Verification Gate:**
   - Verify both `english-proof.md` and `README.md` against `gh api /markdown` (`mode=gfm`), asserting:
     - 0 leaked `$` or `\` characters anywhere outside `<math-renderer>`, `<code>`, and `<pre>`;
     - 0 HTML tags (`<em>`, `<code>`, `<br>`), triple backslashes `\\\`, `\texttt`, or underscores inside `\mathrm`/`\text` within any `<math-renderer>`;
     - balanced `{}` / `\left`–`\right` / `\begin`–`\end` across all `<math-renderer>` blocks;
     - 100% `#check` verification of cited Lean declarations and clean `lake build --wfail`.
