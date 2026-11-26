# Author Writing Style Guide: Anurag Saha Roy (*Physical Review A* Edition)

Distilled from a raw-LaTeX rhetorical, syntactic, and mathematical analysis of:
1. `arXiv:2606.04817` — *Effect of isotropic errors on the complexity of Grover's algorithm* (Saha Roy & Lacalle, 2026)
2. `arXiv:2205.04829` — *Software tool-set for automated quantum system identification and device bring up* (Saha Roy *et al.*, 2022/2025)
3. `arXiv:2611.09779` — *Differentiable Digital Twins for Optimization, Calibration, and Characterization of Neutral-Atom- and Ion-based Quantum Computers* (Rossignolo, Bianchet, Saha Roy, & Machnes, 2026)

Adapted where required to American Physical Society (*Physical Review A*, `revtex4-2`) house standards.

---

## 1. Core Tone & Anti-Hype Invariants

Across ~16,000 words of analyzed source text, the prose is **sober, direct, physically grounded, and strictly anti-promotional**.

### Banned Lexicon (Enforced Programmatically, Exact Target Count = 0)
- **Hype adjectives & nouns:** `novel`, `groundbreaking`, `unprecedented`, `revolutionary`, `transformative`, `pivotal`, `paramount`, `cornerstone`, `paradigm`, `game-changer`, `tapestry`, `testament`, `realm`, `landscape`, `synergy`, `holistic`.
- **LLM filler verbs & adverbs:** `delve`, `underscore` / `underscores` / `underscoring`, `leverage` / `leveraging` (as a verb; use `use`, `employ`, or `exploit`), `elucidate`, `unravel`, `shed light`, `foster`, `bolster`, `seamlessly`, `intricate`.
- **Mechanical sentence-initial filler transitions:** `Moreover,`, `Notably,`, `Importantly,`, `Interestingly,`, `Remarkably,`, `Strikingly,`, `Crucially,`, `In conclusion,`.

### Preferred Functional Connectors
- **Contrast & concession:** `However,` (sparingly, 2–4 times per paper), `In contrast,`, `Conversely,`, `Nonetheless,`, `Unlike ...,`, and mid-sentence `while` or `whereas`.
- **Logical consequence:** `Thus,`, `Hence,`, `Consequently,`, and mid-verb `therefore` (*"The channel can therefore be pushed past every unitary gate"*).
- **Inline unpacking:** `i.e.,` (always followed by a comma) to translate an algebraic identity immediately into plain operational language. Avoid `e.g.,`, `etc.`, `viz.`, and `cf.` in running prose; write `such as` or `for example`.

---

## 2. Title, Abstract & Introduction Blueprints

### Title Formula
- Plain, descriptive sentence-case noun phrase (10–16 words).
- **No catchy two-part colon title** and no superlatives.

### Abstract Blueprint (5–6 Sentences, 125–155 Words, 20–28 Words/Sentence)
1. **S1 — Direct Premise:** State the physical or theoretical starting point without textbook throat-clearing (*"Isotropic pure-state errors on the Hilbert-space unit sphere resist conventional quantum error correction..."*).
2. **S2 — Knowledge Gap / Bottleneck:** Contrast prior frameworks or numerical observations against what remained open via `While ..., ...` or `Nonetheless, ...`.
3. **S3 — Primary Contribution:** Open with `Here we derive...` or `In this work, we prove...` naming the exact analytical result.
4. **S4 — Mechanism & Generality:** State the mathematical mechanism (`By combining...`) and its extension to general circuits, POVMs, heterogeneous gate fidelities, and multi-target search.
5. **S5–S6 — Complexity, Resource Estimation & Verification Payoff:** State the concrete optimal-stopping / complexity-crossover laws, utility-scale resource thresholds, and zero-axiom Lean 4 machine verification in the Supplemental Material. *(No raw URLs in APS abstracts.)*

### Introduction Funnel (4–5 Paragraphs, 450–650 Words)
1. **Paragraph 1 — Quantitative Hardware Noise & QEC Structural Assumptions:** Anchor gate error rates quantitatively (`0.01% to 1%`, `$10^{-4}$` fault-tolerant targets), credit QEC theory and recent experimental milestones in compact citation brackets, and pivot (`However, ...`) to noise symmetries that violate standard local-syndrome assumptions.
2. **Paragraph 2 — Geometric Nature of Isotropic Errors & Prior Numerical Puzzle:** Define pure-state isotropic errors geometrically on $`S^{2^{n+1}-1}`$, recall the QEC no-go theorem (Lacalle *et al.*, 2021), and summarize `arXiv:2606.04817`—highlighting both its $`n \le 13`$ classical simulation bottleneck and its empirical zero-free-parameter mixture law.
3. **Paragraph 3 — Four-Pillar Synthesis & Scope of Present Work:** Frame how resolving this puzzle connects (i) quantum-information ensemble/channel duality, (ii) coordinate-free spherical harmonic analysis, (iii) noisy query and gate complexity, and (iv) utility-scale heterogeneous resource estimation.
4. **Paragraph 4 — Contribution-Driven Roadmap:** Narrate the scientific flow and primary results (`Our main theoretical result is established in Sec. III, where we...` / `We first formulate... We then derive...`) rather than dry `"The rest of this paper is organized as follows"` boilerplate, and note the companion machine-checked Lean 4 proof in the Supplemental Material.

---

## 3. Sentence Cadence, Paragraph Architecture & Voice

- **Sentence Length Target:** Mean **22–25 words** (IQR **16–30 words**).
  - Open paragraphs with crisp **10–16 word declarative topic sentences** or **purpose clauses** (`To quantify the practical cost of..., we...`).
  - Follow long 28–38 word derivation or mechanism sentences with a short **8–14 word verdict or anchor sentence** to reset rhythm.
- **Section Lead-Ins:** Every `\section{...}` must open with a **1-paragraph (35–90 word) conceptual signpost** before its first `\subsection{...}` begins—zero naked section-to-subsection jumps.
- **Voice Balance:**
  - **Impersonal active (~50%):** Mathematical objects, symmetries, channels, and bounds act as grammatical subjects (*"Orthogonal reflection across the hyperplane reverses the sign..."*, *"Equation (14) shows that..."*).
  - **First-person plural `we` (~25–30%):** Used for derivations, modeling assumptions, and signposting—predominantly tucked after an introductory phrase (*"For arbitrary register size $`n`$, we obtain..."*) so consecutive sentences do not begin with `"We ..."`. Rarely use possessive `"our"` ($`\le 6`$ times in main text).
  - **Passive (~20–25%):** Reserved for standard conventions (*"Without loss of generality,..."*) and physical state degradation (*"coherent amplification is suppressed"*).
  - **Zero second-person pronouns (`you` / `your`)** and zero contractions (`don't`, `it's`, `we'll`).

---

## 4. Mathematical Exposition: The 3-Beat Equation Sandwich

1. **Beat 1 — Grammatical Lead-In (Zero Orphan Equations):**
   - Integrate every display equation as part of a grammatical English sentence, with **no blank lines** immediately before `\begin{equation}` or after `\end{equation}` when the sentence continues.
   - Use **no colon** when preceded by a linking verb, preposition, or noun apposition (`...is given by`, `...evaluates to`, `...defines the channel`). Use a **colon (`:`)** only after a syntactically complete independent clause (`...weighted by the cumulative fidelity factor:`).
2. **Beat 2 — Punctuated Display Math + Immediate Symbol Gloss:**
   - Use `\begin{equation}`, `\begin{equation*}`, `\begin{align}`, or `\begin{align*}` exclusively (never `$$...$$` or `\[...\]`).
   - **Every** display equation ends with `,` or `.` matching the host sentence.
   - Define 1–3 new symbols immediately via flush-left `where $X$ is ..., and $Y$ denotes ...` (eliding repeated copulas cleanly). For 4+ symbols, end the equation with `.` and open a new sentence `Here $X$ is ..., $Y$ is ..., and $Z$ is ...`.
   - Explicitly explain physical prefactors and exponents (*"The factor $`2`$ in $`\sigma^{2G}`$ reflects the quadratic dependence of Born probabilities on statevector amplitudes."*).
3. **Beat 3 — Limiting-Case Sanity Check & Hardware Translation:**
   - Immediately inspect the physical boundary cases ($`\sigma \to 1`$ coherent limit vs. $`\sigma \to 0`$ uniform/random-guessing limit) in plain prose using `i.e.,`.
   - Ground dimensionless fidelity parameters in experimental gate infidelities (*"For context, $`\sigma = 0.9995`$ corresponds to a single-gate infidelity of approximately $`5 \times 10^{-4}`$."*).

---

## 5. Figures, Tables, Walkthroughs & Discussion

- **Prose Figure Walkthroughs:** Never write bare pointers (`"Results are shown in Fig. 2."`). Walk **axis/setup $`\to`$ monotonic regime progression (low noise $`\to`$ moderate noise $`\to`$ high noise) $`\to`$ secondary structural features (such as peak shifts or crossovers) and their physical mechanism**.
- **3-Move Caption Blueprint (25–80 Words):**
  1. **Verbless noun-phrase title:** *`Noisy Grover success probability versus iteration count across register sizes and per-gate fidelities.`*
  2. **Explicit visual key:** Map every panel `(a)`, `(b)`, curve style (`solid`, `dashed`), marker, and parameter value.
  3. **Self-contained takeaway:** State the key quantitative regime boundary or analytical overlay behavior.
- **Candid Discussion & Limitations:**
  - Include an explicit, unhedged limitations paragraph opening with: *"Some limitations of this study warrant mention. First, ... Second, ... Third, ..."*—distinguishing global $`S^{2^{n+1}-1}`$ pure-state isotropy from spatially local tensor-product hardware channels, state-preparation-and-measurement (SPAM) noise, and expectation values versus single-shot trajectory variance.
  - Close with a **single-paragraph Conclusion** (4–6 sentences, 110–170 words) focused on synthesis and concrete algorithmic/experimental directions, without repeating the Abstract verbatim.

---

## 6. APS *Physical Review A* House Conventions

- **Spelling:** 100% American English (`analyze`, `modeling`, `modeled`, `behavior`, `characterizes`, `parameterizes`, `color`, `center`, `Acknowledgments`, `toward`).
- **Punctuation:** Universal serial (Oxford) comma (`A, B, and C`); zero spaced dashes (avoid em-dashes or use tight APS `word---word` at most sparingly); en-dashes (`--`) for symmetric couplings and co-named concepts (`single--two-qubit`, `Lacalle--Pozo Coronado`).
- **Cross-References & Citations:** `Sec.~\ref{sec:...}`, `Fig.~\ref{fig:...}(a)` (`Figure~\ref{...}` at sentence start), `Table~\ref{tab:...}`, `Eq.~\eqref{eq:...}` (`Equation~\eqref{...}` at sentence start), and non-syntactic bracketed citations (`Ref.~\cite{...}` when used as a grammatical noun).
