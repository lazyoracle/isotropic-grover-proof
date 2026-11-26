# *Physical Review A* Manuscript & Lean Extensions Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend the zero-axiom Lean 4 proof to heterogeneous gate fidelities (`Circuit.count`) and multi-target ($`M`$-item) Grover search, and author a complete *Physical Review A* (`revtex4-2`) manuscript + Supplemental Material (`main.pdf`, `supplement.pdf`, `arxiv.pdf`) in Anurag Saha Roy's codified style with automated style/LaTeX/CI verification.

**Architecture:** Task 1 adds ~140 lines of zero-custom-axiom Lean 4 theorems for heterogeneous gate schedules and $`M`$-marked-item Grover search so every closed-form theorem in the Main Text has a 1-to-1 machine-checked counterpart. Task 2 builds the TDD style/LaTeX linter (`scripts/check_manuscript_style.py`) and deterministic stdlib-Python figure/table data generator (`paper/scripts/generate_data.py` using `math.log1p` for $`n \le 60`$ precision). Tasks 3 and 4 author the modular `revtex4-2` Main Text (`paper/body.tex`, native `tikz`/`pgfplots` figures, `paper/references.bib`), Supplemental Material (`paper/supplement_body.tex`), dual APS/arXiv entry points (`main.tex`, `supplement.tex`, `arxiv.tex`), `scripts/build_paper.sh`, and parallel CI job.

**Tech Stack:** Lean 4 (`v4.35.0`, `Mathlib`, `Physlib`/`QuantumInfo`, `formal-quantum-computation`), TeX Live (`revtex4-2`, `tikz`, `pgfplots`, `latexmk`, `bibtex`), Python 3.12 (`unittest`, `math`).

**Spec:** `notes/issue-41-design.md` and `notes/author-style-guide.md`

## Global Constraints

- **Worktree isolation:** All work happens strictly inside `/home/anurag/isotropic-grover-proof/.claude/worktrees/issue-41`. Never modify `/home/anurag/isotropic-grover-proof` directly.
- **Zero custom axioms & zero `sorry`s:** Every Lean declaration in `IsotropicGroverProof/` must build cleanly under `PATH="$HOME/.elan/bin:$PATH" lake build --wfail` and depend strictly on `[propext, Classical.choice, Quot.sound]`.
- **Author style compliance (`notes/author-style-guide.md`):** 100% APS American English, universal Oxford commas, zero banned hype/LLM words (`novel`, `delve`, `pivotal`, `underscore`, `groundbreaking`, `unprecedented`, `paradigm`, `tapestry`, `testament`, `moreover`, `notably`, `importantly`, `interestingly`, `remarkably`, `strikingly`, `in conclusion`, etc.), 1-paragraph lead-ins after every `\section`, 3-beat punctuated equation sandwiches (zero `$$`/`\[\]`, zero blank lines adjacent to display math), and 3-move verbless-headline captions.
- **Zero external Python dependencies:** Both `scripts/check_manuscript_style.py` and `paper/scripts/generate_data.py` must use Python 3 standard library modules only.
- **No top-level `docs/` directory:** Store manuscript sources in `paper/`, automation scripts in `scripts/` and `paper/scripts/`, and design/plan notes in `notes/`.

## Review Focus

- **IEEE-754 float64 underflow at $`n = 50\text{--}60`$ qubits (`N = 2^60`):** Naive `math.log(1.0 - p_e)` evaluates `1.0 - 2**-60 == 1.0` and divides by zero when computing $`k(n) = \frac{\ln(1 - p_{\mathrm{ideal}})}{\ln(1 - p_e)}`$; `paper/scripts/generate_data.py` must use `math.log1p(-x)` (and asymptotic log-ratio fallback if $`p = 1`$ at $`n = 2, M = 1`$), pinned by `n = 60` tests in Task 2.
- **LaTeX comments, labels after punctuation, and Lean `\_` escapes in `check_manuscript_style.py`:** Comments (`%`, preserving `\%`) must be stripped before scanning prose/math; `\label{...}` / `\notag` / `\nonumber` may appear either before or after the equation's terminal `,` or `.`; `\affiliation`, `\email`, `\cite`, `\bibitem`, and `\url` must be excluded from spelling checks; and `\texttt{foo\_bar}` in `supplement_body.tex` must unescape `\_` to `_` when verifying declarations against `IsotropicGroverProof/*.lean` (pinned in Task 2).
- **Duplicate `hyperref` destinations (`ext4` warnings) in unified `arxiv.pdf`:** Resetting section/equation/figure/table counters before `supplement_body.tex` in `arxiv.tex` collides with Main-Text anchors unless `\theHsection`, `\theHequation`, `\theHfigure`, and `\theHtable` are also prefixed with `S`; `scripts/build_paper.sh` must fail on `destination with the same identifier` in `.log` files (pinned in Task 4).
- **Degenerate subset cardinalities in multi-target Lean theorems (`S = ∅` or `S = Finset.univ`):** General subset measurement theorems (`subsetSuccProb`, `noisyTrajectoryHet_subsetSuccProb`, `noisyCircuitHet_subsetBornProb`) must hold for arbitrary `S : Finset (Fin (2 ^ n))` without cardinality restrictions, while the 2D Grover rotation theorem (`multiGroverIterState`, `noisyMultiGroverHet_succProb`) explicitly requires `0 < S.card` and `S.card < 2 ^ n` so neither normalized basis vector divides by zero (pinned in Task 1).
- **GFM math hygiene on edited `.md` files:** Any updates to `README.md` or `english-proof.md` must continue passing `python3 -B scripts/check_markdown_math.py` with 0 errors (pinned in Tasks 1 and 4).

---

### Task 1: Zero-Axiom Lean 4 Extensions for Heterogeneous Gate Fidelities & Multi-Target Grover Search

**Files:**
- Modify: `IsotropicGroverProof/Sequential.lean`
- Modify: `IsotropicGroverProof/QuantumChannel.lean`
- Modify: `IsotropicGroverProof/GroverCircuit.lean`
- Modify: `english-proof.md`
- Modify: `README.md`

**Interfaces:**
- Consumes: Existing `noisyTrajectoryExpectation`, `depolarizingChannel`, `depolarizingChannel_compose`, `Circuit.count` (`QuantumComputation.Circuits.ResourceCounting`), `PrimitiveGate`, and `Grover.diffuserUnitary`.
- Produces (exact Lean names in namespace `IsotropicGrover`, cited in `paper/supplement_body.tex` in Task 4):
  - In `IsotropicGroverProof/Sequential.lean`:
    - `idealGateTrajectoryHet {n : ℕ} (steps : List (E n ≃ₗᵢ[ℝ] E n × ℝ)) (Φ₀ : E n) : E n`
    - `fidelityProd {α : Type*} (steps : List (α × ℝ)) : ℝ` (`(steps.map Prod.snd).prod`)
    - `noisyTrajectoryExpectationHet (n : ℕ) : List (E n ≃ₗᵢ[ℝ] E n × ℝ) → E n → (E n → ℝ) → ℝ`
    - `noisyTrajectoryHet_eq_uniform` (agrees with `noisyTrajectoryExpectation n σ gates` when `steps = gates.map (·, σ)`)
    - `noisyTrajectoryHet_bilinear` (exact bilinear expectation with `(fidelityProd steps) ^ 2` for `∀ p ∈ steps, p.2 ∈ Set.Icc 0 1`)
    - `noisyTrajectoryHet_succProb`
  - In `IsotropicGroverProof/QuantumChannel.lean`:
    - `noisyTrajectoryExpectationℂHet (n : ℕ) : List (E n ≃ₗᵢ[ℝ] E n × ℝ) → E n → (E n → ℂ) → ℂ`
    - `circuitFidelity {n : ℕ} (σGate : ∀ {k}, PrimitiveGate k → ℝ) : Circuit n → ℝ`
    - `noisyCircuitChannelHet {n : ℕ} (σGate : ∀ {k}, PrimitiveGate k → ℝ) (hσ : ∀ {k} (g : PrimitiveGate k), σGate g ∈ Set.Icc 0 1) : Circuit n → CPTPMap (Fin (2 ^ n)) (Fin (2 ^ n))`
    - `noisyCircuitChannelHet_eq` (`= depolarizingChannel n (circuitFidelity σGate c) _ ∘ₘ CPTPMap.ofUnitary c.eval`)
    - `circuitStepsHet {n : ℕ} (σGate : ∀ {k}, PrimitiveGate k → ℝ) : Circuit n → List (𝐔[Fin (2 ^ n)] × ℝ)`
    - `noisyCircuitHet_trajectory_eq_channel` (entrywise equality between `noisyTrajectoryExpectationℂHet` of `pureDensityMatrix` and `noisyCircuitChannelHet`)
    - `circuitFidelity_eq_prod_count` (explicit factorization of `circuitFidelity σGate c` into `σGate (.x) ^ c.count .x * ... * σGate (.toffoli) ^ c.count .toffoli`)
    - `gateCount1Q`, `gateCount2Q`, `gateCount3Q : Circuit n → ℕ` and `circuitFidelity_arity` (`σ₁ ^ gateCount1Q c * σ₂ ^ gateCount2Q c * σ₃ ^ gateCount3Q c` when `σGate` depends only on gate arity, plus `gateCount_sum_eq_size : gateCount1Q c + gateCount2Q c + gateCount3Q c = c.size`)
  - In `IsotropicGroverProof/GroverCircuit.lean`:
    - `subsetSuccProb (n : ℕ) (Ψ : E n) (S : Finset (Fin (2 ^ n))) : ℝ` (`∑ w ∈ S, succProb n Ψ w`)
    - `noisyTrajectoryHet_subsetSuccProb` (holds for *all* `S : Finset (Fin (2 ^ n))`, including `∅` and `Finset.univ`)
    - `noisyCircuitHet_subsetBornProb` (`∑ w ∈ S, ((computationalPOVM n).measure (noisyCircuitChannelHet σGate hσ c ρ) w : ℝ) = (circuitFidelity σGate c) ^ 2 * (∑ w ∈ S, ((computationalPOVM n).measure (CPTPMap.ofUnitary c.eval ρ) w : ℝ)) + (1 - (circuitFidelity σGate c) ^ 2) * (S.card : ℝ) / (2 ^ n : ℝ)`)
    - `multiOracleMatrix {n : ℕ} (S : Finset (Fin (2 ^ n))) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ` (`1 - (2 : ℂ) • ∑ w ∈ S, Matrix.single w w 1`), `multiOracleUnitary {n : ℕ} (S : Finset (Fin (2 ^ n))) : 𝐔[Fin (2 ^ n)]`, and `multiGroverStep {n : ℕ} (S : Finset (Fin (2 ^ n))) : 𝐔[Fin (2 ^ n)]` (`Grover.diffuserUnitary * multiOracleUnitary S`)
    - `multiTargetState`, `multiNonTargetState` (`E n` / `Ket (Fin (2 ^ n))`), `multiGroverHalfAngle (n M : ℕ) : ℝ` (`Real.arcsin (Real.sqrt ((M : ℝ) / (2 ^ n : ℝ)))`), `multiGroverPSucc (K n M : ℕ) : ℝ` (`Real.sin ((2 * (K : ℝ) + 1) * multiGroverHalfAngle n M) ^ 2`)
    - `multiGrover_ideal_subsetSuccProb` (for `0 < S.card` and `S.card < 2 ^ n`, after `hadamardUnitary` + `K` applications of `multiGroverStep S` on `Ket.basis 0`, `subsetSuccProb` equals `multiGroverPSucc K n S.card`)
    - `noisyMultiGroverHet_succProb` (end-to-end heterogeneous noisy $`M`$-target Grover expectation formula across any decomposition `(steps : List (𝐔[Fin (2 ^ n)] × ℝ))` whose unitary product equals `(multiGroverStep S) ^ K * hadamardUnitary`).

- [ ] **Step 1: Write a Lean check script verifying the target signatures fail before implementation (RED)**

Run:
```bash
PATH="$HOME/.elan/bin:$PATH" lake env lean --stdin <<'EOF'
import IsotropicGroverProof
#check @IsotropicGrover.noisyTrajectoryHet_bilinear
#check @IsotropicGrover.circuitFidelity_eq_prod_count
#check @IsotropicGrover.noisyMultiGroverHet_succProb
EOF
```
Expected: FAIL (`unknown constant`).

- [ ] **Step 2: Implement heterogeneous trajectories in `IsotropicGroverProof/Sequential.lean`**

Generalize the backward induction and bounded-sphere linearity lemmas from `noisyTrajectoryExpectation` (or refactor `noisyTrajectoryExpectation` cleanly in terms of `noisyTrajectoryExpectationHet` if shorter, keeping every existing public theorem name and signature intact!) to prove `noisyTrajectoryHet_bilinear`, `noisyTrajectoryHet_succProb`, and `noisyTrajectoryHet_eq_uniform`.

- [ ] **Step 3: Implement heterogeneous `CPTPMap` circuits & `Circuit.count` factorization in `IsotropicGroverProof/QuantumChannel.lean`**

Define `circuitFidelity`, `noisyCircuitChannelHet`, `noisyTrajectoryExpectationℂHet`, `gateCount1Q`, `gateCount2Q`, `gateCount3Q`, and prove `noisyCircuitChannelHet_eq`, `noisyCircuitHet_trajectory_eq_channel`, `circuitFidelity_eq_prod_count` (by structural induction on `c : Circuit n`, case-splitting `g : PrimitiveGate k` over the 9 constructors in the `.gate` case), `circuitFidelity_arity`, and `gateCount_sum_eq_size`.

- [ ] **Step 4: Implement `subsetSuccProb` & multi-target Grover search in `IsotropicGroverProof/GroverCircuit.lean`, and sync `README.md` / `english-proof.md`**

Prove `noisyTrajectoryHet_subsetSuccProb` and `noisyCircuitHet_subsetBornProb` for arbitrary `S : Finset (Fin (2 ^ n))` (including `S = ∅` and `S = Finset.univ`), then formalize `multiOracleUnitary`, `multiGroverStep`, the 2D plane rotation `multiGrover_ideal_subsetSuccProb` for `0 < S.card` and `S.card < 2 ^ n`, and `noisyMultiGroverHet_succProb`. Add concise cross-references in §8 of `english-proof.md` and `README.md`.

- [ ] **Step 5: Verify build, zero custom axioms, and Markdown math lint (GREEN)**

Run:
```bash
PATH="$HOME/.elan/bin:$PATH" lake build --wfail
PATH="$HOME/.elan/bin:$PATH" lake env lean --stdin <<'EOF'
import IsotropicGroverProof
#print axioms IsotropicGrover.noisyTrajectoryHet_bilinear
#print axioms IsotropicGrover.noisyCircuitChannelHet_eq
#print axioms IsotropicGrover.noisyCircuitHet_trajectory_eq_channel
#print axioms IsotropicGrover.circuitFidelity_eq_prod_count
#print axioms IsotropicGrover.circuitFidelity_arity
#print axioms IsotropicGrover.noisyTrajectoryHet_subsetSuccProb
#print axioms IsotropicGrover.noisyCircuitHet_subsetBornProb
#print axioms IsotropicGrover.noisyMultiGroverHet_succProb
EOF
python3 -B scripts/check_markdown_math.py english-proof.md README.md
```
Expected: `lake build --wfail` exits 0 with 0 warnings; every `#print axioms` outputs strictly `[propext, Classical.choice, Quot.sound]`; `check_markdown_math.py` outputs `0 errors`.

- [ ] **Step 6: Commit**

```bash
git add IsotropicGroverProof/Sequential.lean IsotropicGroverProof/QuantumChannel.lean IsotropicGroverProof/GroverCircuit.lean english-proof.md README.md
git commit -m "feat(lean): formalize heterogeneous gate fidelities and multi-target Grover search"
```

---

### Task 2: Manuscript Style/LaTeX Linter & Deterministic Figure/Table Data Generator

**Files:**
- Create: `scripts/check_manuscript_style.py`
- Create: `scripts/test_check_manuscript_style.py`
- Create: `paper/scripts/generate_data.py`
- Create: `paper/scripts/test_generate_data.py`
- Create: `paper/data/fig2_oscillations.dat`
- Create: `paper/data/fig2_peaks.dat`
- Create: `paper/data/fig3a_queries.dat`
- Create: `paper/data/fig3b_growth_rate.dat`
- Create: `paper/data/fig4_resource_budgets.dat`
- Create: `paper/data/table1_rows.tex`
- Modify: `.gitignore`

**Interfaces:**
- Consumes: Codified rules in `notes/author-style-guide.md` and mathematical formulas in `notes/issue-41-design.md`, plus `IsotropicGroverProof/*.lean` declaration names.
- Produces:
  - `python3 -B scripts/check_manuscript_style.py [--lean-dir IsotropicGroverProof] paper/*.tex paper/figures/*.tex` (exits 0 on clean TeX, non-zero with `file:line: message` diagnostics on violations).
  - `python3 -B paper/scripts/generate_data.py [--check]` (writes deterministic whitespace/tab-separated `.dat` files with header comments in `paper/data/` and `paper/data/table1_rows.tex`, or exits non-zero under `--check` if any file on disk differs).
  - Exact `.dat` column schemas consumed by `pgfplots` in Task 3:
    - `paper/data/fig2_oscillations.dat`: columns `K  p_n6_s1  p_n6_s9999  p_n6_s999  p_n6_s99  p_n10_s1  p_n10_s9999  p_n10_s999  p_n10_s99  p_n14_s1  p_n14_s9999  p_n14_s999  p_n14_s99  p_n20_s1  p_n20_s9999  p_n20_s999  p_n20_s99` (or normalized `k_over_kideal` / per-panel files `fig2_n6.dat`, `fig2_n10.dat`, `fig2_n14.dat`, `fig2_n20.dat` + `fig2_peaks.dat` with `n  sigma  K_star  p_star` — document exact filenames/columns in `generate_data.py` docstring and Task 2 report!).
    - `paper/data/fig3a_queries.dat`: columns `n  log2N  Q_ideal  Q_classical  Q_opt_s9999  Q_naive_s9999  Q_opt_s999  Q_naive_s999  Q_opt_s99999  Q_naive_s99999` for $`n \in [4, 50]`$, $`M = 1`$.
    - `paper/data/fig3b_growth_rate.dat`: columns `one_minus_sigma  sigma  b_M1  b_M4  b_M16` across $`1 - \sigma \in [10^{-6}, 2 \times 10^{-1}]`$.
    - `paper/data/fig4_resource_budgets.dat`: columns `n  infid2q_k2_a01  infid2q_k2_a001  infid2q_k10_a01  infid2q_k10_a001` for $`n \in [6, 60]`$ using linear-$`n`$ multi-controlled Toffoli gate counts ($`g_{2\mathrm{q}}(n) = 12n - 18`$, $`g_{1\mathrm{q}}(n) = 16n - 20`$ per Grover iteration, plus $`n`$ initialization Hadamards) and $`1 - \sigma_{1\mathrm{q}} = \alpha(1 - \sigma_{2\mathrm{q}})`$.
    - `paper/data/table1_rows.tex`: pre-formatted LaTeX table rows for $`n \in \{10, 20, 30, 40, 50, 60\}`$ inputted directly into `Table I` of `paper/body.tex`.

- [ ] **Step 1: Write failing unit tests `scripts/test_check_manuscript_style.py` and `paper/scripts/test_generate_data.py` (RED)**

Include unit tests pinning:
1. Banned hype/LLM words (`novel`, `delve`, `pivotal`, `underscore`, `groundbreaking`, `unprecedented`, `paradigm`, `tapestry`, `testament`, `leverage`, `seamlessly`, `elucidate`, `unravel`, `moreover`, `notably`, `importantly`, `interestingly`, `remarkably`, `strikingly`, `in conclusion`) caught case-insensitively in prose and captions, ignored in `%` comments and `\cite{...}` keys.
2. British spelling slips (`analyse`, `analysing`, `analysed`, `modelling`, `modelled`, `behaviour`, `characterises`, `parameterises`, `acknowledgements`, `towards`, `realisations`, `initialisation`, `fulfil`) and second-person pronouns (`you`, `your`) caught in prose, ignored in `\affiliation{...}`, `\email{...}`, `\bibitem`, and `\url{...}`.
3. Equation hygiene: rejects `$$...$$`, `\[...\]`, blank lines immediately above `\begin{equation}`/`\begin{align}` or inside them, and display equations missing terminal `,` or `.` (while accepting `\label{eq:foo}` or `\notag` placed either before or after the terminal `,` / `.`).
4. Cross-reference & Lean-declaration audit: rejects uncited `\label{fig:...}` / `\label{tab:...}`, undefined `\ref{...}` / `\eqref{...}`, naked `\section{...}` followed directly by `\subsection{...}` with zero lead-in prose, and `\texttt{IsotropicGrover.nonexistent\_thm}` (properly unescaping `\_` to `_`) when checked against `IsotropicGroverProof/`.
5. `test_generate_data.py`: verifies `optimal_iteration_continuous(gamma, n, M)` satisfies numerical first-derivative zero to `< 1e-10` and approaches `K_ideal` as `gamma -> 1`; verifies `repetition_overhead(n, M, K, sigma_eff)` using `math.log1p` produces finite, accurate positive values at **`n = 60`** without float64 `ZeroDivisionError`; and verifies `generate_data.py --check` detects stale files.

Run:
```bash
python3 -B -m unittest scripts/test_check_manuscript_style.py paper/scripts/test_generate_data.py
```
Expected: FAIL (`ModuleNotFoundError`).

- [ ] **Step 2: Implement `scripts/check_manuscript_style.py` and `paper/scripts/generate_data.py`, update `.gitignore`, and generate `paper/data/*` (GREEN)**

Add `/paper/build/` to `.gitignore`. Implement both scripts cleanly using Python 3 stdlib only, run `python3 -B paper/scripts/generate_data.py` to populate `paper/data/`, and verify `--check` mode.

- [ ] **Step 3: Run unit test suites and `--check` gate**

Run:
```bash
python3 -B -m unittest scripts/test_check_manuscript_style.py paper/scripts/test_generate_data.py
python3 -B paper/scripts/generate_data.py --check
```
Expected: All tests PASS (`exit 0`).

- [ ] **Step 4: Commit**

```bash
git add .gitignore scripts/check_manuscript_style.py scripts/test_check_manuscript_style.py paper/scripts/generate_data.py paper/scripts/test_generate_data.py paper/data/
git commit -m "feat(paper): add manuscript style linter and deterministic figure data generator"
```

---

### Task 3: Author *Physical Review A* Main Manuscript (`paper/body.tex`), Vector Figures & Bibliography

**Files:**
- Create: `paper/preamble.tex`
- Create: `paper/metadata.tex`
- Create: `paper/references.bib`
- Create: `paper/figures/fig1_sphere_duality.tex`
- Create: `paper/figures/fig2_grover_oscillations.tex`
- Create: `paper/figures/fig3_complexity_crossover.tex`
- Create: `paper/figures/fig4_resource_estimation.tex`
- Create: `paper/body.tex`
- Create: `paper/main.tex`
- Create: `scripts/build_paper.sh`

**Interfaces:**
- Consumes: `notes/author-style-guide.md`, `notes/issue-41-design.md`, `paper/data/*` (from Task 2), and `scripts/check_manuscript_style.py` (from Task 2).
- Produces: Complete `revtex4-2` Main Text compiling cleanly to `paper/build/main.pdf` via `scripts/build_paper.sh`, with `\ifarXivunified` hooks (`\suppRef`) ready for Task 4's `supplement.tex` and `arxiv.tex`.

- [ ] **Step 1: Create `scripts/build_paper.sh` failing before `paper/main.tex` exists (RED)**

Write `scripts/build_paper.sh` (executable `bash` with `set -euo pipefail`) that runs:
1. `python3 -B paper/scripts/generate_data.py --check`
2. `python3 -B -m unittest scripts/test_check_manuscript_style.py paper/scripts/test_generate_data.py`
3. `python3 -B scripts/check_manuscript_style.py ...`
4. `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex` inside `paper/` (and `supplement.tex` / `arxiv.tex` once present or required in Task 4), scanning `paper/build/*.log` to fail on any `Reference .* undefined`, `Citation .* undefined`, `destination with the same identifier`, or `Overfull \hbox` > `4pt`.

Run: `bash scripts/build_paper.sh`
Expected: FAIL (`paper/main.tex` missing).

- [ ] **Step 2: Create `paper/preamble.tex`, `paper/metadata.tex`, `paper/references.bib`, and `paper/figures/fig1`–`fig4`**

- Configure `paper/preamble.tex` cleanly for `revtex4-2` (`amsmath`, `amssymb`, `amsthm`, `mathtools`, `bm`, `braket`, `booktabs`, `tikz`, `pgfplots`, `hyperref` with `colorlinks=true,allcolors=blue`, colorblind-safe Okabe–Ito plot colors, and `\newif\ifarXivunified` + `\newcommand{\suppRef}{...}`).
- Configure `paper/metadata.tex` with Anurag Saha Roy (`anurag@qruise.com`, Qruise GmbH & UPM) and Jesús Lacalle (`jesus.glopezdelacalle@upm.es`, UPM), omitting funding acknowledgements.
- Populate `paper/references.bib` with verified DOIs/arXiv IDs (`SahaRoyLacalle2026` = `arXiv:2606.04817`, Fonseca de Oliveira *et al.* 2017, Lacalle & Pozo Coronado 2019, Lacalle *et al.* 2021, Lacalle *et al.* 2026, Grover 1996, Boyer *et al.* 1998, Zalka 1999, Shenvi *et al.* 2003, Shapira *et al.* 2003, Salas 2008, Cohn *et al.* 2016, Barenco *et al.* 1995, Nielsen & Chuang 2000, Fowler *et al.* 2012, Google Quantum AI 2025, Bluvstein *et al.* 2024, Lean 4 / Moura & Ullrich 2021, Mathlib 2020, `SupplementalMaterial`, etc.).
- Build publication-quality `tikz`/`pgfplots` figures `fig1_sphere_duality.tex` through `fig4_resource_estimation.tex` sized accurately for `revtex4-2` single-column (`\columnwidth`) or full-width (`\textwidth`, `figure*`) with crisp typography and zero overlapping labels.

- [ ] **Step 3: Author `paper/body.tex` and `paper/main.tex` following `notes/author-style-guide.md` and `notes/issue-41-design.md`**

Draft all six sections (`Sec. I` Introduction through `Sec. VI` Discussion and Conclusion, plus `Table I` inputting `paper/data/table1_rows.tex`), ensuring:
- Self-contained, crystal-clear English proofs of Theorems 1–3, Corollary 1, and Proposition 1 with zero Lean syntax in the Main Text;
- Explicit physical comparison between global $`S^{2^{n+1}-1}`$ pure-state isotropy, local per-qubit depolarizing channels $`\mathcal{D}_p^{\otimes n}`$, QEC syndrome projections, and shot-to-shot pure-state Porter–Thomas/Beta variance;
- Complete analytical resolution of `arXiv:2606.04817` (Eq. 19 exactness, $`K^*(\gamma, n, M)`$ peak shift, $`Q_{\mathrm{eff}}(n)`$ $`O(\sqrt{N/M}) \to \Omega(N/M)`$ crossover, $`b(\sigma)`$ multi-target curves, and $`n = 10\text{--}60`$ heterogeneous 1q/2q fidelity budgets);
- Strict adherence to every rule in `notes/author-style-guide.md`.

- [ ] **Step 4: Compile `main.pdf`, inspect rendered layout & logs, and run `scripts/build_paper.sh` (GREEN)**

Run:
```bash
bash scripts/build_paper.sh
pdfinfo paper/build/main.pdf
```
Also render pages of `paper/build/main.pdf` via `pdftoppm -png -r 150 paper/build/main.pdf /tmp/opencode/main_page` and visually inspect the rendered PNG pages using the `read` tool to verify figure aesthetics, caption spacing, table alignment, and equation layout!
Expected: `scripts/build_paper.sh` exits 0 with 0 style errors, 0 undefined refs/citations, and clean visual layout across all pages.

- [ ] **Step 5: Commit**

```bash
rm -rf /tmp/opencode/main_page*
git add paper/preamble.tex paper/metadata.tex paper/references.bib paper/figures/ paper/body.tex paper/main.tex scripts/build_paper.sh
git commit -m "feat(paper): add Physical Review A main manuscript, vector figures, and build script"
```

---

### Task 4: Author Supplemental Material (`supplement.pdf`), Unified arXiv Preprint (`arxiv.pdf`), & CI Integration

**Files:**
- Create: `paper/figures/figS1_lean_architecture.tex`
- Create: `paper/supplement_body.tex`
- Create: `paper/supplement.tex`
- Create: `paper/arxiv.tex`
- Modify: `scripts/build_paper.sh`
- Modify: `.github/workflows/lean_action_ci.yml`
- Modify: `README.md`

**Interfaces:**
- Consumes: Lean declarations from Task 1 (`IsotropicGroverProof/*.lean`), `paper/preamble.tex`, `paper/metadata.tex`, `paper/body.tex`, `paper/references.bib` from Task 3, and `scripts/check_manuscript_style.py` from Task 2.
- Produces:
  - `paper/build/main.pdf` (standalone APS *PRA* Main Text)
  - `paper/build/supplement.pdf` (standalone APS *PRA* Supplemental Material with `S`-prefixed counters)
  - `paper/build/arxiv.pdf` (unified arXiv preprint with Main Text + `\onecolumngrid` `S`-numbered Supplemental Material + unified bibliography and zero `hyperref` duplicate-destination warnings)
  - Parallel `paper` CI job in `.github/workflows/lean_action_ci.yml`.

- [ ] **Step 1: Extend `scripts/build_paper.sh` to require `supplement.pdf`, `arxiv.pdf`, and Lean-identifier cross-checking, confirming RED before files exist**

Update `scripts/build_paper.sh` to compile all three targets (`main.tex`, `supplement.tex`, `arxiv.tex`), check all three `.log` files (including rejecting `destination with the same identifier`), and run `check_manuscript_style.py --lean-dir IsotropicGroverProof` across all `.tex` files including `supplement_body.tex`.
Run: `bash scripts/build_paper.sh`
Expected: FAIL (`supplement.tex` / `arxiv.tex` not found).

- [ ] **Step 2: Author `paper/figures/figS1_lean_architecture.tex`, `paper/supplement_body.tex`, `paper/supplement.tex`, and `paper/arxiv.tex`**

- Build `figS1_lean_architecture.tex` (`tikz` 3-layer dependency diagram across `Mathlib`, `Physlib`/`QuantumInfo`, `formal-quantum-computation`, and the 9 `IsotropicGroverProof` modules).
- Draft `paper/supplement_body.tex` (`Secs. S1–S5`, including exhaustive `Table S1` mapping every mathematical object and theorem in the Main Text—including Task 1's heterogeneous `circuitFidelity_eq_prod_count` and multi-target `noisyMultiGroverHet_succProb`—to its verified Lean 4 identifier, plus the concrete 1-qubit and 14-gate 2-qubit circuit witnesses and verification commands) in strict compliance with `notes/author-style-guide.md`.
- Configure `S`-prefixed counters (`\renewcommand{\theequation}{S\arabic{equation}}`, `\renewcommand{\theHequation}{S\arabic{equation}}`, and analogously for `section`, `figure`, `table`) in both `supplement.tex` and the `\onecolumngrid` tail of `arxiv.tex` so `hyperref` anchors are 100% unique.

- [ ] **Step 3: Wire parallel `paper` job into `.github/workflows/lean_action_ci.yml` and update `README.md`**

- Add a `paper` job in `.github/workflows/lean_action_ci.yml` (`runs-on: ubuntu-24.04`) that checks out the repo, installs `texlive-latex-recommended texlive-latex-extra texlive-publishers texlive-pictures texlive-science latexmk`, runs `bash scripts/build_paper.sh`, and uploads `paper/build/main.pdf`, `paper/build/supplement.pdf`, and `paper/build/arxiv.pdf` via `actions/upload-artifact@v4` (ensuring `deploy` still depends only on `build` on `main`).
- Document the `paper/` directory and `bash scripts/build_paper.sh` in `README.md`.

- [ ] **Step 4: Full end-to-end verification & visual PDF inspection (GREEN)**

Run:
```bash
bash scripts/build_paper.sh
python3 -B -m unittest discover -s scripts -p 'test_*.py'
python3 -B scripts/check_markdown_math.py english-proof.md README.md notes/author-style-guide.md notes/issue-41-design.md notes/issue-41-plan.md
PATH="$HOME/.elan/bin:$PATH" lake build --wfail
```
Render pages of `paper/build/supplement.pdf` and the transition/table pages of `paper/build/arxiv.pdf` with `pdftoppm -png -r 150` into `/tmp/opencode/` and visually inspect via `read` to confirm clean typography, zero table/diagram clipping, working `S`-prefixed numbering, and clean `\suppRef` rendering in both `main.pdf` and `arxiv.pdf`. Remove temporary `/tmp/opencode/*.png` files afterward.
Expected: All commands exit 0 with zero warnings/errors.

- [ ] **Step 5: Commit**

```bash
git add paper/figures/figS1_lean_architecture.tex paper/supplement_body.tex paper/supplement.tex paper/arxiv.tex scripts/build_paper.sh .github/workflows/lean_action_ci.yml README.md
git commit -m "feat(paper): add Lean 4 supplemental material, unified arXiv build, and CI workflow"
```
