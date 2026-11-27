# Issue #41 Design Specification: *Physical Review A* Manuscript & Lean 4 Extensions

## 1. Objective & Scope

Produce a publication-ready *Physical Review A* (`revtex4-2`) manuscript (`paper/`) and accompanying Supplemental Material presenting:
1. **Main Text:** A self-contained English mathematical proof of exact expected measurement probabilities for noisy quantum circuits and Grover's search algorithm under isotropic pure-state gate errors, grounded in a four-pillar motivation (**theoretical quantum information**, **applied mathematics**, **quantum complexity theory**, and **quantum resource estimation**), resolving the empirical mixture law and all four open problems of `arXiv:2606.04817` (Saha Roy & Lacalle, 2026), and written strictly in the author voice codified in `notes/author-style-guide.md`.
2. **Lean 4 Formalization Extensions (`IsotropicGroverProof/`):** Zero-custom-axiom extensions (~120–150 lines) formalizing **heterogeneous per-gate fidelity schedules** (connecting directly to `Circuit.count` over `PrimitiveGate`) and **multi-target ($`M`$-marked-item) Grover search**, ensuring 1-to-1 machine-checked coverage of every closed-form theorem in the Main Text.
3. **Supplemental Material:** Complete account of the Lean 4 (`v4.35.0`) formalization architecture across `Mathlib`, `Physlib` (`QuantumInfo`), and `formal-quantum-computation`, `#print axioms` verification, design choices, and a complete Mathematical-Result $`\leftrightarrow`$ Lean-Declaration correspondence table.

---

## 2. Metadata & Dual APS / arXiv Build Architecture

### 2.1 Title, Authors & Affiliations (`paper/metadata.tex`)
- **Title:** *Exact measurement statistics and complexity of quantum circuits and Grover's algorithm under isotropic gate errors*
- **Authors & Affiliations:**
  1. **Anurag Saha Roy** (`\email{anurag@qruise.com}`)
     - `\affiliation{Qruise GmbH, Am H\"olzersbach 7, Saarbr\"ucken, 66113, Germany}`
     - `\affiliation{ETS de Ingenier\'ia de Sistemas Inform\'aticos, Universidad Polit\'ecnica de Madrid, C/ Alan Turing s/n, Madrid, 28031, Spain}`
  2. **Jes\'us Lacalle** (`\email{jesus.glopezdelacalle@upm.es}`)
     - `\affiliation{ETS de Ingenier\'ia de Sistemas Inform\'aticos, Universidad Polit\'ecnica de Madrid, C/ Alan Turing s/n, Madrid, 28031, Spain}`
- **Funding Acknowledgements:** Omitted per author instruction (no `\begin{acknowledgments}` grant block).

### 2.2 Zero-Duplication Modular File Layout (`paper/`)
- `paper/preamble.tex`: Shared `revtex4-2`-compatible packages (`amsmath`, `amssymb`, `amsthm`, `mathtools`, `bm`, `braket`, `booktabs`, `tikz`, `pgfplots` with `\pgfplotsset{compat=1.18}`, `hyperref`), theorem environments (`theorem`, `lemma`, `proposition`, `corollary`, `remark`), paired delimiters (`\norm`, `\abs`, `\ip`), and `\newif\ifarXivunified` conditional macro `\suppRef` (emitting `\cite{SupplementalMaterial}` in standalone APS mode vs. internal `\hyperref[sec:supp-overview]{Supplemental Material}` in unified arXiv mode).
- `paper/metadata.tex`: Shared `\author`, `\email`, and `\affiliation` declarations.
- `paper/body.tex`: Main Text Sections I–VI, inputting vector figures from `paper/figures/*.tex` and data tables from `paper/data/*.dat`.
- `paper/supplement_body.tex`: Supplemental Material Sections S1–S5, inputting `paper/figures/figS1_lean_architecture.tex`.
- `paper/references.bib`: Shared BibTeX bibliography (including `@misc{SupplementalMaterial, note = {See Supplemental Material at [URL will be inserted by publisher] for the zero-axiom Lean 4 formalization architecture, module hierarchy, theorem correspondence table, and verification instructions.}}` used only in `main.tex`).
- `paper/scripts/generate_data.py`: Deterministic Python 3 script (using standard library `math` and `csv`/`pathlib` only—zero third-party Python dependencies) generating `paper/data/*.dat` for `pgfplots` figures and printing exact benchmark values for Table I.
- **Three `revtex4-2` Entry Points (outputting to gitignored `paper/build/`):**
  1. `paper/main.tex` (`\documentclass[aps,pra,twocolumn,superscriptaddress,10pt]{revtex4-2}`, `\arXivunifiedfalse`): Compiles `body.tex` + `\bibliography{references}` $`\to`$ `paper/build/main.pdf`.
  2. `paper/supplement.tex` (`\documentclass[aps,pra,onecolumn,superscriptaddress,10pt]{revtex4-2}`, `\arXivunifiedfalse`): Sets `S`-prefixed section/equation/figure/table counters (`S1`, `(S1)`, `Fig. S1`, `Table S1`) and compiles `supplement_body.tex` + `\bibliography{references}` $`\to`$ `paper/build/supplement.pdf`.
  3. `paper/arxiv.tex` (`\documentclass[aps,pra,twocolumn,superscriptaddress,10pt]{revtex4-2}`, `\arXivunifiedtrue`): Compiles `body.tex`, switches via `\clearpage\onecolumngrid` with reset `S`-prefixed counters to `supplement_body.tex`, and emits a single unified `\bibliography{references}` $`\to`$ `paper/build/arxiv.pdf`.

---

## 3. Zero-Axiom Lean 4 Extensions (`IsotropicGroverProof/`)

All new definitions and theorems must compile cleanly with `lake build --wfail` and depend strictly on `[propext, Classical.choice, Quot.sound]`.

### 3.1 Heterogeneous Per-Gate Trajectories (`IsotropicGroverProof/Sequential.lean`)
- Define `noisyTrajectoryExpectationHet (n : ℕ) : List (E n ≃ₗᵢ[ℝ] E n × ℝ) → E n → (E n → ℝ) → ℝ`, applying isometric gate $`U_k`$ followed by an isotropic sphere perturbation with gate-specific parameter $`\sigma_k \in [0, 1]`$.
- Prove `noisyTrajectoryHet_bilinear`: for any list `steps : List (E n ≃ₗᵢ[ℝ] E n × ℝ)` with `∀ p ∈ steps, p.2 ∈ Set.Icc 0 1`, unit initial state `‖Φ₀‖ = 1`, and vectors `u v : E n`:

```math
\operatorname{noisyTrajectoryExpectationHet}(n, \mathit{steps}, \Phi_0, \Psi \mapsto \langle \Psi, u\rangle\langle \Psi, v\rangle) = \Bigl(\prod_{(U,\sigma) \in \mathit{steps}} \sigma^2\Bigr)\langle \Phi_{\mathrm{ideal}}, u\rangle\langle \Phi_{\mathrm{ideal}}, v\rangle + \frac{1 - \prod_{(U,\sigma) \in \mathit{steps}} \sigma^2}{d(n)}\langle u, v\rangle,
```

along with `noisyTrajectoryHet_succProb` and agreement with `noisyTrajectoryExpectation` when all $`\sigma_k = \sigma`$.

### 3.2 Syntactic `Circuit.count` Heterogeneous Channel Theorems (`IsotropicGroverProof/QuantumChannel.lean`)
- Define `circuitFidelity (σGate : ∀ {k}, PrimitiveGate k → ℝ) : Circuit n → ℝ` (product of `σGate g` across `.gate g r`, `1` on `.identity`, multiplicative on `.seq`) and `noisyCircuitChannelHet` applying `depolarizingChannel n (σGate g) _` after each primitive gate `.gate g r`.
- Prove:
  1. `noisyCircuitChannelHet_eq`: `noisyCircuitChannelHet σGate hσ c = depolarizingChannel n (circuitFidelity σGate c) _ ∘ₘ CPTPMap.ofUnitary c.eval`.
  2. `noisyCircuitHet_trajectory_eq_channel`: exact equivalence between the microscopic pure-state trajectory `noisyTrajectoryExpectationℂHet` along `c` and `noisyCircuitChannelHet`.
  3. `circuitFidelity_eq_prod_count`: for any `c : Circuit n`, `circuitFidelity σGate c` equals the explicit product over the 9 primitive gates weighted by `c.count g`, plus the arity-tiered specialization `circuitFidelity_arity` ($`\sigma_{1\mathrm{q}}^{G_{1\mathrm{q}}} \sigma_{2\mathrm{q}}^{G_{2\mathrm{q}}} \sigma_{3\mathrm{q}}^{G_{3\mathrm{q}}}`$ where $`G_{1\mathrm{q}} + G_{2\mathrm{q}} + G_{3\mathrm{q}} = c.\mathrm{size}`$):

```math
\sigma_{\mathrm{eff}}(c) = \Bigl(\prod_{g_1 \in \{X,Y,Z,H,S,T\}} \sigma(g_1)^{\mathrm{count}(g_1, c)}\Bigr) \sigma(\mathrm{CNOT})^{\mathrm{count}(\mathrm{CNOT}, c)} \sigma(\mathrm{SWAP})^{\mathrm{count}(\mathrm{SWAP}, c)} \sigma(\mathrm{TOFF})^{\mathrm{count}(\mathrm{TOFF}, c)}.
```

### 3.3 Multi-Target ($`M`$-Marked-Item) Grover Search (`IsotropicGroverProof/GroverCircuit.lean`)
- Define subset measurement probability `subsetSuccProb (n : ℕ) (Ψ : E n) (S : Finset (Fin (2 ^ n))) : ℝ := ∑ w ∈ S, succProb n Ψ w` (and its `computationalPOVM` sum equivalence).
- Prove `noisyTrajectoryHet_subsetSuccProb` and `noisyCircuitHet_subsetBornProb`: for any target set $`S \subseteq \mathrm{Fin}(2^n)`$ of cardinality $`M = S.\mathrm{card}`$:

```math
\mathbb{E}\bigl[\operatorname{subsetSuccProb}_n(\Psi_{\mathrm{noisy}}, S)\bigr] = \sigma_{\mathrm{eff}}^2 \operatorname{subsetSuccProb}_n(\Phi_{\mathrm{ideal}}, S) + (1 - \sigma_{\mathrm{eff}}^2)\frac{M}{2^n}.
```

- Formalize the multi-target phase oracle unitary `multiOracleUnitary (S : Finset (Fin (2 ^ n))) : 𝐔[Fin (2 ^ n)]` ($`O_S = I - 2\sum_{w \in S}\lvert w\rangle\langle w\rvert`$), the multi-target Grover step $`G_S = D \cdot O_S`$, its exact 2D plane invariant state after $`K`$ iterations (`sin((2K+1)θ_{n,M}) |S⟩ + cos((2K+1)θ_{n,M}) |S^⊥⟩` with $`\theta_{n,M} = \arcsin\sqrt{M / 2^n}`$ for $`0 < M < 2^n`$), and the end-to-end noisy multi-target Grover theorem `noisyMultiGroverHet_succProb`:

```math
\mathbb{E}\bigl[\operatorname{subsetSuccProb}_n(\Psi_{\mathrm{noisy}}, S)\bigr] = \sigma_{\mathrm{eff}}^2 \sin^2\!\bigl((2K+1)\arcsin\sqrt{M / 2^n}\bigr) + (1 - \sigma_{\mathrm{eff}}^2)\frac{M}{2^n}.
```

---

## 4. Main-Text Section-by-Section Content & Figures (`paper/body.tex`)

### Section I — Introduction
- Quantitative gate-infidelity framing (`0.01%`–`1%` physical error rates, `$10^{-4}$` fault-tolerant targets) and recent QEC experimental milestones vs. symmetry assumptions.
- Geometric formulation of pure-state isotropic errors on $`S^{2^{n+1}-1}`$, the QEC syndrome no-go result (Lacalle *et al.*, 2021), and the numerical discoveries & four open problems of `arXiv:2606.04817`.
- Synthesis of the four motivating pillars (QI channel duality, spherical harmonic analysis, noisy query/gate complexity, utility-scale resource estimation) and contribution-driven roadmap referencing the machine-checked Lean 4 Supplemental Material via `\suppRef`.

### Section II — Isotropic Pure-State Error Model on $`\mathbb{C}^N \cong \mathbb{R}^{2N}`$
- Real Euclidean embedding $`\iota : \mathbb{C}^N \to \mathbb{R}^{2N}`$ ($`N = 2^n`$, $`d = 2N`$), real-linear isometry lifting of unitary gates $`U \in \mathrm{U}(N)`$ into $`\mathrm{O}(2N)`$, and Born-rule / POVM projection identities.
- Tangent-normal decomposition $`\Psi' = (\cos\theta)\Psi + (\sin\theta)\mathbf{e}_2`$ with $`\mathbf{e}_2 \sim \mu_\perp(\Psi)`$ uniform on $`S^{d-2}`$ and angle $`\theta \in [0, \pi]`$ distributed according to the spherical Poisson kernel on $`\sigma \in [0, 1]`$ (including boundary Dirac/uniform limits at $`\sigma = 1`$ and $`\sigma = 0`$).
- Heterogeneous sequential pure-state Markov trajectory across arbitrary gate lists $`((U_1, \sigma_1), \dots, (U_G, \sigma_G))`$.
- **Figure 1 (`paper/figures/fig1_sphere_duality.tex`, `tikz`):** Schematic of the tangent-sphere perturbation on $`S^{2N-1}`$, orthogonal reflection across $`\operatorname{span}\{\mathbf{v}\}^\perp`$, and the $`(2N - 1)`$ cancellation mapping pure-state trajectories to $`\Lambda_\sigma(\rho)`$.

### Section III — Exact Spherical Moments and Microscopic-to-Channel Duality
- **Theorem 1 (Spherical Poisson Moments for All $`d \ge 2`$):** Self-contained 1D Fundamental Theorem of Calculus + two-step parity induction proof that $`I_d(\sigma) = 1`$, $`\mathbb{E}[\cos\theta] = \sigma`$, and $`\mathbb{E}[\cos^2\theta] = \frac{(d-1)\sigma^2 + 1}{d}`$ for all $`d \ge 2`$ and $`\sigma \in [0, 1]`$—highlighting why elementary 1D integration bypasses multivariable spherical-harmonic PDEs.
- **Theorem 2 (Equatorial Reflection Symmetry & Bilinear Cancellation):** Coordinate-free reflection proof that $`\mathbb{E}[\langle \mathbf{e}_2, \mathbf{u}\rangle] = 0`$ and $`\mathbb{E}[\langle \mathbf{e}_2, \mathbf{u}\rangle\langle \mathbf{e}_2, \mathbf{v}\rangle] = \frac{\langle P_\perp \mathbf{u}, P_\perp \mathbf{v}\rangle}{d - 1}`$, followed by exact single-step cancellation of $`d - 1 = 2N - 1`$:

$$
\mathbb{E}\bigl[\langle \Psi', \mathbf{u}\rangle\langle \Psi', \mathbf{v}\rangle\bigr] = \sigma^2\langle \Psi, \mathbf{u}\rangle\langle \Psi, \mathbf{v}\rangle + \frac{1 - \sigma^2}{2N}\langle \mathbf{u}, \mathbf{v}\rangle.
$$

- **Theorem 3 (Emergence of the Depolarizing Channel & Heterogeneous Composition):** Entrywise averaging of $`\lvert\psi'\rangle\langle\psi'\rvert`$ yields $`\Lambda_\sigma(\rho) = \sigma^2\rho + (1 - \sigma^2)\frac{I_N}{N}`$ (with the $`2`$ in $`2N`$ canceling against real+imaginary basis components, while off-diagonal imaginary cross terms cancel identically). By backward Markov induction, any $`G`$-gate heterogeneous circuit satisfies $`\mathbb{E}[\operatorname{Tr}(E_m \lvert\psi_{\mathrm{noisy}}\rangle\langle\psi_{\mathrm{noisy}}\rvert)] = \sigma_{\mathrm{eff}}^2 \operatorname{Tr}(E_m \rho_{\mathrm{ideal}}) + \frac{1 - \sigma_{\mathrm{eff}}^2}{N}\operatorname{Tr}(E_m)`$ with $`\sigma_{\mathrm{eff}} = \prod_{g=1}^G \sigma_g`$, without invoking spherical convolution.
- **Quantum-Information Duality Discussion:** Operational equivalence for all single-copy linear observables/POVMs vs. distinction on nonlinear/multi-copy functionals (such as shot-to-shot trajectory variance $`\mathrm{Var}(\lvert\langle w \vert \psi_{\mathrm{noisy}}\rangle\rvert^2) > 0`$ at $`\sigma = 0`$, where $`\Lambda_0(\rho) = I_N/N`$ is deterministic while pure-state Haar/uniform draws fluctuate with Porter–Thomas / Beta statistics!) and why global $`S^{2N-1}`$ isotropy mixes QEC code and syndrome subspaces unlike local tensor-product depolarizing channels $`\mathcal{D}_p^{\otimes n}`$.

### Section IV — Exact Noisy Grover Search ($`M \ge 1`$ Targets) and Optimal Stopping
- **Corollary 1 (Exact Multi-Target Noisy Grover Formula):** Specialization to $`M`$ marked items ($`0 < M < N`$, $`\theta = \arcsin\sqrt{M/N}`$), recovering Eq. (19) of `arXiv:2606.04817` at $`M = 1`$ and uniform $`\sigma`$ as an exact theorem rather than a phenomenological fit.
- **Proposition 1 (Exact Noise-Shifted Optimal Iteration Count):** Writing $`\sigma_{\mathrm{eff}}(K) = \sigma_{\mathrm{init}}\gamma^K`$ with per-iteration fidelity $`\gamma \in (0, 1]`$ and dimensionless noise-to-rotation ratio $`\kappa = \frac{-\ln\gamma}{2\theta}`$ ($`\phi = \arctan\kappa`$), the continuous first-lobe maximum of $`p_e(K) = \sin^2\theta + \sigma_{\mathrm{init}}^2 \gamma^{2K}(\sin^2((2K+1)\theta) - \sin^2\theta)`$ occurs at the exact angle:

$$
(2K^* + 1)\theta = \frac{\pi - \phi - \arcsin\bigl(\sin\phi \cos(2\theta)\bigr)}{2},
$$

satisfying $`K^*(\gamma, n, M) \le K_{\mathrm{ideal}}`$, approaching $`(2K^* + 1)\theta \to \operatorname{arccot}\kappa`$ for $`M \ll N`$, and saturating at an $`N`$-independent ceiling $`K^* \approx \frac{1}{-\ln\gamma} - \frac{1}{2}`$ in the overdamped regime $`\kappa \gg 1`$. Clarifies the subtle operational distinction between maximizing single-shot $`p_e(K)`$ (where $`K = 1`$ strictly beats $`K = 0`$ for $`M/N < 3/4`$ and $`\gamma > 0`$ because the uniform state $`|s\rangle`$ already lies at the depolarizing fixed point $`M/N`$) and minimizing expected oracle queries $`Q(K) = K \cdot k(n, K)`$.
- **Figure 2 (`paper/figures/fig2_grover_oscillations.tex`, `pgfplots`):** Exact $`p_e(n, K)`$ vs. $`K`$ across $`n \in \{6, 10, 14, 20\}`$ and $`\sigma \in \{0.99, 0.999, 0.9999, 1.0\}`$, overlaid with the analytical peak locus $`(K^*, p_e(K^*))`$.

### Section V — Complexity Phase Transition and Utility-Scale Resource Estimation
- **Exact Repetition Overhead & Analytical $`b(\sigma)`$ Law:** Exact analysis of $`k(n, K) = \frac{\ln(1 - p_{\mathrm{ideal}}(n, K))}{\ln(1 - p_e(n, K))}`$, explaining both the discrete parity/overshoot oscillations and the per-qubit exponential growth factor $`b(\sigma)`$ observed numerically in Figs. 4–5 of `arXiv:2606.04817`.
- **Asymptotic Crossover $`N_{\mathrm{cross}}`$ & Fidelity Scaling Law:** Proves that for any fixed per-gate fidelity $`\sigma_g < 1`$, total expected oracle queries $`Q_{\mathrm{eff}}(n) = K \cdot k(n, K)`$ crosses over from $`\frac{\pi}{4}\sqrt{N/M}`$ (slope $`1/2`$) to classical $`\Omega(N/M)`$ scaling (slope $`1`$) past $`\kappa \sim 1`$ (even under optimal early stopping $`K^*`$, whereas naive $`K_{\mathrm{ideal}}`$ incurs an even steeper penalty when $`p_{\mathrm{ideal}} \approx 1`$), and establishes that preserving Grover's $`O(\sqrt{N/M})`$ speedup requires $`1 - \sigma_g = O(1 / G(n)) = O\bigl(1 / (n\sqrt{N/M})\bigr)`$.
- **Utility-Scale Heterogeneous 1q/2q Resource Budgets ($`n = 10\text{--}60`$):** Applies `circuitFidelity_eq_prod_count` ($`\sigma_{\mathrm{eff}} = \sigma_{1\mathrm{q}}^{G_{1\mathrm{q}}} \sigma_{2\mathrm{q}}^{G_{2\mathrm{q}}}`$) using explicit linear-$`n`$ multi-controlled Toffoli decompositions into `CNOT` + single-qubit Clifford+$`T`$ gates ($`g_{2\mathrm{q}}(n) = 12n - 18`$, $`g_{1\mathrm{q}}(n) = 16n - 20`$ per Grover iteration for clean ancilla-assisted / standard Barenco–Toffoli benchmarks, stated explicitly with exact counts) under realistic QPU infidelity asymmetry $`1 - \sigma_{1\mathrm{q}} = \alpha(1 - \sigma_{2\mathrm{q}})`$ ($`\alpha \in \{0.1, 0.01\}`$).
- **Figure 3 (`paper/figures/fig3_complexity_crossover.tex`, two-panel `pgfplots`):** (a) Log–log total expected queries $`Q_{\mathrm{eff}}(n)`$ vs. $`N = 2^n`$ for $`n = 4\text{--}50`$ comparing optimal $`K^*`$ against naive $`K_{\mathrm{ideal}}`$ and classical $`N/M`$; (b) analytical per-qubit overhead factor $`b(\sigma)`$ for $`M \in \{1, 4, 16\}`$.
- **Figure 4 (`paper/figures/fig4_resource_estimation.tex`, `pgfplots`) & Table I (`tab:resource-budgets`):** Required entangling-gate infidelity $`1 - \sigma_{2\mathrm{q}}`$ and single-qubit infidelity $`1 - \sigma_{1\mathrm{q}}`$ across $`n \in \{10, 20, 30, 40, 50, 60\}`$ for overhead budgets $`k(n) \le 2`$ and $`k(n) \le 10`$ under $`\alpha = 0.1`$ and $`\alpha = 0.01`$.

### Section VI — Discussion and Conclusion
- Synthesis of how geometric sphere cancellation unifies pure-state isotropic noise with channel-level resource estimation while explaining `arXiv:2606.04817`.
- Candid enumerated limitations (`"Some limitations of this study warrant mention. First, ... Second, ... Third, ..."`): (1) global $`S^{2^{n+1}-1}`$ pure-state isotropy vs. spatially local hardware noise ($`\mathcal{D}_p^{\otimes n}`$) and correlated crosstalk; (2) expectation-value exactness vs. shot-to-shot pure-state distribution variance (`Beta(1, N-1)` / Porter–Thomas fluctuations); (3) ideal SPAM assumption at preparation and readout.
- Single-paragraph Conclusion outlining extensions to amplitude estimation, variational/Trotterized circuits, non-isotropic noise mixtures, and experimental benchmarking.

---

## 5. Supplemental Material (`paper/supplement_body.tex`)

1. **Sec. S1 — Scope & Trust Boundary of the Machine-Checked Proof:** Lean `v4.35.0` kernel verification, `#print axioms` audit confirming dependence strictly on `[propext, Classical.choice, Quot.sound]`, zero `sorry`s, and continuous CI enforcement.
2. **Sec. S2 — Three-Layer Formalization Architecture (`paper/figures/figS1_lean_architecture.tex`):** Visual dependency DAG and narrative linking Layer 1 (`Mathlib` `Measure.haar`, `Metric.sphere`, `intervalIntegral`), Layer 2 (`Physlib` `QuantumInfo`: `Ket`, `MState`, `CPTPMap`, `POVM`), and Layer 3 (`formal-quantum-computation`: `Circuit`, `PrimitiveGate`, `Circuit.count`, `Circuit.size`, `Grover`).
3. **Sec. S3 — Key Formalization Engineering Choices:** (a) Replacing multivariable Laplace–Beltrami PDEs with the 1D FTC + parity induction; (b) coordinate-free ambient orthogonal reflections on $`V_\perp(\Psi)`$; (c) radial-bump extension and local Householder charts proving parameter continuity of spherical integrals across $`\Psi \in S^{d-1}`$; (d) syntactic induction on `Circuit n` for `Circuit.size` and `Circuit.count`.
4. **Sec. S4 — Mathematical-to-Lean Correspondence Table (Table S1):** Exhaustive mapping from every Main-Text definition, lemma, theorem, and corollary (including `noisyTrajectoryHet_bilinear`, `circuitFidelity_eq_prod_count`, and `noisyMultiGroverHet_succProb`) to its exact Lean module and identifier, plus the concrete 1-qubit (`Circuit.H 0`) and 14-gate 2-qubit (`grover2QubitCircuit`) witnesses.
5. **Sec. S5 — Reproducible Verification Guide:** Exact `lake build --wfail`, axiom-audit, and manuscript build commands.

---

## 6. Automated Verification & CI Gates

1. **`scripts/check_manuscript_style.py` + `scripts/test_check_manuscript_style.py`:**
   - Rejects any occurrence of banned hype/LLM words in `paper/*.tex` prose/captions.
   - Rejects British spelling variants in `paper/*.tex` prose/captions (ignoring BibTeX keys, `\affiliation` proper nouns, and LaTeX control sequences).
   - Rejects `$$...$$`, `\[...\]`, blank lines adjacent to `\begin{equation}` / `\begin{align}`, and display equations lacking terminal punctuation (`,` or `.` before `\end{equation}` / `\end{align}`).
   - Verifies every `\label{fig:...}` and `\label{tab:...}` is referenced via `\ref`, every `\ref` / `\eqref` resolves to a defined `\label`, and every `IsotropicGrover.*` or Lean declaration cited in `\texttt{...}` in `supplement_body.tex` exists in `IsotropicGroverProof/*.lean`.
2. **`scripts/build_paper.sh`:**
   - Runs `python3 paper/scripts/generate_data.py --check` (verifying `paper/data/*.dat` is up to date and reproducible).
   - Runs `python3 -B -m unittest scripts/test_check_manuscript_style.py` and `python3 -B scripts/check_manuscript_style.py`.
   - Compiles `main.tex`, `supplement.tex`, and `arxiv.tex` into `paper/build/` using `latexmk -pdf -interaction=nonstopmode -halt-on-error`, and parses `.log` files to fail on any `LaTeX Warning: Reference ... undefined`, `Citation ... undefined`, or `Overfull \hbox` exceeding `4pt`.
3. **CI Integration (`.github/workflows/lean_action_ci.yml`):**
   - Adds a dedicated fast `paper` job on `ubuntu-24.04` (running in parallel with the Lean `build` job in ~1–2 minutes) that installs TeX Live packages (`texlive-latex-recommended`, `texlive-latex-extra`, `texlive-publishers`, `texlive-pictures`, `texlive-science`, `latexmk`), runs `scripts/build_paper.sh`, and uploads `main.pdf`, `supplement.pdf`, and `arxiv.pdf` as downloadable workflow artifacts, while the Lean `build` job continues to verify `lake build --wfail`, `axiom-audit`, `check_markdown_math.py`, and `build_docs.sh`.
