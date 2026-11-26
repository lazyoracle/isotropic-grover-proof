# Codebase Hygiene & End-to-End Natural Language Proof Rewrite Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Polish `IsotropicGroverProof/` for simplicity and maintainability, and rewrite `english-proof.md` and `README.md` to provide a clear, accurate, and extensible end-to-end exposition matching the zero-axiom Lean formalization.

**Architecture:** Task 1 cleans barrel imports, stale comments, and remaining minor proof duplications across `IsotropicGroverProof/` while verifying all declarations under `lake build --wfail` and `#print axioms`. Task 2 rewrites `english-proof.md` and `README.md` and cross-checks every Lean declaration name and theorem statement cited in prose against the compiled codebase.

**Tech Stack:** Lean 4 (`v4.35.0`), Markdown / KaTeX math (`english-proof.md`, `README.md`).

**Spec:** `notes/issue-32-design.md`

## Global Constraints

- **Worktree isolation:** Work strictly inside `/home/anurag/isotropic-grover-proof/.claude/worktrees/issue-32`. Never modify `/home/anurag/isotropic-grover-proof` directly.
- **Lean binary path:** Always include `$HOME/.elan/bin` on `PATH` when invoking `lean` or `lake`.
- **Zero non-standard axioms, zero `sorry`s, zero warnings:** `lake build --wfail` must exit 0 with every declaration depending solely on `[propext, Classical.choice, Quot.sound]`.
- **100% prose-to-code fidelity:** Every Lean file path, definition name, and theorem name cited in `english-proof.md` and `README.md` must exist with the exact spelling and mathematical hypotheses proved in `IsotropicGroverProof/`. Never overstate what is proved (e.g. keep downstream $k(n)$ repetition fitting clearly labeled as downstream application).
- **Documentation directory:** Never create a top-level `docs/` directory (breaks `docgen-action@v1`).

## Review Focus

- Broken or misspelled Lean theorem citations in `english-proof.md` / `README.md`: verify every backticked Lean identifier in `english-proof.md` and `README.md` resolves in `IsotropicGroverProof` (or upstream `QuantumInfo` / `QuantumComputation`).
- Stale references to deleted files or removed axioms/stubs: ensure zero mentions of `GegenbaurerHelper.lean`, `isotropicComposition`, or `poissonIntegral_cos_sq_d3` being an unproved axiom remain in `README.md`, `english-proof.md`, or `IsotropicGroverProof/*.lean`.
- Parameter domain accuracy in prose: clearly distinguish legacy `Set.Ioo 0 1` / `0 < G` theorems (`isotropicGrover_main`) from the generalized `Set.Icc 0 1` / all-`G : ℕ` theorems (`noisyTrajectory_succProb`, `noisyCircuit_bornProb`, `noisyGrover_*`).
- Barrel completeness: ensure `IsotropicGroverProof.lean` → `IsotropicGroverProof/Basic.lean` transitively imports all 11 files in `IsotropicGroverProof/` so CI `axiom-audit` inspects 100% of the repository.
- Mathematical clarity and extensibility of `english-proof.md`: ensure every derivation step (including the 1D FTC antiderivatives $\tilde{F}_0, \tilde{G}_0, \tilde{G}_1, \tilde{H}_3$, the even/odd complex density-matrix cancellation, and the §9 extensibility recipes) is self-contained and algebraically verified.

---

### Task 1: Whole-Codebase Hygiene, Comment Cleanup, and Deduplication Audit Across `IsotropicGroverProof/`

**Files:**
- Modify: `IsotropicGroverProof.lean`
- Modify: `IsotropicGroverProof/*.lean` (header comment updates, `two_le_d` reuse, unused import/helper cleanup, `#guard_msgs in #print axioms` completeness)

**Interfaces:**
- Consumes: All modules in `IsotropicGroverProof/`
- Produces: Clean, zero-warning, zero-stale-comment `IsotropicGroverProof` library with verified barrel coverage and `#print axioms` guards on all headline theorems.

- [ ] **Step 1: Audit `IsotropicGroverProof/` for stale comments, duplicate `2 ≤ d n` snippets, and barrel coverage**

Run a scan across `IsotropicGroverProof.lean` and `IsotropicGroverProof/*.lean` for stale `"All sorrys"`, `"SORRY BUDGET"`, inline `have hd2 : 2 ≤ d n := by ...` blocks replaceable by `two_le_d n`, and duplicate imports in `IsotropicGroverProof.lean`.

- [ ] **Step 2: Apply cleanups and add `#guard_msgs in #print axioms` on any unguarded headline theorems**

1. Simplify `IsotropicGroverProof.lean` to `import IsotropicGroverProof.Basic` (with a concise module docstring) and verify `Basic.lean` imports every file in `IsotropicGroverProof/`.
2. Update outdated file-header comments in `MainTheorem.lean`, `Defs.lean`, `IsotropicError.lean`, `Composition.lean`, `CrossTerm.lean`, `SecondMoment.lean`, `Gegenbauer.lean`, `Sequential.lean`, `LimitingCases.lean`, and `GroverCircuit.lean` to accurately reflect the current verified architecture.
3. Reuse `two_le_d n` where `2 ≤ d n` was still proved inline (`CrossTerm.lean`, `MainTheorem.lean`, `Sequential.lean`) and remove any unused imports, keeping all public theorem names and signatures unchanged.
4. Ensure `#guard_msgs in #print axioms` guards cover headline theorems across `MainTheorem.lean`, `Sequential.lean`, `LimitingCases.lean`, `QuantumChannel.lean`, and `GroverCircuit.lean`.

- [ ] **Step 3: Verify full build and barrel import completeness**

Run:
```bash
PATH="$HOME/.elan/bin:$PATH" lake build --wfail
```
Expected: Exit code 0, 0 errors, 0 warnings, and all 11 submodules in `IsotropicGroverProof/` imported by `IsotropicGroverProof/Basic.lean`.

- [ ] **Step 4: Commit**

```bash
git add notes/issue-32-design.md notes/issue-32-plan.md IsotropicGroverProof.lean IsotropicGroverProof/
git commit -m "chore: clean up barrel imports, stale comments, and shared dimension helpers"
```

### Task 2: Rewrite `english-proof.md` and `README.md` with End-to-End Exposition and Verified Lean Cross-References

**Files:**
- Modify: `english-proof.md`
- Modify: `README.md`

**Interfaces:**
- Consumes: Finalized `IsotropicGroverProof/` declarations and module layout from Task 1.
- Produces: Complete, clear, extensible `english-proof.md` (§1–§9 + formalization map + references) and updated `README.md` with 100% verified declaration cross-references.

- [ ] **Step 1: Rewrite `english-proof.md` (§1–§9) per `notes/issue-32-design.md`**

Write the complete end-to-end mathematical exposition in `english-proof.md` covering:
- Executive summary, exact scope/assumptions, and a **Lean Formalization Map** table linking each section to its Lean file and key theorem names.
- §1 Complex-to-real Hilbert space & Born-rule/`POVM` bridge (`Ket`, `MState`, `computationalPOVM`, `ketToReal`, `unitaryToRealIso`).
- §2 Single-gate isotropic error model across $\sigma \in [0, 1]$ (`poissonAngleMeasure`, `perpSphereMeasure`, `isotropicError`).
- §3 Exact Poisson moments $\mathrm{E}[\cos\theta] = \sigma$ and $\mathrm{E}[\cos^2\theta] = \frac{(d-1)\sigma^2+1}{d}$ — presenting both the geometric harmonic-extension derivation and the self-contained 1D FTC + two-step induction proof (`antiderivF0`, `antiderivG0`, `antiderivG1`, `antiderivH3`, `poissonAngleMeasure_cos_sq`).
- §4 Equatorial sphere symmetry and the full bilinear second-moment operator (`perpSphere_inner_mul_inner`, `isotropicError_bilinear_secondMoment`).
- §5 Exact emergence of the complex depolarizing `CPTPMap` $\Lambda_\sigma(\rho) = \sigma^2\rho + (1-\sigma^2)\frac{I_N}{N}$ (`depolarizingChannel`, `isotropicOneStep_eq_depolarizingChannel`), showing the explicit real/imaginary index calculation.
- §6 Multi-gate noisy circuits: pure-state Markov chain (`noisyTrajectory_bilinear`, `noisyTrajectory_fidelity_eq_sequentialFidelity`, `noisyTrajectory_succProb`), `CPTPMap` unitary commutation & semigroup composition (`depolarizingChannel_comm_ofUnitary`, `depolarizingChannel_compose`), and syntactic `Circuit.size` collapse (`noisyCircuitChannel_eq`, `noisyCircuit_bornProb`).
- §7 Grover's algorithm specialization (`Grover.oracleUnitary`, `Grover.diffuserUnitary`, `Grover.p_succ`, `noisyGrover_iterGates_succProb`, `noisyGrover_fullGates_succProb`, `noisyGrover_circuit_bornProb`) + worked 1-qubit and 14-gate 2-qubit (`grover2QubitCircuit`) examples.
- §8 Limiting regimes, continuity on $[0, 1]$, monotonicity, and downstream repetition overhead $k(n)$.
- §9 Extensibility guide (arbitrary `Circuit n` algorithms, general observables/`POVM`s & multi-target Grover, and gate-specific fidelities $\prod_g \sigma_g^{2 \cdot c.\mathrm{count}(g)}$ via `Circuit.count`) + complete References (including Grover 1996, Lacalle & Pozo Coronado 2019, Axler–Bourdon–Ramey 2001, Muirhead 1982, Mardia & Jupp 2000, Meiburg et al. 2025 `QuantumInfo`/`Physlib`, and Shirobokov et al. 2026 `formal-quantum-computation`).

- [ ] **Step 2: Update `README.md` to match the completed formalization**

Update `README.md` with:
- Accurate overview across $\sigma \in [0, 1]$ and $G, n \in \mathbb{N}$ (both general $G$ and syntactic `c.size`),
- Summary of the proved theorem layers (Geometric engine, Multi-gate Markov trajectory, `QuantumInfo` `CPTPMap` & `Circuit.size` bridge, End-to-end Grover + concrete 1- and 2-qubit circuits, Limiting cases),
- Dependencies (`Lean v4.35.0`, `Mathlib v4.35.0`, `Physlib v4.35.0` `QuantumInfo`, `google-deepmind/formal-quantum-computation`),
- Zero-custom-axiom & CI `axiom-audit` section,
- Updated `IsotropicGroverProof/` 11-file repository map (including `QuantumChannel.lean`) and build instructions (`lake exe cache get && lake build --wfail`).

- [ ] **Step 3: Machine-verify every cited Lean theorem/definition name and run `lake build --wfail`**

Write and run a one-off Lean `#check` verification via `PATH="$HOME/.elan/bin:$PATH" lake env lean --stdin` confirming every `IsotropicGrover.*` declaration cited in `english-proof.md` and `README.md` resolves cleanly, confirm zero stale references (`GegenbaurerHelper`, `isotropicComposition`), and run `PATH="$HOME/.elan/bin:$PATH" lake build --wfail`.

- [ ] **Step 4: Commit**

```bash
git add english-proof.md README.md
git commit -m "docs: rewrite english-proof.md and README.md for zero-axiom QuantumInfo + QuantumComputation proof"
```
