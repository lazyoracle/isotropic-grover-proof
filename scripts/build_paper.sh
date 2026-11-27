#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

echo "[1/4] Checking deterministic figure and table data..."
python3 -B paper/scripts/generate_data.py --check

echo "[2/4] Running style-linter and data-generator unit tests..."
python3 -B -m unittest scripts/test_check_manuscript_style.py paper/scripts/test_generate_data.py

echo "[3/4] Linting LaTeX manuscript sources..."
REQUIRED_TEX=(
  "paper/main.tex"
  "paper/preamble.tex"
  "paper/metadata.tex"
  "paper/body.tex"
  "paper/figures/fig1_sphere_duality.tex"
  "paper/figures/fig2_grover_oscillations.tex"
  "paper/figures/fig3_complexity_crossover.tex"
  "paper/figures/fig4_resource_estimation.tex"
)

for req in "${REQUIRED_TEX[@]}"; do
  if [[ ! -f "$req" ]]; then
    echo "ERROR: Required manuscript file missing: $req" >&2
    exit 1
  fi
done

LINT_ARGS=("--lean-dir" "IsotropicGroverProof")

# Check main manuscript tree together so cross-references and float citations resolve cleanly
MAIN_GROUP=(
  "paper/preamble.tex"
  "paper/metadata.tex"
  "paper/body.tex"
  "paper/main.tex"
  "paper/figures/fig1_sphere_duality.tex"
  "paper/figures/fig2_grover_oscillations.tex"
  "paper/figures/fig3_complexity_crossover.tex"
  "paper/figures/fig4_resource_estimation.tex"
  "paper/data/table1_rows.tex"
)
python3 -B scripts/check_manuscript_style.py "${LINT_ARGS[@]}" "${MAIN_GROUP[@]}"

# If Supplemental Material / unified arXiv sources are present, lint them as well
if [[ -f "paper/supplement_body.tex" ]]; then
  SUPP_GROUP=("paper/preamble.tex" "paper/metadata.tex" "paper/supplement_body.tex")
  [[ -f "paper/supplement.tex" ]] && SUPP_GROUP+=("paper/supplement.tex")
  [[ -f "paper/figures/figS1_lean_architecture.tex" ]] && SUPP_GROUP+=("paper/figures/figS1_lean_architecture.tex")
  python3 -B scripts/check_manuscript_style.py "${LINT_ARGS[@]}" "${SUPP_GROUP[@]}"
fi

if [[ -f "paper/arxiv.tex" ]]; then
  ARXIV_GROUP=("${MAIN_GROUP[@]}" "paper/arxiv.tex")
  [[ -f "paper/supplement_body.tex" ]] && ARXIV_GROUP+=("paper/supplement_body.tex")
  [[ -f "paper/figures/figS1_lean_architecture.tex" ]] && ARXIV_GROUP+=("paper/figures/figS1_lean_architecture.tex")
  python3 -B scripts/check_manuscript_style.py "${LINT_ARGS[@]}" "${ARXIV_GROUP[@]}"
fi

echo "[4/4] Compiling LaTeX targets with latexmk and auditing build logs..."
mkdir -p paper/build
TARGETS=("main.tex")
[[ -f "paper/supplement.tex" ]] && TARGETS+=("supplement.tex")
[[ -f "paper/arxiv.tex" ]] && TARGETS+=("arxiv.tex")

for target in "${TARGETS[@]}"; do
  (
    cd paper
    latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build "$target"
  )
done

python3 -B - "${TARGETS[@]}" <<'PY'
import re
import sys
from pathlib import Path

targets = sys.argv[1:]
build_dir = Path("paper/build")
errors: list[str] = []

undef_ref_re = re.compile(r"LaTeX Warning: Reference `[^']*' on page .* undefined")
undef_cit_re = re.compile(r"LaTeX Warning: Citation `[^']*' on page .* undefined")
there_undef_re = re.compile(r"LaTeX Warning: There were undefined (?:references|citations)")
mult_label_re = re.compile(r"LaTeX Warning: Label `[^']*' multiply defined")
dup_dest_re = re.compile(r"destination with the same identifier")
overfull_re = re.compile(r"Overfull \\hbox \(([0-9]+(?:\.[0-9]+)?)pt too wide\)")

for target in targets:
    stem = Path(target).stem
    log_path = build_dir / f"{stem}.log"
    pdf_path = build_dir / f"{stem}.pdf"
    if not pdf_path.is_file():
        errors.append(f"{pdf_path}: expected PDF output missing")
    if not log_path.is_file():
        errors.append(f"{log_path}: expected log file missing")
        continue

    raw_log = log_path.read_text(encoding="latin-1")
    # Join hard-wrapped 79-column TeX log lines for reliable pattern matching where needed
    lines = raw_log.splitlines()
    for idx, line in enumerate(lines, start=1):
        window = line + (" " + lines[idx] if idx < len(lines) else "")
        if undef_ref_re.search(window):
            errors.append(f"{log_path}:{idx}: {line.strip()}")
        if undef_cit_re.search(window):
            errors.append(f"{log_path}:{idx}: {line.strip()}")
        if there_undef_re.search(line):
            errors.append(f"{log_path}:{idx}: {line.strip()}")
        if mult_label_re.search(window):
            errors.append(f"{log_path}:{idx}: {line.strip()}")
        if dup_dest_re.search(window):
            errors.append(f"{log_path}:{idx}: duplicate hyperref destination: {line.strip()}")
        m_over = overfull_re.search(line)
        if m_over:
            pt = float(m_over.group(1))
            if pt > 4.0:
                errors.append(f"{log_path}:{idx}: Overfull \\hbox ({pt:.2f}pt > 4.0pt): {line.strip()}")

if errors:
    for err in errors:
        print(f"LOG AUDIT FAIL: {err}", file=sys.stderr)
    sys.exit(1)

print(f"OK: {len(targets)} PDF target(s) compiled cleanly with 0 log-audit errors")
PY
