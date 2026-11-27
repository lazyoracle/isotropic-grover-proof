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
  "paper/supplement.tex"
  "paper/arxiv.tex"
  "paper/preamble.tex"
  "paper/metadata.tex"
  "paper/body.tex"
  "paper/supplement_body.tex"
  "paper/figures/fig1_sphere_duality.tex"
  "paper/figures/fig2_grover_oscillations.tex"
  "paper/figures/fig3_complexity_crossover.tex"
  "paper/figures/fig4_resource_estimation.tex"
  "paper/figures/figS1_lean_architecture.tex"
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

# Check standalone Supplemental Material tree
SUPP_GROUP=(
  "paper/preamble.tex"
  "paper/metadata.tex"
  "paper/supplement_body.tex"
  "paper/supplement.tex"
  "paper/figures/figS1_lean_architecture.tex"
)
python3 -B scripts/check_manuscript_style.py "${LINT_ARGS[@]}" "${SUPP_GROUP[@]}"

# Check unified arXiv manuscript tree
ARXIV_GROUP=(
  "${MAIN_GROUP[@]}"
  "paper/arxiv.tex"
  "paper/supplement_body.tex"
  "paper/figures/figS1_lean_architecture.tex"
)
python3 -B scripts/check_manuscript_style.py "${LINT_ARGS[@]}" "${ARXIV_GROUP[@]}"

python3 -B - <<'PY'
import re
import sys
from pathlib import Path

lean_files = sorted(Path("IsotropicGroverProof").rglob("*.lean")) + [
    Path("IsotropicGroverProof.lean")
]
missing = [str(p) for p in lean_files if not p.is_file()]
if missing:
    print(f"ERROR: Missing Lean source file(s): {', '.join(missing)}", file=sys.stderr)
    sys.exit(1)

actual_lines = sum(p.read_bytes().count(b"\n") for p in lean_files)
supp_path = Path("paper/supplement_body.tex")
raw = supp_path.read_text(encoding="utf-8")
uncommented = "\n".join(
    re.sub(r"(?<!\\)%.*$", "", line) for line in raw.splitlines()
)

pattern = re.compile(
    r"(?:\$([0-9][0-9,\{\}]*)\$|([0-9][0-9,]*))\s+lines\s+of\s+Lean"
)
matches = list(pattern.finditer(uncommented))
if not matches:
    print(
        f"ERROR: {supp_path}: expected Lean line-count statement ('... lines of Lean') not found",
        file=sys.stderr,
    )
    sys.exit(1)

for m in matches:
    token = m.group(1) or m.group(2)
    stated = int(re.sub(r"[^0-9]", "", token))
    if stated != actual_lines:
        formatted = f"{actual_lines:,}".replace(",", "{,}")
        print(
            f"ERROR: {supp_path}: stated Lean line count ({stated}) != actual wc -l total ({actual_lines}); "
            f"update to ${formatted}$",
            file=sys.stderr,
        )
        sys.exit(1)

print(f"OK: {supp_path} Lean line count ({actual_lines}) matches {len(lean_files)} Lean source files")
PY

echo "[4/4] Compiling LaTeX targets with latexmk and auditing build logs..."
mkdir -p paper/build
TARGETS=("main.tex" "supplement.tex" "arxiv.tex")

for target in "${TARGETS[@]}"; do
  (
    cd paper
    latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build "$target"
  )
done

python3 -B - "${TARGETS[@]}" <<'PY'
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

targets = sys.argv[1:]
build_dir = Path("paper/build")
errors: list[str] = []
pdffonts_bin = shutil.which("pdffonts")
if pdffonts_bin is None:
    if os.environ.get("CI") == "true" or os.environ.get("GITHUB_ACTIONS") == "true":
        errors.append("pdffonts binary not found in CI; install poppler-utils")
    else:
        print("WARNING: pdffonts not found; skipping Type 3 font audit", file=sys.stderr)

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
    elif pdffonts_bin is not None:
        font_out = subprocess.check_output([pdffonts_bin, str(pdf_path)], text=True)
        for fline in font_out.splitlines()[2:]:
            if re.search(r"\bType 3\b", fline):
                errors.append(f"{pdf_path}: rasterized Type 3 bitmap font detected: {fline.strip()}")
    if not log_path.is_file():
        errors.append(f"{log_path}: expected log file missing")
        continue

    raw_log = log_path.read_text(encoding="latin-1")
    # Join hard-wrapped 79-column TeX log lines only when nxt itself does not match
    lines = raw_log.splitlines()
    for idx, line in enumerate(lines, start=1):
        nxt = lines[idx] if idx < len(lines) else ""
        joined = (line + " " + nxt, line + nxt) if nxt else ()
        for rx in (undef_ref_re, undef_cit_re, mult_label_re):
            if rx.search(line) or (nxt and not rx.search(nxt) and any(rx.search(w) for w in joined)):
                errors.append(f"{log_path}:{idx}: {line.strip()}")
        if there_undef_re.search(line):
            errors.append(f"{log_path}:{idx}: {line.strip()}")
        if dup_dest_re.search(line) or (
            nxt and not dup_dest_re.search(nxt) and any(dup_dest_re.search(w) for w in joined)
        ):
            errors.append(f"{log_path}:{idx}: duplicate hyperref destination: {line.strip()}")
        m_over = overfull_re.search(line)
        if m_over:
            pt = float(m_over.group(1))
            if pt > 4.0:
                errors.append(f"{log_path}:{idx}: Overfull \\hbox ({pt:.2f}pt > 4.0pt): {line.strip()}")

# Cross-check hardcoded Main-Text display numbers in \mref{<key>}{<text>} against main.aux
main_aux_path = build_dir / "main.aux"
supp_body_path = Path("paper/supplement_body.tex")
if not main_aux_path.is_file():
    errors.append(f"{main_aux_path}: expected main.aux missing for \\mref cross-check")
elif supp_body_path.is_file():
    aux_labels: dict[str, str] = {}
    newlabel_re = re.compile(r"\\newlabel\{([^{}]+)\}\{\{((?:[^{}]|\{[^{}]*\})*)\}")
    for m_lbl in newlabel_re.finditer(main_aux_path.read_text(encoding="utf-8")):
        aux_labels[m_lbl.group(1)] = m_lbl.group(2)

    mref_re = re.compile(r"\\mref\{([^{}]+)\}\{([^{}]+)\}")
    for line_no, raw_line in enumerate(supp_body_path.read_text(encoding="utf-8").splitlines(), start=1):
        clean_line = re.sub(r"(?<!\\)%.*$", "", raw_line)
        for m_ref in mref_re.finditer(clean_line):
            key, disp = m_ref.group(1), m_ref.group(2)
            if key not in aux_labels:
                errors.append(
                    f"{supp_body_path}:{line_no}: \\mref{{{key}}}{{{disp}}} key missing from {main_aux_path}"
                )
                continue
            expected_num = aux_labels[key]
            extracted = disp.strip()
            if key.startswith("eq:"):
                extracted = re.sub(r"^(?:Eqs?\.|Equations?)~", "", extracted)
                if extracted.startswith("(") and extracted.endswith(")"):
                    extracted = extracted[1:-1]
            elif key.startswith(("thm:", "cor:", "prop:", "lem:")):
                extracted = re.sub(
                    r"^(?:Theorems?|Corollar(?:y|ies)|Propositions?|Lemmas?)~", "", extracted
                )
                extracted = re.sub(r"\(\d+\)$", "", extracted)
            elif key.startswith("sec:"):
                extracted = re.sub(r"^(?:Secs?\.|Sections?)~", "", extracted)
            elif key.startswith(("fig:", "tab:")):
                extracted = re.sub(r"^(?:Figs?\.|Figures?|Tables?)~", "", extracted)
                extracted = re.sub(r"\([a-z]\)$", "", extracted)
            if extracted != expected_num:
                errors.append(
                    f"{supp_body_path}:{line_no}: \\mref{{{key}}}{{{disp}}} display number "
                    f"'{extracted}' != {main_aux_path} label '{expected_num}'"
                )

if errors:
    for err in errors:
        print(f"LOG AUDIT FAIL: {err}", file=sys.stderr)
    sys.exit(1)

print(f"OK: {len(targets)} PDF target(s) compiled cleanly with 0 log-audit errors")
PY
