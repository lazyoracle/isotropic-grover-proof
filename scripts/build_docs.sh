#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

if [ -d "$HOME/.elan/bin" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi

LEAN_REV="$(cut -d: -f2 < lean-toolchain | tr -d '[:space:]')"

mkdir -p docbuild
EXPECTED_LAKEFILE="$(cat <<EOF
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "isotropic-grover-proof"
path = "../"

[[require]]
name = "doc-gen4"
scope = "leanprover"
rev = "$LEAN_REV"
EOF
)"

if [ ! -f docbuild/lakefile.toml ] || [ "$(cat docbuild/lakefile.toml)" != "$EXPECTED_LAKEFILE" ]; then
  printf '%s\n' "$EXPECTED_LAKEFILE" > docbuild/lakefile.toml
  rm -f docbuild/lake-manifest.json docbuild/.root-manifest.sha256
fi

(
  cd docbuild
  if [ ! -f lake-manifest.json ] \
    || [ ! -d ../.lake/packages/doc-gen4 ] \
    || [ ! -d ../.lake/packages/MD4Lean ] \
    || [ ! -d ../.lake/packages/BibtexQuery ] \
    || [ ! -d ../.lake/packages/UnicodeBasic ] \
    || [ ! -d ../.lake/packages/leansqlite ] \
    || ! sha256sum -c --status .root-manifest.sha256 2>/dev/null; then
    MATHLIB_NO_CACHE_ON_UPDATE=1 lake update isotropic-grover-proof
    sha256sum ../lake-manifest.json > .root-manifest.sha256
  fi
  rm -f .lake/build/doc-data/*.docs_built
  rm -rf .lake/build/doc/IsotropicGroverProof .lake/build/doc/IsotropicGroverProof.html
  lake build IsotropicGroverProof:docs
)

rm -rf _pages && mkdir -p _pages
cp -r docbuild/.lake/build/doc _pages/docs

for page in \
  "_pages/docs/IsotropicGroverProof.html" \
  "_pages/docs/IsotropicGroverProof/MainTheorem.html" \
  "_pages/docs/IsotropicGroverProof/QuantumChannel.html" \
  "_pages/docs/IsotropicGroverProof/GroverCircuit.html"; do
  if [ ! -s "$page" ]; then
    echo "error: expected generated documentation page missing or empty: $page" >&2
    exit 1
  fi
done

grep -q "isotropicGrover_main" _pages/docs/IsotropicGroverProof/MainTheorem.html
grep -q "depolarizingChannel" _pages/docs/IsotropicGroverProof/QuantumChannel.html
grep -q "noisyGrover_circuit_bornProb" _pages/docs/IsotropicGroverProof/GroverCircuit.html
