#!/usr/bin/env bash
# Regenerate paper/sqg-identity.pdf from paper/sqg-identity.md.
#
# Requirements:
#   - pandoc >= 3.0
#   - a LaTeX engine with xelatex (TeX Live, MacTeX, MiKTeX, tectonic…)
#   - STIX Two Math and a serif text font (defaults to Times New Roman)
#
# Usage:
#   scripts/build-paper.sh
set -euo pipefail

cd "$(dirname "$0")/.."

IN="paper/sqg-identity.md"
OUT="paper/sqg-identity.pdf"

if ! command -v pandoc >/dev/null 2>&1; then
  echo "error: pandoc not found on PATH" >&2
  exit 1
fi

if ! command -v xelatex >/dev/null 2>&1; then
  echo "error: xelatex not found on PATH (install TeX Live / MacTeX)" >&2
  exit 1
fi

if [ ! -f "$IN" ]; then
  echo "error: $IN not found" >&2
  exit 1
fi

echo "Building $OUT from $IN ..."
pandoc "$IN" \
  -o "$OUT" \
  --pdf-engine=xelatex \
  -V geometry:margin=1in \
  -V fontsize=11pt \
  -V mainfont="texgyretermes-regular.otf" \
  -V mainfontoptions="BoldFont=texgyretermes-bold.otf, ItalicFont=texgyretermes-italic.otf, BoldItalicFont=texgyretermes-bolditalic.otf" \
  -V mathfont="texgyretermes-math.otf" \
  --toc --toc-depth=3 \
  --number-sections

echo "Done: $OUT"
ls -la "$OUT"
