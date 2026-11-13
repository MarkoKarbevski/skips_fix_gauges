#!/bin/bash
# Compile paper A, B, C, D and/or E, copy the PDFs next to their sources, and run the define-before-use check.
# A: the absorb paper. B: the merged unlock paper. C: the "at least" paper. D: the "exactly" paper.
# E: the paper on the functional dimension.
# Usage: tools/build.sh [A|B|C|D|E|all]   (PAPER_BUILD_DIR sets where LaTeX writes its build files)
# Exit 1 if LaTeX fails, a reference is undefined, or the check flags a use before definition.
cd "$(dirname "$0")/.." || exit 1
out=${PAPER_BUILD_DIR:-/tmp/paper_build}
status=0
build() {
  k=$1; dir=$2; name=$3
  mkdir -p "$out/$k"
  (cd "$dir" && latexmk -pdf -interaction=nonstopmode -outdir="$out/$k" "$name.tex" > "$out/$k/latexmk.out" 2>&1) || { echo "paper $k: LaTeX failed, see $out/$k/latexmk.out"; status=1; }
  undef=$(grep -o "Reference \`[^']*' on page [0-9]* undefined\|Citation \`[^']*' on page [0-9]* undefined" "$out/$k/$name.log" | sort -u)
  [ -n "$undef" ] && { echo "paper $k: $undef"; status=1; }
  grep -o 'Overfull \\hbox ([0-9.]*pt too wide)[^0-9]*[0-9-]*' "$out/$k/$name.log" | sed "s/^/paper $k: /"
  cp "$out/$k/$name.pdf" "$dir/$name.pdf"
  echo "paper $k: $(pdfinfo "$dir/$name.pdf" | grep Pages)"
  python3 tools/check_flow.py "$dir/$name.tex" tools/glossary_$k.py tools/flow_allow_$k.txt > "$out/$k/flow.txt"; fs=$?
  grep -v '^    unit' "$out/$k/flow.txt" | grep -v 'flow graph written' | sed "s/^/paper $k: /"
  [ $fs -ne 0 ] && status=1
}
case ${1:-all} in
  A|all) build A new_paper_absorb_skip new_paper_absorb_skip ;;&
  B|all) build B new_paper_skips_unlock_d2_params new_paper_skips_unlock_d2_params ;;&
  C|all) build C new_paper_skips_at_least new_paper_skips_at_least ;;&
  D|all) [ -f new_paper_skips_exactly/new_paper_skips_exactly.tex ] && build D new_paper_skips_exactly new_paper_skips_exactly ;;&
  E|all) [ -f new_paper_functional_dimension/new_paper_functional_dimension.tex ] && build E new_paper_functional_dimension new_paper_functional_dimension ;;
esac
exit $status
