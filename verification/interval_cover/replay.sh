#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
files=(lean-sweep/Sweep.lean CoverCount.lean ChoiceContract.lean)
if rg -nw 'sorry|axiom|admit' "${files[@]}"; then
    echo "Found a placeholder or axiom in the interval-cover proofs" >&2
    exit 1
else
    status=$?
    [[ $status == 1 ]] || exit "$status"
fi
echo "Scanned all three proof sources for sorry, axiom and admit. Zero matches."
for file in "${files[@]}"; do
    prlimit --as=8589934592 -- lean -j1 -DwarningAsError=true "$file"
done
python3 -B full_cover_count.py
python3 -B cover_choice.py
