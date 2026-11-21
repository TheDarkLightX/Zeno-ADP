#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
    printf 'usage: %s OUTPUT_DIRECTORY\n' "$0" >&2
    exit 2
fi
mkdir -p "$1"
output=$(cd "$1" && pwd)
cd "$(dirname "${BASH_SOURCE[0]}")/.."
mkdir -p "$output/lean"
export LEAN_PATH="$output/lean"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$output/target}"
export CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0
readonly lean_bin="${LEAN_BIN:-lean}"
readonly rust_version="${RUST_VERSION:-1.87.0}"

"$lean_bin" --version
for module in BellmanTabulation IntervalConvolution BellmanBag BellmanAlgebras BellmanLexicographic Instances BellmanProbability BellmanExpectation BellmanFrontiers DistinctIntersections Structures GeneratedRanks TrackRanks JointRetention ProductProvenance Wavefront ChildSequence; do
    "$lean_bin" -DwarningAsError=true -o "$LEAN_PATH/$module.olean" "verification/$module.lean"
done
cargo "+$rust_version" build --offline --locked --lib
rustc "+$rust_version" --edition=2021 -Dwarnings verification/rust_bridge.rs \
    -L "dependency=$CARGO_TARGET_DIR/debug/deps" \
    --extern "zeno_adp=$CARGO_TARGET_DIR/debug/libzeno_adp.rlib" -o "$output/rust-bridge"
"$output/rust-bridge" "$output/bridge-input.jsonl" "$output/rust-answers.jsonl"
"$lean_bin" -DwarningAsError=true --run verification/Bridge.lean \
    < "$output/bridge-input.jsonl" > "$output/lean-answers.jsonl"
python3 -I -B verification/compare.py "$output/rust-answers.jsonl" "$output/lean-answers.jsonl"
python3 -I -B verification/compare.py "$output/bridge-input.jsonl" "$output/rust-answers.jsonl" \
    --make-control "$output/bridge-control"
"$lean_bin" -DwarningAsError=true --run verification/Bridge.lean reverse \
    < "$output/bridge-control.chart" > "$output/bridge-control.lean"
python3 -I -B verification/compare.py "$output/bridge-control.rust" "$output/bridge-control.lean" --control
python3 -B verification/test_compare.py
rustc "+$rust_version" --edition=2021 -Dwarnings verification/log_leaves.rs \
    -L "dependency=$CARGO_TARGET_DIR/debug/deps" \
    --extern "zeno_adp=$CARGO_TARGET_DIR/debug/libzeno_adp.rlib" -o "$output/log-leaves"
python3 -I -B verification/check_log_leaves.py "$output/log-leaves"
