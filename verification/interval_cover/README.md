# Interval-cover checks

From this directory, run `bash replay.sh` with Lean 4.30.0 selected, Python 3,
ripgrep and util-linux installed. With elan, select the local toolchain using
`ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0 bash replay.sh`. The script scans the three proof sources
for placeholders and axiom declarations, runs Lean with one worker and
an 8 GiB address-space limit, and runs both Python checkers. Each theorem
prints its axiom dependencies.

- `lean-sweep/Sweep.lean` establishes the sweep geometry, gap retirement
  and the correspondence between indexed subsets and include/skip sequences.
  Different legal right edges can be distinguished when all valid future
  menus are allowed.
- `CoverCount.lean` establishes local cost-shift, choice and doubling laws.
  `ChoiceContract.lean` checks the partition and unanimity laws.
- `full_cover_count.py` compares its sweep to exhaustive selection and
  checks the exact 7^50,000 fixture. `cover_choice.py` checks independent
  interventions, including forced choices that raise the optimum.

Rust differential tests exercise the actual sparse and range structures
and the reverse computation. Run `cargo test --offline --locked` at the
repository root. The real-data benchmark has additional fixture tests in
`cargo test --offline --locked --example interval_cover_cross_bench`.
[Interval-cover guide](../../docs/INTERVAL-COVER.md)
