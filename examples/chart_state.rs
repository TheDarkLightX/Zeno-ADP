//! Find the coarsest history state of a reachable raw model, then align with it.
//!
//! The scorer charges affine gaps: opening a gap costs more than extending it.
//! It is read only through scores of operation words. Declaring the last two
//! operations as the history gives 21 states. Merging states that agree on every
//! future score change leaves three: after a match or mismatch, inside a
//! deletion, and inside an insertion.
//!
//! Run with `cargo run --offline --locked --example chart_state`.

use zeno_adp::assurance::Label;
use zeno_adp::state_discovery::{Alignment, Error, Observer, RawModel, Sense, Symbol};

/// Match 2, mismatch -1, a run of `n` gap symbols of one kind `-3 - (n - 1)`.
fn affine(word: &[Symbol]) -> i64 {
    let mut score = 0;
    for (n, &op) in word.iter().enumerate() {
        score += match op {
            Alignment::MATCH => 2,
            Alignment::MISMATCH => -1,
            _ if n > 0 && word[n - 1] == op => -1,
            _ => -3,
        };
    }
    score
}

fn main() -> Result<(), Error> {
    let mut scorer = |word: &[Symbol]| affine(word);
    let observer = Observer::last_symbols(Alignment::SYMBOLS, 2)?;
    let mut raw = RawModel::read(observer, &mut scorer)?;
    assert_eq!(raw.scorer_calls(), 85);
    // Compare the declared history with the scorer on every word of up to 8 operations.
    let check = raw.check(&mut scorer, 8)?;
    let quotient = raw.quotient()?;
    assert_eq!(quotient.as_ref().classes(), 3);

    let (x, y) = (b"GATTACA", b"GCATGCA");
    let chart = quotient.chart(&Alignment { x, y }, Sense::Maximize)?;
    let best = chart.solve(Some(&check))?.into_inner();
    let names = ['M', 'X', 'D', 'I'];
    let ops: String = best.word.iter().map(|&s| names[s]).collect();
    println!(
        "score {} with {} optimal alignments, first {ops}",
        best.score, best.count
    );
    assert_eq!(i128::from(affine(&best.word)), best.score);
    // These sequences have alignment words longer than the checked length.
    assert_eq!(best.scorer_label, Label::Unchecked);

    let short = quotient.chart(
        &Alignment {
            x: b"GAT",
            y: b"GT",
        },
        Sense::Maximize,
    )?;
    assert_eq!(
        short.solve(Some(&check))?.into_inner().scorer_label,
        Label::Exact
    );
    Ok(())
}
