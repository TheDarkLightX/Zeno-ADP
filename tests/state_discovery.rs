use std::collections::BTreeSet;

use num_bigint::BigUint;
use zeno_adp::assurance::Label;
use zeno_adp::state_discovery::{
    minimum_feature_sets, Alignment, Error, Feature, FeatureSetBudget, Geometry, Observer,
    RawModel, Sense, Symbol, Verdict,
};

const A: Symbol = Alignment::MATCH;
const B: Symbol = Alignment::MISMATCH;
const D: Symbol = Alignment::DELETE;
const I: Symbol = Alignment::INSERT;

// The six-feature fixture tests every subset through size three. It
// retains a collision for each smaller subset and both size-three winners.
const FEATURE_WORK: usize = 1 + 6 + 15 + 20;
const FEATURE_SLOTS: usize = 3 + 6 * 4 + 15 * 5 + 2 * 4;
const FEATURE_BUDGET: FeatureSetBudget = FeatureSetBudget {
    max_candidates: FEATURE_WORK,
    max_certificate_slots: FEATURE_SLOTS,
};

/// A synthetic scorer (higher is better). Its score changes
/// depend on the last two operations.
fn two_symbol_score(word: &[Symbol]) -> i64 {
    let mut out = 0;
    for (n, &a) in word.iter().enumerate() {
        let h = &word[n.saturating_sub(2)..n];
        if a == A || a == B {
            out += if a == A { 3 } else { -2 };
        } else {
            out += if h.last() == Some(&a) { -1 } else { -3 };
            if h == [a, A] {
                out += 6;
            }
            if a == D && h == [B, A] {
                out += 5;
            }
        }
    }
    out
}

/// The two-symbol scorer plus a bonus of 4 for an insertion after B, A, D: horizon three.
fn horizon_three(word: &[Symbol]) -> i64 {
    let mut out = two_symbol_score(word);
    for n in 3..word.len() {
        if word[n] == I && word[n - 3..n] == [B, A, D] {
            out += 4;
        }
    }
    out
}

/// Affine gaps (Gotoh): match 2, mismatch -1, a run of L gaps of one kind -3-(L-1).
fn gotoh(word: &[Symbol]) -> i64 {
    let mut out = 0;
    for (n, &a) in word.iter().enumerate() {
        out += match a {
            A => 2,
            B => -1,
            _ if n > 0 && word[n - 1] == a => -1,
            _ => -3,
        };
    }
    out
}

fn binary_words(max: usize) -> Vec<Vec<u8>> {
    let mut words = vec![Vec::new()];
    let mut level = vec![Vec::new()];
    for _ in 0..max {
        let mut next = Vec::new();
        for word in &level {
            for &bit in b"01" {
                let mut longer: Vec<u8> = word.clone();
                longer.push(bit);
                next.push(longer);
            }
        }
        words.extend(next.iter().cloned());
        level = next;
    }
    words
}

/// Every alignment word in move order: diagonal, delete, insert.
fn alignment_words(x: &[u8], y: &[u8]) -> Vec<Vec<Symbol>> {
    let geometry = Alignment { x, y };
    let mut out = Vec::new();
    let mut stack = vec![(geometry.start(), Vec::new())];
    while let Some((cell, word)) = stack.pop() {
        if geometry.is_final(&cell) {
            out.push(word.clone());
        }
        for (symbol, next) in geometry.moves(&cell).into_iter().rev() {
            let mut longer = word.clone();
            longer.push(symbol);
            stack.push((next, longer));
        }
    }
    out
}

fn classes_as_words(
    raw: &RawModel,
    class_of: &[Option<usize>],
    horizon: usize,
) -> BTreeSet<BTreeSet<String>> {
    let names = ['A', 'B', 'D', 'I'];
    let mut groups: std::collections::BTreeMap<usize, BTreeSet<String>> = Default::default();
    for (state, class) in class_of.iter().enumerate() {
        if let Some(class) = class {
            let word: String = Observer::history(4, state)
                .unwrap()
                .iter()
                .map(|&s| names[s])
                .collect();
            assert!(word.len() <= horizon && raw.is_reachable(state));
            groups.entry(*class).or_default().insert(word);
        }
    }
    groups.into_values().collect()
}

fn set(words: &[&str]) -> BTreeSet<String> {
    words.iter().map(|w| w.to_string()).collect()
}

#[test]
fn two_symbol_scorer_quotient_has_seven_classes_and_exact_charts() {
    let mut scorer = |w: &[Symbol]| two_symbol_score(w);
    let mut raw = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut scorer).unwrap();
    // 21 histories times 4 symbols, plus the empty word.
    assert_eq!(raw.scorer_calls(), 85);
    let check = raw.check(&mut scorer, 8).unwrap();
    // The check asks every word up to length 8 once, the 85 read words included.
    assert_eq!(check.as_ref().words_checked(), (4u64.pow(9) - 1) / 3);
    assert_eq!(check.as_ref().scorer_calls(), (4usize.pow(9) - 1) / 3);
    let quotient = raw.quotient().unwrap();
    assert_eq!(quotient.as_ref().classes(), 7);
    let expected: BTreeSet<BTreeSet<String>> = [
        set(&["", "A", "AA"]),
        set(&["B", "AB", "BB", "DB", "IB"]),
        set(&["D", "AD", "BD", "DD", "ID"]),
        set(&["I", "AI", "BI", "DI", "II"]),
        set(&["BA"]),
        set(&["DA"]),
        set(&["IA"]),
    ]
    .into_iter()
    .collect();
    assert_eq!(
        classes_as_words(&raw, &quotient.as_ref().class_of, 2),
        expected
    );
    // Merging from any order reaches the same partition.
    let merged = raw.merging().finish().unwrap().into_inner();
    assert_eq!(classes_as_words(&raw, &merged.class_of, 2), expected);

    let words = binary_words(4);
    let (mut pairs, mut quotient_cells, mut raw_cells) = (0, 0, 0);
    for x in &words {
        for y in &words {
            let all = alignment_words(x, y);
            let best = all.iter().map(|w| two_symbol_score(w)).max().unwrap();
            let optimal: Vec<&Vec<Symbol>> =
                all.iter().filter(|w| two_symbol_score(w) == best).collect();
            let chart = quotient
                .chart(&Alignment { x, y }, Sense::Maximize)
                .unwrap();
            quotient_cells += chart.chart().cells().len();
            raw_cells += raw
                .raw_chart(&Alignment { x, y }, Sense::Maximize)
                .unwrap()
                .chart()
                .cells()
                .len();
            let solved = chart.solve(Some(&check)).unwrap().into_inner();
            assert_eq!(solved.score, i128::from(best));
            assert_eq!(solved.count, BigUint::from(optimal.len()));
            assert_eq!(&solved.word, optimal[0]);
            assert_eq!(i128::from(two_symbol_score(&solved.word)), solved.score);
            assert_eq!(solved.scorer_label, Label::Exact);
            pairs += 1;
        }
    }
    assert_eq!(pairs, 961);
    // The figures quoted in docs/EXACT.md: reachable chart cells over these pairs.
    assert_eq!((quotient_cells, raw_cells), (40_473, 71_753));
}

#[test]
fn every_pair_of_classes_has_a_refused_merge() {
    let mut scorer = |w: &[Symbol]| two_symbol_score(w);
    let raw = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut scorer).unwrap();
    let quotient = raw.quotient().unwrap().into_inner();
    for a in 0..quotient.classes() {
        for b in a + 1..quotient.classes() {
            let (probe, gains) = quotient.separating_probe(a, b).unwrap();
            assert!(!probe.is_empty());
            assert_ne!(gains[0], gains[1]);
        }
    }
    // The empty history and a mismatch agree on every one-symbol score change;
    // a two-symbol probe separates them.
    let mut merging = raw.merging();
    let empty = 0;
    let mismatch = 1 + B;
    let Verdict::Refused(refusal) = merging.propose(empty, mismatch).unwrap() else {
        panic!("the merge must be refused");
    };
    assert_eq!(refusal.probe.len(), 2);
    assert!(refusal.replay(&raw).is_ok());
    // Merging the empty history with A is admitted.
    assert!(matches!(
        merging.propose(empty, 1 + A).unwrap(),
        Verdict::Admitted { .. }
    ));
}

#[test]
fn gotoh_affine_gaps_have_three_classes_at_every_declared_horizon() {
    for horizon in 1..=3 {
        let mut scorer = |w: &[Symbol]| gotoh(w);
        let mut raw =
            RawModel::read(Observer::last_symbols(4, horizon).unwrap(), &mut scorer).unwrap();
        raw.check(&mut scorer, 6).unwrap();
        let quotient = raw.quotient().unwrap().into_inner();
        assert_eq!(quotient.classes(), 3, "horizon {horizon}");
        let start = quotient.start;
        let after = |s: Symbol| quotient.next[start][s];
        assert_eq!(after(A), start);
        assert_eq!(after(B), start);
        assert_ne!(after(D), after(I));
        assert_ne!(after(D), start);
    }
}

#[test]
fn a_declared_horizon_that_is_too_short_is_refused_at_the_boundary() {
    let mut scorer = |w: &[Symbol]| horizon_three(w);
    let observer = Observer::last_symbols(4, 2).unwrap();
    let mut raw = RawModel::read(observer.clone(), &mut scorer).unwrap();
    let Err(Error::Refuted(violation)) = raw.check(&mut scorer, 8) else {
        panic!("a horizon-three scorer must be refused at horizon two");
    };
    assert_eq!(violation.word, vec![B, A, D]);
    assert_eq!(violation.access, vec![A, D]);
    assert_eq!(violation.symbol, I);
    assert!(violation.replay(&observer, &mut scorer).is_ok());
}

#[test]
fn without_the_check_a_too_short_horizon_is_unchecked_beyond_the_table() {
    let mut scorer = |w: &[Symbol]| horizon_three(w);
    let mut raw = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut scorer).unwrap();
    // Length 3 covers only the words the table was read from.
    let check = raw.check(&mut scorer, 3).unwrap();
    let quotient = raw.quotient().unwrap();
    let mut wrong = 0;
    for x in &binary_words(4) {
        for y in &binary_words(4) {
            let best = alignment_words(x, y)
                .iter()
                .map(|w| horizon_three(w))
                .max()
                .unwrap();
            let solved = quotient
                .chart(&Alignment { x, y }, Sense::Maximize)
                .unwrap()
                .solve(Some(&check))
                .unwrap()
                .into_inner();
            if solved.score != i128::from(best) {
                wrong += 1;
                assert_eq!(solved.scorer_label, Label::Unchecked);
            }
            if solved.scorer_label == Label::Exact {
                assert_eq!(solved.score, i128::from(best));
            }
        }
    }
    assert!(wrong > 0);
}

#[test]
fn tampered_quotients_are_refused() {
    let mut scorer = |w: &[Symbol]| two_symbol_score(w);
    let raw = RawModel::read(Observer::last_symbols(4, 2).unwrap(), &mut scorer).unwrap();
    let quotient = raw.quotient().unwrap().into_inner();

    // Merge the two classes of the empty history and of B: the closure fails.
    let mut merged = quotient.clone();
    let (keep, drop) = (merged.class_of[0].unwrap(), merged.class_of[1 + B].unwrap());
    for class in merged.class_of.iter_mut().flatten() {
        if *class == drop {
            *class = keep;
        }
    }
    assert!(merged.verify(&raw).is_err());

    let mut transition = quotient.clone();
    transition.next[0][A] = (transition.next[0][A] + 1) % transition.classes();
    assert!(matches!(
        transition.verify(&raw),
        Err(Error::Closure { .. })
    ));

    let mut probe = quotient.clone();
    probe.probes.pop();
    assert!(matches!(probe.verify(&raw), Err(Error::Separation { .. })));
}

fn six_features() -> Vec<Feature> {
    // States index: none = 0, then symbols A, B, D, I as 1..=4 where needed.
    let gap = Observer::new(4, 0, vec![vec![0, 0, 1, 2]; 3]).unwrap();
    let last = |symbol: usize| symbol + 1;
    let mut tier_next = Vec::new();
    for state in 0..10 {
        let (previous, _bit) = (state / 2, state % 2);
        let row = (0..4)
            .map(|a| {
                let bit = usize::from(previous == last(a) && (a == D || a == I));
                last(a) * 2 + bit
            })
            .collect();
        tier_next.push(row);
    }
    let tier = Observer::new(4, 0, tier_next).unwrap();
    let parity = Observer::new(4, 0, vec![vec![0, 1, 0, 0], vec![1, 0, 1, 1]]).unwrap();
    let tail = Observer::new(4, 0, vec![vec![1, 2, 3, 4]; 5]).unwrap();
    let length = Observer::new(4, 0, vec![vec![1; 4], vec![2; 4], vec![0; 4]]).unwrap();
    let gaps = Observer::new(4, 0, vec![vec![0, 0, 1, 1], vec![1, 1, 0, 0]]).unwrap();
    vec![
        Feature::new(gap, vec![0, 1, 2]).unwrap(),
        Feature::new(tier, (0..10).map(|s| s % 2).collect()).unwrap(),
        Feature::new(parity, vec![0, 1]).unwrap(),
        Feature::new(tail, (0..5).collect()).unwrap(),
        Feature::new(length, vec![0, 1, 2]).unwrap(),
        Feature::new(gaps, vec![0, 1]).unwrap(),
    ]
}

/// A scorer with an unbounded history (lower is better): gap open 5, the second gap
/// symbol 1, later ones 3, and mismatches alternately 2 and 5.
fn parity_cost(word: &[Symbol]) -> i64 {
    let (mut cost, mut gap, mut run, mut mismatches) = (0, None, 0, 0);
    for &a in word {
        if a == D || a == I {
            cost += if Some(a) != gap {
                5
            } else if run == 1 {
                1
            } else {
                3
            };
            run = if Some(a) == gap { run + 1 } else { 1 };
            gap = Some(a);
        } else {
            if a == B {
                cost += 2 + 3 * (mismatches % 2);
                mismatches += 1;
            }
            gap = None;
            run = 0;
        }
    }
    cost
}

#[test]
fn six_feature_library_has_two_minimum_sets() {
    let (observer, values) = Feature::library(&six_features()).unwrap();
    let mut scorer = |w: &[Symbol]| parity_cost(w);
    let mut raw = RawModel::read(observer, &mut scorer).unwrap();
    raw.check(&mut scorer, 8).unwrap();
    let sets = minimum_feature_sets(&raw, &values, FEATURE_BUDGET).unwrap();
    let work_limit = FEATURE_WORK - 1;
    let low_work = FeatureSetBudget {
        max_candidates: work_limit,
        ..FEATURE_BUDGET
    };
    assert_eq!(
        minimum_feature_sets(&raw, &values, low_work),
        Err(Error::FeatureWorkLimit { limit: work_limit })
    );
    assert_eq!(
        sets.verify(&raw, &values, work_limit),
        Err(Error::FeatureWorkLimit { limit: work_limit })
    );
    let storage_limit = FEATURE_SLOTS - 1;
    let low_storage = FeatureSetBudget {
        max_certificate_slots: storage_limit,
        ..FEATURE_BUDGET
    };
    assert_eq!(
        minimum_feature_sets(&raw, &values, low_storage),
        Err(Error::FeatureStorageLimit {
            limit: storage_limit
        })
    );
    assert_eq!(sets.size, 3);
    assert_eq!(sets.sets, vec![vec![0, 1, 2], vec![1, 2, 3]]);
    // Every smaller set has a collision.
    assert_eq!(sets.collisions.len(), 1 + 6 + 15);
    sets.verify(&raw, &values, FEATURE_WORK).unwrap();
    // A dropped collision, a listed insufficient set and a missing set are refused.
    let mut short = sets.clone();
    short.collisions.pop();
    assert!(short.verify(&raw, &values, FEATURE_WORK).is_err());
    short.collisions.push(short.collisions[0].clone());
    assert_eq!(
        short.verify(&raw, &values, FEATURE_WORK),
        Err(Error::FeatureSets("a collision is listed twice"))
    );
    let mut extra = sets.clone();
    extra.sets.push(vec![0, 1, 4]);
    assert!(extra.verify(&raw, &values, FEATURE_WORK).is_err());
    let mut missing = sets.clone();
    missing.sets.pop();
    assert!(missing.verify(&raw, &values, FEATURE_WORK).is_err());
    let quotient = raw.quotient().unwrap();
    for x in &binary_words(3) {
        for y in &binary_words(3) {
            let best = alignment_words(x, y)
                .iter()
                .map(|w| parity_cost(w))
                .min()
                .unwrap();
            let solved = quotient
                .chart(&Alignment { x, y }, Sense::Minimize)
                .unwrap()
                .solve(None)
                .unwrap();
            assert_eq!(solved.as_ref().score, i128::from(best));
            assert_eq!(solved.as_ref().scorer_label, Label::Unchecked);
        }
    }
}

#[test]
fn feature_sets_verification_is_set_level() {
    use zeno_adp::assurance::Shape;
    use zeno_adp::state_discovery::FeatureSets;

    let (observer, values) = Feature::library(&six_features()).unwrap();
    let raw = RawModel::read(observer, &mut parity_cost).unwrap();
    let sets = minimum_feature_sets(&raw, &values, FEATURE_BUDGET).unwrap();
    assert_eq!(sets.sets, vec![vec![0, 1, 2], vec![1, 2, 3]]);
    let mut sets_reordered = sets.clone();
    sets_reordered.sets.reverse();
    sets_reordered.verify(&raw, &values, FEATURE_WORK).unwrap();
    let mut collisions_reordered = sets;
    collisions_reordered.collisions.reverse();
    collisions_reordered
        .verify(&raw, &values, FEATURE_WORK)
        .unwrap();
    assert_eq!(FeatureSets::SHAPE, Shape::SetLevel);
}

#[test]
fn removing_the_parity_feature_is_refused() {
    let mut library = six_features();
    library.remove(2);
    let (observer, _) = Feature::library(&library).unwrap();
    let mut scorer = |w: &[Symbol]| parity_cost(w);
    let mut raw = RawModel::read(observer.clone(), &mut scorer).unwrap();
    let Err(Error::Refuted(violation)) = raw.check(&mut scorer, 8) else {
        panic!("mismatch parity is needed");
    };
    assert_eq!(violation.symbol, B);
    assert!(violation.replay(&observer, &mut scorer).is_ok());
}

#[test]
fn observers_are_validated() {
    assert!(Observer::new(0, 0, vec![]).is_err());
    assert!(Observer::new(2, 1, vec![vec![0, 0]]).is_err());
    assert!(Observer::new(2, 0, vec![vec![0, 3]]).is_err());
    assert_eq!(Observer::history(4, 0).unwrap(), Vec::<Symbol>::new());
    assert_eq!(Observer::history(4, 5).unwrap(), vec![0, 0]);
    let last = Observer::last_symbols(2, 2).unwrap();
    assert_eq!(last.states(), 7);
    assert_eq!(last.state_after(&[1, 0, 1]), 3 + 1);
}

#[test]
fn empty_feature_findings_are_refused_first() {
    use zeno_adp::state_discovery::FeatureSets;
    let raw = RawModel::read(Observer::last_symbols(1, 0).unwrap(), &mut |_| 0).unwrap();
    // The empty certificate must be refused even when the feature table is malformed.
    let findings = FeatureSets {
        size: 12,
        sets: vec![],
        collisions: vec![],
    };
    let values = [vec![0; 24]];
    for values in [&values[..], &[]] {
        assert_eq!(
            findings.verify(&raw, values, 0),
            Err(Error::FeatureSets("no sufficient set is listed"))
        );
    }
    let missing_coverage = FeatureSets {
        sets: vec![(0..findings.size).collect()],
        ..findings
    };
    assert_eq!(
        missing_coverage.verify(&raw, &values, 0),
        Err(Error::FeatureSets("some smaller set has no collision"))
    );
}

#[test]
fn both_chart_builders_refuse_out_of_alphabet_moves() {
    struct OutsideAlphabet;
    impl Geometry for OutsideAlphabet {
        type Cell = bool;
        fn start(&self) -> bool {
            false
        }
        fn moves(&self, cell: &bool) -> Vec<(Symbol, bool)> {
            if *cell {
                vec![]
            } else {
                vec![(2, true)]
            }
        }
        fn is_final(&self, cell: &bool) -> bool {
            *cell
        }
    }
    let raw = RawModel::read(Observer::last_symbols(2, 0).unwrap(), &mut |_| 0).unwrap();
    let quotient = raw.quotient().unwrap();
    let raw_chart = std::panic::catch_unwind(|| raw.raw_chart(&OutsideAlphabet, Sense::Minimize));
    let quotient_chart =
        std::panic::catch_unwind(|| quotient.chart(&OutsideAlphabet, Sense::Minimize));
    for result in [raw_chart, quotient_chart] {
        assert!(matches!(
            result,
            Ok(Err(Error::SymbolOutOfRange { symbol: 2 }))
        ));
    }
}

#[test]
fn feature_library_refuses_an_edited_value_vector() {
    let mut feature = Feature::new(Observer::last_symbols(2, 0).unwrap(), vec![0]).unwrap();
    feature.value.clear();
    assert!(matches!(
        Feature::library(&[feature]),
        Err(Error::InvalidObserver(_))
    ));
}

#[test]
fn violation_replay_refuses_a_truncated_horizon() {
    let observer = Observer::last_symbols(2, 0).unwrap();
    let mut score = |word: &[Symbol]| i64::from(word.len() > 1);
    let mut raw = RawModel::read(observer.clone(), &mut score).unwrap();
    let Err(Error::Refuted(mut violation)) = raw.check(&mut score, 2) else {
        panic!("the one-state observer cannot represent the scorer");
    };
    assert_eq!(violation.replay(&observer, &mut score), Ok(()));
    violation.checked_length = 0;
    assert_eq!(
        violation.replay(&observer, &mut score),
        Err(Error::ReplayMismatch)
    );
}

#[test]
fn history_refuses_an_empty_alphabet() {
    assert_eq!(
        Observer::history(0, 1),
        Err(Error::InvalidObserver("the alphabet is empty"))
    );
}

#[test]
fn observer_rejects_unrepresentable_table_capacity() {
    assert_eq!(
        Observer::last_symbols(usize::MAX, 0),
        Err(Error::AllocationFailed)
    );
    assert_eq!(
        Observer::last_symbols(1, usize::MAX),
        Err(Error::AllocationFailed)
    );
    assert_eq!(
        Observer::last_symbols(2, usize::BITS as usize),
        Err(Error::AllocationFailed)
    );
    // Compare the arithmetic transition table to direct suffixes on small
    // alphabets, including unary and zero-horizon cases.
    for symbols in 1..=4 {
        for horizon in 0..=3 {
            let observer = Observer::last_symbols(symbols, horizon).unwrap();
            for state in 0..observer.states() {
                let history = Observer::history(symbols, state).unwrap();
                assert_eq!(observer.state_after(&history), state);
                for symbol in 0..symbols {
                    let mut word = history.clone();
                    word.push(symbol);
                    let suffix = &word[word.len().saturating_sub(horizon)..];
                    let next = observer.next(state, symbol);
                    assert_eq!(Observer::history(symbols, next).unwrap(), suffix);
                }
            }
        }
    }
}
