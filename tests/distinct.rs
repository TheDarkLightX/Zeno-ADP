use std::collections::{BTreeMap, BTreeSet};
use zeno_adp::distinct::{BinaryTreeGrammar, Constructor, Production};
use zeno_adp::queries::{count, derivation_count, trees, TreeMultiplicity::DistinctTrees};
use zeno_adp::{Chart, Error, Tree};

// Replays the research domain: two starts, two labels, four ordered binary
// child pairs per start, and exact sizes through the first five-leaf boundary.
const NONTERMINALS: usize = 2;
const LEAF_LABELS: usize = 2;
const MAX_LEAVES: usize = 4;
const RULES_PER_ROW: usize = LEAF_LABELS + NONTERMINALS * NONTERMINALS;

type Terms = BTreeSet<Tree<Constructor<usize>>>;

fn grammar(mask: usize) -> BinaryTreeGrammar<usize> {
    let rows = (0..NONTERMINALS)
        .map(|start| {
            let candidates =
                (0..LEAF_LABELS)
                    .map(Production::Leaf)
                    .chain((0..NONTERMINALS).flat_map(|left| {
                        (0..NONTERMINALS).map(move |right| Production::Branch { left, right })
                    }));
            candidates
                .enumerate()
                .filter(|(index, _)| mask & (1 << (start * RULES_PER_ROW + index)) != 0)
                .map(|(_, rule)| rule)
                .collect()
        })
        .collect();
    BinaryTreeGrammar::new(rows).unwrap()
}

fn reference_sets(chart: &Chart<Constructor<usize>>) -> BTreeMap<usize, Vec<Terms>> {
    let root = chart.root();
    let mut by_split = BTreeMap::<_, Vec<_>>::new();
    for rule in &chart.cells()[root] {
        // Leaf count determines the split uniquely from the first child.
        let split = rule
            .children
            .first()
            .map_or(0, |child| child / NONTERMINALS);
        let mut cells = chart.cells().to_vec();
        cells[root] = vec![rule.clone()];
        let singleton = Chart::new(cells, root).unwrap();
        by_split
            .entry(split)
            .or_default()
            .push(trees(&singleton, DistinctTrees).into_iter().collect());
    }
    by_split
}

fn inclusion_exclusion(families: &BTreeMap<usize, Vec<Terms>>) -> (i64, i64, i64, usize) {
    let (mut exact, mut disjoint, mut pairwise, mut terms) = (0, 0, 0, 0);
    for alternatives in families.values() {
        for mask in 1usize..(1 << alternatives.len()) {
            let mut selected = alternatives
                .iter()
                .enumerate()
                .filter(|(index, _)| mask & (1 << index) != 0)
                .map(|(_, set)| set);
            let first = selected.next().unwrap();
            let intersection = first
                .iter()
                .filter(|term| selected.clone().all(|language| language.contains(*term)))
                .count() as i64;
            let multiplicity = mask.count_ones();
            let term = if multiplicity % 2 == 1 {
                intersection
            } else {
                -intersection
            };
            exact += term;
            if multiplicity == 1 {
                disjoint += term;
            }
            if multiplicity <= 2 {
                pairwise += term;
            }
            terms += 1;
        }
    }
    (exact, disjoint, pairwise, terms)
}

#[test]
fn complete_semantic_intersection_domain() {
    let mut cells = 0;
    let mut intersections = 0;
    let mut literal_terms = 0;
    let mut profile_pairs = 0;
    let mut profile_projections = 0;
    let mut disjoint_failures = 0;
    let mut truncation_failures = 0;
    let mut ambiguous = 0;
    let mut first_disjoint = None;
    let mut first_truncation = None;
    for mask in 0..(1 << (NONTERMINALS * RULES_PER_ROW)) {
        let grammar = grammar(mask);
        let fast = grammar.distinct_counts(MAX_LEAVES).unwrap();
        let mut profiles_per_size = vec![0];
        for size in 1..=MAX_LEAVES {
            let charts: Vec<_> = (0..NONTERMINALS)
                .map(|start| grammar.chart(size, start).unwrap())
                .collect();
            let languages: Vec<Terms> = charts
                .iter()
                .map(|chart| trees(chart, DistinctTrees).into_iter().collect())
                .collect();
            let overlap = languages[0].intersection(&languages[1]).count();
            assert_eq!(fast.intersection(size, 0, &[1]).unwrap(), overlap as u128);
            intersections += 1;
            profiles_per_size.push(
                usize::from(languages[0].len() > overlap)
                    + usize::from(languages[1].len() > overlap)
                    + usize::from(overlap > 0),
            );
            profile_projections += NONTERMINALS * profiles_per_size[size];
            profile_pairs += (1..size)
                .map(|split| profiles_per_size[split] * profiles_per_size[size - split])
                .sum::<usize>();
            for (start, chart) in charts.iter().enumerate() {
                let reference = languages[start].len();
                assert_eq!(fast.count(size, start).unwrap(), reference as u128);
                assert_eq!(count(chart, DistinctTrees).unwrap(), reference as u128);
                ambiguous += usize::from(derivation_count(chart).unwrap() > reference as u128);
                let (exact, disjoint, pairwise, terms) =
                    inclusion_exclusion(&reference_sets(chart));
                assert_eq!(exact, reference as i64);
                if disjoint != exact {
                    disjoint_failures += 1;
                    first_disjoint.get_or_insert((mask, start, size, disjoint, exact));
                }
                if pairwise != exact {
                    truncation_failures += 1;
                    first_truncation.get_or_insert((mask, start, size, pairwise, exact));
                }
                literal_terms += terms;
                cells += 1;
                intersections += 1; // Each singleton language is an intersection.
            }
        }
    }
    assert_eq!(disjoint_failures, 9_716);
    assert_eq!(truncation_failures, 3_888);
    println!("{cells} start cells, {intersections} intersections including singleton languages, {ambiguous} ambiguous cells, 0 disagreements");
    println!("{literal_terms} literal terms, {profile_pairs} profile pairs, {profile_projections} profile projections");
    println!("disjoint control {disjoint_failures}: {first_disjoint:?}; pairwise control {truncation_failures}: {first_truncation:?}");
}

#[test]
fn duplicate_productions_and_wide_profiles() {
    // One more nonterminal than fits in a u64 membership mask.
    const NONTERMINALS: usize = u64::BITS as usize + 1;
    let mut productions = vec![vec![Production::Leaf('a')]; NONTERMINALS];
    productions[0].push(Production::Leaf('a'));
    let grammar = BinaryTreeGrammar::new(productions).unwrap();
    let counts = grammar.distinct_counts(1).unwrap();
    assert_eq!(
        counts.intersection(1, 0, &[NONTERMINALS - 1, 0]).unwrap(),
        1
    );
    assert_eq!(derivation_count(&grammar.chart(1, 0).unwrap()).unwrap(), 2);
    assert_eq!(counts.count(0, 0), Ok(0));
    assert_eq!(
        counts.count(1, NONTERMINALS),
        Err(Error::InvalidNonterminal(NONTERMINALS))
    );
    assert_eq!(counts.count(2, 0), Err(Error::LeafCountOutOfRange(2)));
    assert!(matches!(
        BinaryTreeGrammar::<char>::new(vec![vec![Production::Branch { left: 0, right: 1 }]]),
        Err(Error::InvalidNonterminal(1))
    ));
}
