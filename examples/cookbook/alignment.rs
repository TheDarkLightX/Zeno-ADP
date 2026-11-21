use super::{step, words, Checks, Step};
use std::collections::BTreeMap;
use zeno_adp::algebras::{
    pareto_min, Additive, Cost, Count, Minimum, MinimumCount, Optimum, ScoredOperator,
};
use zeno_adp::compiled;
use zeno_adp::grammars::{self, Align, LocalAlign};
use zeno_adp::queries::TreeMultiplicity;
use zeno_adp::{
    compiled_grammar, enumerate, tabulate_cells, Algebra, Chart, Error, Operator, Rule, Tree,
};

const PAIR_BOUND: usize = 2; // Includes consecutive and split gaps and repeated hits.

fn pairs() -> impl Iterator<Item = (Vec<u8>, Vec<u8>)> {
    let all = words(b"ab", PAIR_BOUND);
    all.clone().into_iter().flat_map(move |left| {
        all.clone()
            .into_iter()
            .map(move |right| (left.clone(), right))
    })
}

fn raw_paths(left: &[u8], right: &[u8]) -> Vec<Vec<Align>> {
    let mut paths = Vec::new();
    let mut append = |a, b, column| {
        paths.extend(raw_paths(a, b).into_iter().map(|mut path| {
            path.push(column);
            path
        }));
    };
    match (left.split_last(), right.split_last()) {
        (None, None) => paths.push(Vec::new()),
        (Some((&a, l)), Some((&b, r))) => {
            append(l, r, Align::Diagonal { left: a, right: b });
            append(l, right, Align::Left(a));
            append(left, r, Align::Right(b));
        }
        (Some((&a, l)), None) => append(l, right, Align::Left(a)),
        (None, Some((&b, r))) => append(left, r, Align::Right(b)),
    }
    paths
}

fn global_cost(path: &[Align]) -> i64 {
    path.iter()
        .map(|&column| match column {
            Align::Diagonal { left, right } => i64::from(left != right),
            Align::Left(_) | Align::Right(_) => 1,
            Align::Start => 0,
        })
        .sum()
}

fn columns(tree: &Tree<Align>) -> Vec<Align> {
    let mut values = Vec::new();
    let mut node = tree;
    while let [child] = node.children.as_slice() {
        values.push(node.operator);
        node = child;
    }
    assert_eq!(node.operator, Align::Start);
    values.reverse();
    values
}

pub fn global() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for (left, right) in pairs() {
        let source = grammars::alignment_source(&left, &right)?;
        let chart = grammars::alignment(&left, &right)?;
        checks.chart(&chart);
        let best = compiled::best(&source)?;
        let minimum = tabulate_cells(&chart, &Minimum)?;
        let ties = tabulate_cells(&chart, &MinimumCount)?;
        checks.equal_values(best.scores().cells(), &minimum);
        let width = right.len() + 1;
        let mut direct = vec![(0_i64, 1_u128); (left.len() + 1) * width];
        for i in 0..=left.len() {
            for j in 0..=right.len() {
                let rank = i * width + j;
                if rank > 0 {
                    let mut candidates = Vec::new();
                    if i > 0 {
                        let (cost, n) = direct[rank - width];
                        candidates.push((cost + 1, n));
                    }
                    if j > 0 {
                        let (cost, n) = direct[rank - 1];
                        candidates.push((cost + 1, n));
                    }
                    if i > 0 && j > 0 {
                        let (cost, n) = direct[rank - width - 1];
                        candidates.push((cost + i64::from(left[i - 1] != right[j - 1]), n));
                    }
                    let cost = candidates.iter().map(|x| x.0).min().unwrap();
                    direct[rank] = (
                        cost,
                        candidates.iter().filter(|x| x.0 == cost).map(|x| x.1).sum(),
                    );
                }
                let (cost, count) = direct[rank];
                assert_eq!(
                    ties[rank],
                    [Optimum {
                        cost: Cost::Finite(cost),
                        count
                    }]
                );
                assert_eq!(minimum[rank], [Cost::Finite(cost)]);
            }
        }
        let mut paths = raw_paths(&left, &right);
        paths.sort_by_key(|path| global_cost(path));
        const PREFIX_ANSWERS: usize = 3; // Exposes ties and truncation together.
        for limit in [PREFIX_ANSWERS, paths.len() + 1] {
            let ranked = best
                .recover()
                .k_lowest(limit, TreeMultiplicity::Derivations)?;
            let actual: Vec<_> = ranked.iter().map(|x| (x.value, columns(&x.tree))).collect();
            assert!(actual.into_iter().eq(paths
                .iter()
                .take(limit)
                .map(|p| (Cost::Finite(global_cost(p)), p.clone()))));
        }
    }
    Ok(checks)
}

fn local_identity(tree: &Tree<LocalAlign>) -> Option<((usize, usize), Vec<Align>)> {
    let mut node = tree;
    let mut path = Vec::new();
    loop {
        match node.operator {
            LocalAlign::Empty => return None,
            LocalAlign::End => {}
            LocalAlign::Column(column) => path.push(column),
            LocalAlign::Start { left, right } => {
                path.reverse();
                return Some(((left, right), path));
            }
        }
        node = &node.children[0];
    }
}

pub fn local() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for (left, right) in pairs() {
        let chart = grammars::local_alignment(&left, &right)?;
        let source = grammars::local_alignment_source(&left, &right)?;
        checks.chart(&chart);
        checks.compiled(&source, &chart, &Additive::default())?;
        let width = right.len() + 1;
        let size = (left.len() + 1) * width;
        let mut reset = vec![0_i64; size];
        let scores = tabulate_cells(&chart, &Minimum)?;
        let mut direct = vec![None]; // One empty alignment, regardless of starts.
        for i in 0..=left.len() {
            for j in 0..=right.len() {
                let rank = i * width + j;
                let mut endings = Vec::new();
                if i > 0 {
                    endings.push(reset[rank - width] + 1);
                }
                if j > 0 {
                    endings.push(reset[rank - 1] + 1);
                }
                if i > 0 && j > 0 {
                    let score = if left[i - 1] == right[j - 1] { -2 } else { 1 };
                    endings.push(reset[rank - width - 1] + score);
                }
                let best = endings.into_iter().min();
                assert_eq!(scores[rank], [Cost::Finite(0)]);
                assert!(scores[size + rank]
                    .iter()
                    .copied()
                    .eq(best.map(Cost::Finite)));
                reset[rank] = best.unwrap_or(0).min(0);
                for a in 0..=i {
                    for b in 0..=j {
                        if (a, b) != (i, j) {
                            direct.extend(
                                raw_paths(&left[a..i], &right[b..j])
                                    .into_iter()
                                    .map(|path| Some(((a, b), path))),
                            );
                        }
                    }
                }
            }
        }
        assert_eq!(
            scores[chart.root()],
            [Cost::Finite(*reset.iter().min().unwrap())]
        );
        let mut actual: Vec<_> = enumerate(&chart).iter().map(local_identity).collect();
        // Align has a natural constructor order. Sorting preserves multiplicity.
        actual.sort();
        direct.sort();
        assert_eq!(actual, direct);
    }
    Ok(checks)
}

const OPEN: i64 = 3; // A one-column gap costs more than a substitution.
const EXTEND: i64 = 1; // Extending an open gap is cheaper than opening another.
const SUBSTITUTION: i64 = 2;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Match,
    Left,
    Right,
}

const MODES: [Mode; 3] = [Mode::Match, Mode::Left, Mode::Right];

fn affine_chart(left: &[u8], right: &[u8]) -> Result<Chart<Step>, Error> {
    let width = right.len() + 1;
    let rank = |i, j, mode| (i * width + j) * MODES.len() + mode as usize;
    let root = rank(left.len(), right.len(), Mode::Right) + 1;
    let mut rows = vec![vec![]; root + 1];
    rows[0].push(step("start", 0, []));
    for i in 0..=left.len() {
        for j in 0..=right.len() {
            for prev in MODES {
                if i > 0 && j > 0 {
                    let penalty = i64::from(left[i - 1] != right[j - 1]) * SUBSTITUTION;
                    rows[rank(i, j, Mode::Match)].push(step(
                        "diagonal",
                        penalty,
                        [rank(i - 1, j - 1, prev)],
                    ));
                }
                if i > 0 {
                    let cost = if prev == Mode::Left { EXTEND } else { OPEN };
                    rows[rank(i, j, Mode::Left)].push(step("left", cost, [rank(i - 1, j, prev)]));
                }
                if j > 0 {
                    let cost = if prev == Mode::Right { EXTEND } else { OPEN };
                    rows[rank(i, j, Mode::Right)].push(step("right", cost, [rank(i, j - 1, prev)]));
                }
            }
        }
    }
    for mode in MODES {
        rows[root].push(step("finish", 0, [rank(left.len(), right.len(), mode)]));
    }
    Chart::new(rows, root)
}

fn mode(column: &Align) -> Mode {
    match column {
        Align::Left(_) => Mode::Left,
        Align::Right(_) => Mode::Right,
        _ => Mode::Match,
    }
}

fn run_cost(path: &[Align]) -> i64 {
    path.chunk_by(|a, b| mode(a) != Mode::Match && mode(a) == mode(b))
        .map(|run| match run[0] {
            Align::Diagonal { left, right } => i64::from(left != right) * SUBSTITUTION,
            _ => OPEN + (run.len() as i64 - 1) * EXTEND,
        })
        .sum()
}

fn optima(costs: impl Iterator<Item = i64>) -> Vec<Optimum> {
    let mut best = None;
    let mut count = 0;
    for cost in costs {
        if best.is_none_or(|x| x > cost) {
            best = Some(cost);
            count = 0;
        }
        count += u128::from(best == Some(cost));
    }
    best.map(|cost| Optimum {
        cost: Cost::Finite(cost),
        count,
    })
    .into_iter()
    .collect()
}

pub fn affine() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for (left, right) in pairs().chain([(b"aaa".to_vec(), b"a".to_vec())]) {
        let chart = affine_chart(&left, &right)?;
        checks.chart(&chart);
        let scores = tabulate_cells(&chart, &MinimumCount)?;
        let mut rank = 0;
        for i in 0..=left.len() {
            for j in 0..=right.len() {
                let paths = raw_paths(&left[..i], &right[..j]);
                for last in MODES {
                    let costs = paths
                        .iter()
                        .filter(|p| p.last().map_or(Mode::Match, mode) == last)
                        .map(|p| run_cost(p));
                    assert_eq!(scores[rank], optima(costs));
                    rank += 1;
                }
            }
        }
        assert_eq!(
            scores[chart.root()],
            optima(raw_paths(&left, &right).iter().map(|p| run_cost(p)))
        );
    }
    Ok(checks)
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Infix {
    Core(Step),
    At(usize, usize),
}

impl Operator for Infix {
    fn arity(&self) -> usize {
        match self {
            Self::Core(op) => op.arity(),
            Self::At(..) => 1,
        }
    }
}
impl zeno_adp::algebras::ScoredOperator for Infix {
    fn cost(&self) -> Cost {
        match self {
            Self::Core(op) => op.cost(),
            Self::At(..) => Cost::Finite(0),
        }
    }
}

pub fn infix() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for (pattern, target) in pairs() {
        let mut rows = Vec::new();
        let mut ends = Vec::new();
        for a in 0..=target.len() {
            for b in a..=target.len() {
                let core = affine_chart(&pattern, &target[a..b])?;
                let offset = rows.len();
                rows.extend(core.cells().iter().map(|rules| {
                    rules
                        .iter()
                        .map(|r| {
                            Rule::new(
                                Infix::Core(r.operator),
                                r.children.iter().map(|&x| x + offset).collect::<Vec<_>>(),
                            )
                        })
                        .collect::<Vec<_>>()
                }));
                ends.push(Rule::new(Infix::At(a, b), [core.root() + offset]));
            }
        }
        let root = rows.len();
        rows.push(ends);
        let chart = Chart::new(rows, root)?;
        checks.chart(&chart);
        let scores = tabulate_cells(&chart, &Minimum)?;
        if pattern.is_empty() && target == b"a" {
            // Empty cores cost zero. The sole nonempty core pays a gap opening.
            assert_eq!(scores[root], [Cost::Finite(0)], "empty pattern score");
            let winning_ends: Vec<_> = chart.cells()[root]
                .iter()
                .filter(|rule| {
                    assert_eq!(rule.children.len(), 1);
                    scores[rule.children[0]] == [Cost::Finite(0)]
                })
                .map(|rule| &rule.operator)
                .collect();
            assert_eq!(winning_ends, [&Infix::At(0, 0), &Infix::At(1, 1)]);
        }
        let expected: Vec<_> = (0..=target.len())
            .flat_map(|start| (start..=target.len()).map(move |end| (start, end)))
            .map(|(start, end)| {
                let cost = raw_paths(&pattern, &target[start..end])
                    .iter()
                    .map(|path| run_cost(path))
                    .min()
                    .unwrap();
                (start, end, cost)
            })
            .collect();
        let best = expected.iter().map(|x| x.2).min().unwrap();
        assert_eq!(scores[root], [Cost::Finite(best)]);
        let mut winners = Vec::new();
        assert_eq!(chart.cells()[root].len(), expected.len());
        for (rule, &(a, b, cost)) in chart.cells()[root].iter().zip(&expected) {
            assert_eq!(rule.operator, Infix::At(a, b));
            assert_eq!(rule.children.len(), 1);
            assert_eq!(scores[rule.children[0]], [Cost::Finite(cost)]);
            if cost == best {
                winners.push((a, b));
            }
        }
        let recovered =
            zeno_adp::queries::co_minimal(&chart, &Minimum, TreeMultiplicity::Derivations)?;
        let mut actual: Vec<_> = recovered
            .iter()
            .map(|w| match w.tree.operator {
                Infix::At(a, b) => (a, b),
                _ => unreachable!(),
            })
            .collect();
        actual.dedup();
        assert_eq!(actual, winners);
    }
    Ok(checks)
}

const TRACKS: usize = 3;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Triple {
    Start,
    Column([Option<u8>; TRACKS]),
}

impl Operator for Triple {
    fn arity(&self) -> usize {
        usize::from(matches!(self, Self::Column(_)))
    }
}

impl ScoredOperator for Triple {
    fn cost(&self) -> Cost {
        Cost::Finite(match *self {
            Self::Start => 0,
            Self::Column([a, b, c]) => i64::from(a != b) + i64::from(a != c) + i64::from(b != c),
        })
    }
}

fn column(tracks: [&[u8]; TRACKS], ends: [usize; TRACKS], advances: [bool; TRACKS]) -> Triple {
    Triple::Column(std::array::from_fn(|i| {
        advances[i].then(|| tracks[i][ends[i] - 1])
    }))
}

compiled_grammar! {
    fn triple(input: u8) -> Triple {
        prefix_tracks 3 |tracks, ends|;
        empty Start => Ok(Some(Triple::Start));
        step A [true, false, false] => Ok(Some(column(tracks, ends, [true, false, false])));
        step B [false, true, false] => Ok(Some(column(tracks, ends, [false, true, false])));
        step AB [true, true, false] => Ok(Some(column(tracks, ends, [true, true, false])));
        step C [false, false, true] => Ok(Some(column(tracks, ends, [false, false, true])));
        step AC [true, false, true] => Ok(Some(column(tracks, ends, [true, false, true])));
        step BC [false, true, true] => Ok(Some(column(tracks, ends, [false, true, true])));
        step ABC [true, true, true] => Ok(Some(column(tracks, ends, [true, true, true])));
    }
    with fn triple_count: Count = Count;
}

pub fn three_tracks() -> Result<Checks, Error> {
    const TRACK_BOUND: usize = 1; // Every choice of a gap or one token in each track.
    let words = words(b"ab", TRACK_BOUND);
    let all = &words;
    let triples = all.iter().flat_map(|a| {
        all.iter().flat_map(move |b| {
            all.iter()
                .map(move |c| [a.as_slice(), b.as_slice(), c.as_slice()])
        })
    });
    let mut checks = Checks::default();
    for tracks in triples.chain([[&b"ab"[..], &b"ab"[..], &b"ba"[..]], [b"ab", b"", b"b"]]) {
        let source = triple(tracks)?;
        let chart = compiled::reference_chart(&source)?;
        checks.chart(&chart);
        checks.compiled(&source, &chart, &Additive::default())?;
        let counts = tabulate_cells(&chart, &Count)?;
        checks.equal_values(triple_count(tracks)?.cells(), &counts);
        let scores = tabulate_cells(&chart, &Minimum)?;
        let [h, w, d] = tracks.map(|x| x.len() + 1);
        let rank = |i, j, k| (i * w + j) * d + k;
        let mut direct = vec![(0_i64, 1_u128); h * w * d];
        for i in 0..h {
            for j in 0..w {
                for k in 0..d {
                    let end = [i, j, k];
                    let cell = rank(i, j, k);
                    if cell > 0 {
                        let mut best = i64::MAX;
                        let mut count = 0;
                        for mask in 1..1 << TRACKS {
                            let shift: [usize; TRACKS] = std::array::from_fn(|t| mask >> t & 1);
                            if (0..TRACKS).any(|t| shift[t] > end[t]) {
                                continue;
                            }
                            let prior = [i - shift[0], j - shift[1], k - shift[2]];
                            let (score, paths) = direct[rank(prior[0], prior[1], prior[2])];
                            let mut extra = 0;
                            for a in 0..TRACKS {
                                for b in a + 1..TRACKS {
                                    let cost = match (shift[a], shift[b]) {
                                        (0, 0) => 0,
                                        (1, 1) => {
                                            i64::from(tracks[a][prior[a]] != tracks[b][prior[b]])
                                        }
                                        _ => 1,
                                    };
                                    extra += cost;
                                }
                            }
                            best = best.min(score + extra);
                            count += paths;
                        }
                        direct[cell] = (best, count);
                    }
                    assert_eq!(scores[cell], [Cost::Finite(direct[cell].0)]);
                    assert_eq!(counts[cell], [direct[cell].1]);
                }
            }
        }
        let mut distinct = std::collections::BTreeSet::new();
        for tree in enumerate(&chart) {
            let mut path = Vec::new();
            let mut node = &tree;
            while let Triple::Column(values) = node.operator {
                assert!(values.iter().any(Option::is_some));
                path.push(values);
                node = &node.children[0];
            }
            path.reverse();
            for (track, expected) in tracks.iter().enumerate() {
                assert!(path
                    .iter()
                    .filter_map(|column| column[track])
                    .eq(expected.iter().copied()));
            }
            assert!(distinct.insert(path));
        }
        assert_eq!(counts[chart.root()], [distinct.len() as u128]);
    }
    Ok(checks)
}

type EditKey = [u32; 3];
type Histogram = BTreeMap<EditKey, u128>;

struct EditFront;
impl Algebra<Align> for EditFront {
    type Value = Histogram;
    fn apply(&self, op: &Align, children: &[&Histogram]) -> Result<Histogram, Error> {
        let Some(child) = children.first() else {
            return Ok(BTreeMap::from([([0; 3], 1)]));
        };
        Ok(child
            .iter()
            .map(|(&[s, i, d], &count)| {
                let key = match *op {
                    Align::Left(_) => [s, i, d + 1],
                    Align::Right(_) => [s, i + 1, d],
                    Align::Diagonal { left, right } => [s + u32::from(left != right), i, d],
                    Align::Start => unreachable!(),
                };
                (key, count)
            })
            .collect())
    }
    fn choose(&self, bags: &[Histogram]) -> Result<Vec<Histogram>, Error> {
        let mut totals = Histogram::new();
        for bag in bags {
            for (&key, &n) in bag {
                *totals.entry(key).or_default() += n;
            }
        }
        let keys: Vec<_> = totals.keys().copied().collect();
        totals.retain(|key, _| {
            !keys
                .iter()
                .any(|other| other != key && (0..key.len()).all(|i| other[i] <= key[i]))
        });
        Ok((!totals.is_empty()).then_some(totals).into_iter().collect())
    }
}

pub fn trade_offs() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for (left, right) in pairs() {
        let chart = grammars::alignment(&left, &right)?;
        checks.chart(&chart);
        let table = tabulate_cells(&chart, &EditFront)?;
        let mut rank = 0;
        for i in 0..=left.len() {
            for j in 0..=right.len() {
                let mut raw = Histogram::new();
                let mut objectives = std::collections::BTreeSet::new();
                for path in raw_paths(&left[..i], &right[..j]) {
                    let mut key = [0; 3];
                    key[0] = path
                        .iter()
                        .filter(|c| matches!(c, Align::Diagonal { left, right } if left != right))
                        .count() as u32;
                    key[1] = path.iter().filter(|c| matches!(c, Align::Right(_))).count() as u32;
                    key[2] = path.iter().filter(|c| matches!(c, Align::Left(_))).count() as u32;
                    *raw.entry(key).or_default() += 1;
                    let substitutions = path
                        .iter()
                        .filter(
                            |step| matches!(step, Align::Diagonal { left, right } if left != right),
                        )
                        .count() as u32;
                    let gaps = path
                        .iter()
                        .filter(|step| matches!(step, Align::Left(_) | Align::Right(_)))
                        .count() as u32;
                    objectives.insert((substitutions, gaps));
                }
                let all: Vec<_> = raw.keys().copied().collect();
                let expected: Histogram = raw
                    .into_iter()
                    .filter(|([s, i, d], _)| {
                        !all.iter().any(|&[a, b, c]| {
                            a <= *s && b <= *i && c <= *d && [a, b, c] != [*s, *i, *d]
                        })
                    })
                    .collect();
                assert_eq!(table[rank], [expected]);
                let project = |key: &EditKey| (key[0], key[1] + key[2]);
                assert_eq!(table[rank].len(), 1);
                let front: Vec<_> = table[rank][0].keys().map(project).collect();
                let projected: std::collections::BTreeSet<_> =
                    pareto_min(&front)?.into_iter().collect();
                if i == 1 && j == 1 && left[0] != right[0] {
                    // One substitution or two gap columns.
                    assert_eq!(
                        projected,
                        std::collections::BTreeSet::from([(0, 2), (1, 0)]),
                        "single-token edit trade-offs"
                    );
                }
                let direct = objectives
                    .iter()
                    .copied()
                    .filter(|&(s, g)| {
                        !objectives
                            .iter()
                            .any(|&(a, b)| a <= s && b <= g && (a, b) != (s, g))
                    })
                    .collect();
                assert_eq!(projected, direct, "projected edit objectives");
                rank += 1;
            }
        }
    }
    Ok(checks)
}
