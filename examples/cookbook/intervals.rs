use super::{words, Checks};
use zeno_adp::algebras::{pareto_min, Additive, Cost, Count, Minimum};
use zeno_adp::compiled;
use zeno_adp::{enumerate, tabulate_cells, Algebra, Chart, Error, Operator, Rule, Tree};

#[path = "../support/optimal_bst.rs"]
#[allow(dead_code)]
mod bst;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Token {
    Digit(i64),
    Add,
    Sub,
    Mul,
}

impl Operator for Token {
    fn arity(&self) -> usize {
        if matches!(self, Self::Digit(_)) {
            0
        } else {
            2
        }
    }
}

fn arithmetic_value(token: Token, a: i64, b: i64) -> i64 {
    match token {
        Token::Digit(value) => value,
        Token::Add => a + b,
        Token::Sub => a - b,
        Token::Mul => a * b,
    }
}

struct Extrema;

impl Algebra<Token> for Extrema {
    type Value = (i64, i64);
    fn apply(&self, op: &Token, values: &[&Self::Value]) -> Result<Self::Value, Error> {
        let Token::Digit(_) = op else {
            let [(a, b), (c, d)] = [*values[0], *values[1]];
            let corners =
                [(a, c), (a, d), (b, c), (b, d)].map(|(l, r)| arithmetic_value(*op, l, r));
            return Ok((
                *corners.iter().min().unwrap(),
                *corners.iter().max().unwrap(),
            ));
        };
        let value = arithmetic_value(*op, 0, 0);
        Ok((value, value))
    }
    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
        Ok(candidates
            .iter()
            .copied()
            .reduce(|a, b| (a.0.min(b.0), a.1.max(b.1)))
            .into_iter()
            .collect())
    }
}

fn eval(tree: &Tree<Token>) -> i64 {
    match tree.children.as_slice() {
        [] => arithmetic_value(tree.operator, 0, 0),
        [a, b] => arithmetic_value(tree.operator, eval(a), eval(b)),
        _ => unreachable!(),
    }
}

fn raw_brackets(digits: &[i64], ops: &[Token]) -> Vec<i64> {
    if let [value] = digits {
        return vec![*value];
    }
    let mut results = Vec::new();
    for split in 1..digits.len() {
        for a in raw_brackets(&digits[..split], &ops[..split - 1]) {
            for b in raw_brackets(&digits[split..], &ops[split..]) {
                let value = match ops[split - 1] {
                    Token::Add => a + b,
                    Token::Sub => a - b,
                    Token::Mul => a * b,
                    Token::Digit(_) => unreachable!(),
                };
                results.push(value);
            }
        }
    }
    results
}

pub fn arithmetic() -> Result<Checks, Error> {
    use compiled::{TokenAtom, TokenGrammar, TokenProduction};
    const MAX_OPERANDS: usize = 4; // Three internal nodes exercise competing splits.
    let grammar = TokenGrammar::new(
        &["expression"],
        0,
        vec![
            TokenProduction {
                name: "digit".into(),
                parent: 0,
                children: vec![],
                tracks: [vec![TokenAtom::Predicate(Box::new(|t| {
                    matches!(t, Token::Digit(_))
                }))]],
                operator: Box::new(|m| m.inputs[0][m.parent[0].start]),
            },
            TokenProduction {
                name: "binary".into(),
                parent: 0,
                children: vec![0, 0],
                tracks: [vec![
                    TokenAtom::Child(0),
                    TokenAtom::Predicate(Box::new(|t| !matches!(t, Token::Digit(_)))),
                    TokenAtom::Child(1),
                ]],
                operator: Box::new(|m| m.inputs[0][m.children[0][0].end]),
            },
        ],
    )?;
    let mut checks = Checks::default();
    let operators = words(&[Token::Add, Token::Sub, Token::Mul], MAX_OPERANDS - 1);
    for digits in words(&[1, 2], MAX_OPERANDS)
        .into_iter()
        .filter(|d| !d.is_empty())
    {
        for ops in operators.iter().filter(|ops| ops.len() + 1 == digits.len()) {
            let mut input = vec![Token::Digit(digits[0])];
            for (&op, &digit) in ops.iter().zip(&digits[1..]) {
                input.extend([op, Token::Digit(digit)]);
            }
            let bound = grammar.bind([&input])?;
            let reference = compiled::reference_chart(&bound)?;
            checks.chart(&reference);
            checks.compiled(&bound, &reference, &Count)?;
            let extrema = tabulate_cells(&reference, &Extrema)?;
            let counts = tabulate_cells(&reference, &Count)?;
            for rank in 0..reference.cells().len() {
                let (_, [span]) = bound.cell(rank).unwrap();
                if span.is_empty() || span.start % 2 == 1 || span.end % 2 == 0 {
                    assert!(extrema[rank].is_empty() && counts[rank].is_empty());
                } else {
                    let a = span.start / 2;
                    let b = span.end / 2;
                    let values = raw_brackets(&digits[a..=b], &ops[a..b]);
                    assert_eq!(
                        extrema[rank],
                        [(*values.iter().min().unwrap(), *values.iter().max().unwrap())]
                    );
                    assert_eq!(counts[rank], [values.len() as u128]);
                }
            }
            let oracle = raw_brackets(&digits, ops);
            assert!(enumerate(&reference).iter().map(eval).eq(oracle));
        }
    }
    Ok(checks)
}

fn raw_matrix_cost(dims: &[u32]) -> i64 {
    if dims.len() == 2 {
        return 0;
    }
    (1..dims.len() - 1)
        .map(|k| {
            raw_matrix_cost(&dims[..=k])
                + raw_matrix_cost(&dims[k..])
                + i64::from(dims[0]) * i64::from(dims[k]) * i64::from(dims[dims.len() - 1])
        })
        .min()
        .unwrap()
}

fn score_matrix_tree(
    tree: &Tree<zeno_adp::grammars::MatrixChain>,
    dims: &[u32],
) -> (usize, usize, i64) {
    match tree.operator {
        zeno_adp::grammars::MatrixChain::Matrix { at } => (at, at + 1, 0),
        zeno_adp::grammars::MatrixChain::Multiply { .. } => {
            let (a, k, left) = score_matrix_tree(&tree.children[0], dims);
            let (split, b, right) = score_matrix_tree(&tree.children[1], dims);
            assert_eq!(k, split);
            (
                a,
                b,
                left + right + i64::from(dims[a]) * i64::from(dims[k]) * i64::from(dims[b]),
            )
        }
    }
}

const DIMENSION_BOUND: usize = 5; // Four matrices allow both balanced and skewed trees.
fn dimensions() -> impl Iterator<Item = Vec<u32>> {
    words(&[2, 3], DIMENSION_BOUND)
        .into_iter()
        .filter(|v| v.len() >= 2)
}

pub fn matrix_chain() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for dims in dimensions() {
        let source = zeno_adp::grammars::matrix_chain_source(&dims)?;
        let chart = zeno_adp::grammars::matrix_chain(&dims)?;
        checks.chart(&chart);
        let table = compiled::best(&source)?;
        let reference = tabulate_cells(&chart, &Minimum)?;
        checks.equal_values(table.scores().cells(), &reference);
        let fast = zeno_adp::fast::matrix_chain(&dims)?;
        let reference_finite: Vec<_> = reference
            .iter()
            .map(|bag| match bag.as_slice() {
                [Cost::Finite(x)] => vec![*x],
                _ => unreachable!(),
            })
            .collect();
        checks.equal_values(fast.cells(), &reference_finite);
        let mut rank = 0;
        for len in 1..dims.len() {
            for start in 0..dims.len() - len {
                assert_eq!(
                    reference[rank],
                    [Cost::Finite(raw_matrix_cost(&dims[start..=start + len]))]
                );
                rank += 1;
            }
        }
        let winner = table.recover().first_minimum_tree()?.unwrap();
        assert_eq!(
            score_matrix_tree(&winner.tree, &dims),
            (0, dims.len() - 1, raw_matrix_cost(&dims))
        );
    }
    Ok(checks)
}

type Objective = (i64, i64);

struct MemoryWork<'a>(&'a [u32]);

impl Algebra<zeno_adp::grammars::MatrixChain> for MemoryWork<'_> {
    type Value = Objective;
    fn apply(
        &self,
        op: &zeno_adp::grammars::MatrixChain,
        children: &[&Objective],
    ) -> Result<Objective, Error> {
        let size = |a: usize, b: usize| i64::from(self.0[a]) * i64::from(self.0[b]);
        Ok(match *op {
            zeno_adp::grammars::MatrixChain::Matrix { at } => (0, size(at, at + 1)),
            zeno_adp::grammars::MatrixChain::Multiply {
                left,
                split,
                right,
                cost,
            } => {
                let (a, b) = (size(left, split), size(split, right));
                let live = a + b + size(left, right);
                let (l, r) = (*children[0], *children[1]);
                let left_first = l.1.max(a + r.1).max(live);
                let right_first = r.1.max(b + l.1).max(live);
                (cost + l.0 + r.0, left_first.min(right_first))
            }
        })
    }
    fn choose(&self, candidates: &[Objective]) -> Result<Vec<Objective>, Error> {
        pareto_min(candidates)
    }
}

// Enumerate allocation/release traces. The output of each subtree stays
// live until the parent allocates its own result.
fn traces(dims: &[u32]) -> Vec<(i64, Vec<i64>)> {
    let end = dims.len() - 1;
    let output = i64::from(dims[0]) * i64::from(dims[end]);
    if end == 1 {
        return vec![(0, vec![output])];
    }
    let mut result = Vec::new();
    for k in 1..end {
        let left = traces(&dims[..=k]);
        let right = traces(&dims[k..]);
        for (work_l, events_l) in &left {
            for (work_r, events_r) in &right {
                let work = work_l + work_r + output * i64::from(dims[k]);
                let release = -events_l.iter().chain(events_r).sum::<i64>();
                for (first, second) in [(events_l, events_r), (events_r, events_l)] {
                    result.push((
                        work,
                        first
                            .iter()
                            .chain(second)
                            .copied()
                            .chain([output, release])
                            .collect(),
                    ));
                }
            }
        }
    }
    result
}

struct LowestLocalPeak<'a>(MemoryWork<'a>);

impl Algebra<zeno_adp::grammars::MatrixChain> for LowestLocalPeak<'_> {
    type Value = Objective;
    fn apply(
        &self,
        op: &zeno_adp::grammars::MatrixChain,
        children: &[&Objective],
    ) -> Result<Objective, Error> {
        self.0.apply(op, children)
    }
    fn choose(&self, candidates: &[Objective]) -> Result<Vec<Objective>, Error> {
        Ok(candidates
            .iter()
            .copied()
            .min_by_key(|&(work, peak)| (peak, work))
            .into_iter()
            .collect())
    }
}

pub fn matrix_frontier() -> Result<Checks, Error> {
    let mut checks = Checks::default();
    const SINGLE_WINNER_CONTROL: &[u32] = &[27, 11, 27, 13, 8, 23];
    for dims in dimensions().chain([SINGLE_WINNER_CONTROL.to_vec()]) {
        let chart = zeno_adp::grammars::matrix_chain(&dims)?;
        checks.chart(&chart);
        let table = tabulate_cells(&chart, &MemoryWork(&dims))?;
        let mut rank = 0;
        for len in 1..dims.len() {
            for a in 0..dims.len() - len {
                let mut outcomes: Vec<_> = traces(&dims[a..=a + len])
                    .into_iter()
                    .map(|(work, events)| {
                        let mut live = 0;
                        let peak = events
                            .into_iter()
                            .map(|delta| {
                                live += delta;
                                live
                            })
                            .max()
                            .unwrap();
                        (work, peak)
                    })
                    .collect();
                outcomes.sort_unstable();
                outcomes.dedup();
                let front: Vec<_> = outcomes
                    .iter()
                    .copied()
                    .filter(|&x| !outcomes.iter().any(|&y| y != x && y.0 <= x.0 && y.1 <= x.1))
                    .collect();
                assert_eq!(table[rank], front);
                rank += 1;
            }
        }
        if dims == SINGLE_WINNER_CONTROL {
            let singleton = tabulate_cells(&chart, &LowestLocalPeak(MemoryWork(&dims)))?;
            assert_eq!(singleton[chart.root()], [(12528, 1021)]);
            assert!(table[chart.root()].contains(&(12349, 1021)));
        }
    }
    Ok(checks)
}

fn bst_cost(raw: &[u32]) -> i64 {
    let mass = raw.iter().map(|&x| i64::from(x)).sum::<i64>();
    (0..raw.len())
        .map(|k| mass + bst_cost(&raw[..k]) + bst_cost(&raw[k + 1..]))
        .min()
        .unwrap_or(0)
}

fn visit_keys(tree: &Tree<bst::SearchTree>, depth: u32, raw: &[u32], keys: &mut Vec<usize>) -> i64 {
    match tree.operator {
        bst::SearchTree::Empty => 0,
        bst::SearchTree::Key { index, .. } => {
            let left = visit_keys(&tree.children[0], depth + 1, raw, keys);
            keys.push(index);
            left + i64::from(depth) * i64::from(raw[index])
                + visit_keys(&tree.children[1], depth + 1, raw, keys)
        }
    }
}

pub fn search_tree() -> Result<Checks, Error> {
    const MAX_KEYS: usize = 4; // Includes trees with two nonempty branches.
    let mut checks = Checks::default();
    for raw in words(&[0, 1], MAX_KEYS) {
        let input = bst::prepare(&raw)?;
        let source = bst::grammar(&input)?;
        let chart = compiled::reference_chart(&source)?;
        checks.chart(&chart);
        checks.compiled(&source, &chart, &Additive::default())?;
        let reference = tabulate_cells(&chart, &Minimum)?;
        checks.equal_values(bst::minimum(&input)?.cells(), &reference);
        let mut rank = 0;
        for b in 0..=raw.len() {
            for a in (0..=b).rev() {
                assert_eq!(reference[rank], [Cost::Finite(bst_cost(&raw[a..b]))]);
                rank += 1;
            }
        }
        let best = compiled::best(&source)?;
        let tree = best.recover().first_minimum_tree()?.unwrap();
        let mut keys = Vec::new();
        assert_eq!(visit_keys(&tree.tree, 1, &raw, &mut keys), bst_cost(&raw));
        assert!(keys.into_iter().eq(0..raw.len()));
    }
    Ok(checks)
}

#[derive(Clone, Copy)]
enum Wings {
    Center(usize, usize),
    Enclose,
    Select(usize, usize),
}

impl Operator for Wings {
    fn arity(&self) -> usize {
        usize::from(!matches!(self, Self::Center(..)))
    }
}

impl zeno_adp::algebras::ScoredOperator for Wings {
    fn cost(&self) -> Cost {
        Cost::Finite(self.arity() as i64)
    }
}

fn read_wings(tree: &Tree<Wings>) -> (usize, usize, usize, usize, i64) {
    let Wings::Select(start, end) = tree.operator else {
        unreachable!()
    };
    let mut child = &tree.children[0];
    let mut pairs = 1;
    while matches!(child.operator, Wings::Enclose) {
        child = &child.children[0];
        pairs += 1;
    }
    let Wings::Center(a, b) = child.operator else {
        unreachable!()
    };
    (start, a, b, end, pairs)
}

pub fn palindrome() -> Result<Checks, Error> {
    use zeno_adp::algebras::Maximum;
    const MAX_LEN: usize = 5; // Two pairs can surround a nonempty center.
    let mut checks = Checks::default();
    for word in words(b"ab", MAX_LEN) {
        let side = word.len() + 1;
        let rank = |a, b| b * side + side - 1 - a;
        let mut rows = vec![Vec::new(); side * side + 1];
        let root = rows.len() - 1;
        for b in 0..side {
            for a in 0..b {
                rows[rank(a, b)].push(Rule::new(Wings::Center(a, b), []));
                if b - a >= 3 && word[a] == word[b - 1] {
                    rows[rank(a, b)].push(Rule::new(Wings::Enclose, [rank(a + 1, b - 1)]));
                    rows[root].push(Rule::new(Wings::Select(a, b), [rank(a + 1, b - 1)]));
                }
            }
        }
        let chart = Chart::new(rows, root)?;
        checks.chart(&chart);
        let table = tabulate_cells(&chart, &Maximum)?;
        let mut best = None;
        let mut direct = Vec::new();
        // Start from the center and extend outwards, the opposite direction
        // from the grammar's outermost-pair decomposition.
        let mut pairs = vec![None; side * side];
        for a in 0..word.len() {
            for b in a + 1..side {
                let slot = &mut pairs[rank(a, b)];
                *slot = (*slot).max(Some(0));
                let mut n = 0;
                while a > n && b + n < word.len() && word[a - n - 1] == word[b + n] {
                    n += 1;
                    let count = n as i64;
                    let slot = &mut pairs[rank(a - n, b + n)];
                    *slot = (*slot).max(Some(count));
                    best = best.max(Some(count));
                    direct.push((a - n, a, b, b + n, count));
                }
            }
        }
        for (bag, score) in table[..root].iter().zip(pairs) {
            assert!(bag.iter().copied().eq(score.map(Cost::Finite)));
        }
        assert!(table[root].iter().copied().eq(best.map(Cost::Finite)));
        direct.retain(|entry| Some(entry.4) == best);
        let mut found: Vec<_> = enumerate(&chart)
            .iter()
            .map(read_wings)
            .filter(|entry| Some(entry.4) == best)
            .collect();
        found.sort_unstable();
        direct.sort_unstable();
        assert_eq!(found, direct);
    }
    Ok(checks)
}
