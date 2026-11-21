//! Export validated ranked charts and Rust reference answers to a Lean runner.

use std::collections::BTreeMap;
use std::io::{self, BufWriter, Write};

use zeno_adp::algebras::{
    lexicographic_min, Additive, Cost, CostPolicy, Count, Enumerate, MinimumWithMultiplicity,
    Product, ScoredOperator,
};
use zeno_adp::{grammars, tabulate_cells, Algebra, Chart, Error, Operator, Rule, Tree};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Op {
    id: usize,
    arity: usize,
    cost: Cost,
}

impl Operator for Op {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl ScoredOperator for Op {
    fn cost(&self) -> Cost {
        self.cost
    }
}

impl Op {
    fn secondary(self) -> i64 {
        // A signed second objective with a three-point range so ties and
        // opposite preferences occur on the short domain.
        const WEIGHTS: [i64; 3] = [-1, 0, 1];
        WEIGHTS[self.id % WEIGHTS.len()]
    }
}

struct Secondary;

impl Algebra<Op> for Secondary {
    type Value = i64;

    fn apply(&self, op: &Op, args: &[&i64]) -> Result<i64, Error> {
        args.iter().try_fold(op.secondary(), |sum, &&value| {
            sum.checked_add(value).ok_or(Error::Overflow)
        })
    }

    fn choose(&self, candidates: &[i64]) -> Result<Vec<i64>, Error> {
        Ok(candidates.iter().min().copied().into_iter().collect())
    }
}

fn score(cost: Cost) -> String {
    match cost {
        Cost::Finite(n) => n.to_string(),
        Cost::Infinity => "null".into(),
    }
}

fn bag<T>(
    out: &mut impl Write,
    xs: &[T],
    mut item: impl FnMut(&mut dyn Write, &T) -> io::Result<()>,
) -> io::Result<()> {
    write!(out, "[")?;
    for (i, x) in xs.iter().enumerate() {
        if i != 0 {
            write!(out, ",")?;
        }
        item(out, x)?;
    }
    write!(out, "]")
}

fn tree(out: &mut dyn Write, t: &Tree<Op>) -> io::Result<()> {
    write!(out, "[{},", t.operator.id)?;
    bag(&mut &mut *out, &t.children, tree)?;
    write!(out, "]")
}

fn encode_chart<O: Operator + Ord + ScoredOperator>(chart: &Chart<O>) -> Chart<Op> {
    let mut ids = BTreeMap::new();
    let cells = chart
        .cells()
        .iter()
        .map(|rules| {
            rules
                .iter()
                .map(|rule| {
                    let next_id = ids.len();
                    let op = &rule.operator;
                    let id = *ids.entry(op).or_insert(next_id);
                    Rule::new(
                        Op {
                            id,
                            arity: op.arity(),
                            cost: op.cost(),
                        },
                        rule.children.clone(),
                    )
                })
                .collect()
        })
        .collect();
    Chart::new(cells, chart.root()).unwrap()
}

fn export<O: Operator + Ord + ScoredOperator>(
    input: &mut impl Write,
    report: &mut impl Write,
    group: &str,
    original: &Chart<O>,
    dimensions: Option<&[u32]>,
) -> io::Result<()> {
    let chart = encode_chart(original);
    let counts = tabulate_cells(original, &Count).unwrap();
    let terms = tabulate_cells(&chart, &Enumerate).unwrap();
    let policy = CostPolicy::AttainableInfinity;
    let ties = tabulate_cells(original, &MinimumWithMultiplicity::new(policy)).unwrap();
    let minimum = tabulate_cells(original, &Additive::new(policy)).unwrap();
    let finite = Chart::new(
        chart
            .cells()
            .iter()
            .map(|rules| {
                rules
                    .iter()
                    .filter(|rule| matches!(rule.operator.cost, Cost::Finite(_)))
                    .cloned()
                    .collect()
            })
            .collect(),
        chart.root(),
    )
    .unwrap();
    let lex = tabulate_cells(
        &finite,
        &Product::new(Additive::default(), Secondary, lexicographic_min),
    )
    .unwrap();

    write!(
        input,
        "{{\"group\":\"{group}\",\"root\":{},\"dimensions\":",
        chart.root()
    )?;
    match dimensions {
        Some(d) => write!(input, "{d:?}")?,
        None => write!(input, "null")?,
    }
    write!(input, ",\"cells\":")?;
    bag(input, chart.cells(), |out, rules| {
        bag(&mut &mut *out, rules, |out, rule| {
            let Op { id, arity, cost } = rule.operator;
            write!(
                out,
                "{{\"id\":{id},\"arity\":{arity},\"cost\":{},\"secondary\":{},\"children\":{:?}}}",
                score(cost),
                rule.operator.secondary(),
                rule.children
            )
        })
    })?;
    writeln!(input, "}}")?;

    write!(report, "[\"{group}\",{},[", chart.root())?;
    for cell in 0..chart.cells().len() {
        if cell != 0 {
            write!(report, ",")?;
        }
        write!(report, "[{:?},", counts[cell])?;
        bag(report, &terms[cell], tree)?;
        write!(report, ",")?;
        bag(report, &ties[cell], |out, s| {
            write!(
                out,
                "[{},{},{}]",
                score(s.cost),
                s.optimal_derivations,
                s.total_derivations
            )
        })?;
        write!(report, ",")?;
        bag(report, &minimum[cell], |out, &c| {
            write!(out, "{}", score(c))
        })?;
        write!(report, ",")?;
        bag(report, &lex[cell], |out, &(p, s)| {
            write!(out, "[{},{s}]", score(p))
        })?;
        write!(report, "]")?;
    }
    writeln!(report, "]]")
}

fn words(alphabet: [u8; 2], max: usize) -> Vec<Vec<u8>> {
    (0..=max)
        .flat_map(|n| {
            (0..1usize << n).map(move |bits| (0..n).map(|i| alphabet[(bits >> i) & 1]).collect())
        })
        .collect()
}

// Registered on the inherited domains to exercise empty states, splits and
// many ordered alternatives while keeping full tree bags small.
const NUSSINOV_LENGTH: usize = 6;
const GLOBAL_LENGTH: usize = 4;
const LOCAL_LENGTH: usize = 3;
const MAX_DIMENSIONS: usize = 6;
const MAX_ITEMS: usize = 4;
const MAX_CAPACITY: usize = 4;

fn visit_domains(mut input: impl Write, mut report: impl Write) -> io::Result<()> {
    for sequence in words(*b"AU", NUSSINOV_LENGTH) {
        export(
            &mut input,
            &mut report,
            "nussinov",
            &grammars::nussinov(&sequence, 0).unwrap(),
            None,
        )?;
    }
    for left in words(*b"AC", GLOBAL_LENGTH) {
        for right in words(*b"AC", GLOBAL_LENGTH) {
            export(
                &mut input,
                &mut report,
                "alignment",
                &grammars::alignment(&left, &right).unwrap(),
                None,
            )?;
        }
    }
    for left in words(*b"AC", LOCAL_LENGTH) {
        for right in words(*b"AC", LOCAL_LENGTH) {
            export(
                &mut input,
                &mut report,
                "local",
                &grammars::local_alignment(&left, &right).unwrap(),
                None,
            )?;
        }
    }
    for n in 2..=MAX_DIMENSIONS {
        for dimensions in words([2, 3], n).into_iter().filter(|dims| dims.len() == n) {
            let dims: Vec<_> = dimensions.into_iter().map(u32::from).collect();
            export(
                &mut input,
                &mut report,
                "matrix",
                &grammars::matrix_chain(&dims).unwrap(),
                Some(&dims),
            )?;
        }
    }
    for items in words([0, 1], MAX_ITEMS) {
        let items: Vec<_> = items
            .into_iter()
            .map(|item| match item {
                0 => grammars::Item {
                    weight: 1,
                    value: 1,
                },
                _ => grammars::Item {
                    weight: 2,
                    value: 3,
                },
            })
            .collect();
        for capacity in 0..=MAX_CAPACITY {
            export(
                &mut input,
                &mut report,
                "knapsack",
                &grammars::knapsack(&items, capacity).unwrap(),
                None,
            )?;
        }
    }

    use Cost::{Finite, Infinity};
    let leaf_domain = [
        None,
        Some(Finite(-1)),
        Some(Finite(0)),
        Some(Finite(1)),
        Some(Infinity),
    ];
    let middle_domain = [None, Some(Finite(0)), Some(Infinity)];
    let branch_domain = [Finite(0), Infinity];
    let rule = |id, cost, children: &[usize]| {
        Rule::new(
            Op {
                id,
                arity: children.len(),
                cost,
            },
            children,
        )
    };
    for first in leaf_domain {
        for second in leaf_domain {
            for middle in middle_domain {
                for binary in branch_domain {
                    for ternary in branch_domain {
                        let leaves = [first, second]
                            .into_iter()
                            .flatten()
                            .map(|c| rule(0, c, &[]))
                            .collect();
                        let middle = middle.into_iter().map(|c| rule(1, c, &[])).collect();
                        let tree = vec![
                            leaves,
                            middle,
                            vec![
                                rule(2, Finite(0), &[]),
                                rule(3, binary, &[0, 1]),
                                rule(4, ternary, &[0, 1, 0]),
                            ],
                            vec![],
                        ];
                        export(
                            &mut input,
                            &mut report,
                            "ranked",
                            &Chart::new(tree, 2).unwrap(),
                            None,
                        )?;
                    }
                }
            }
        }
    }
    input.flush()?;
    report.flush()
}

fn main() -> io::Result<()> {
    let mut args = std::env::args_os().skip(1);
    let input = std::fs::File::create(args.next().expect("chart output filename"))?;
    let report = std::fs::File::create(args.next().expect("reference output filename"))?;
    assert!(args.next().is_none());
    visit_domains(BufWriter::new(input), BufWriter::new(report))
}
