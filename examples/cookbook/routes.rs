use super::Checks;
use zeno_adp::algebras::{Cost, Minimum, ScoredOperator};
use zeno_adp::probability::{inside_outside, Rational, WeightedOperator};
use zeno_adp::{tabulate_cells, Chart, Error, Operator, Rule};

type Graph = Vec<Vec<Option<i64>>>;
const ANCHOR: usize = 0;

#[derive(Clone, Copy)]
enum Leg {
    Begin(usize),
    Edge { from: usize, to: usize, cost: i64 },
    Finish(usize),
}

impl Operator for Leg {
    fn arity(&self) -> usize {
        usize::from(!matches!(self, Self::Begin(_)))
    }
}

impl ScoredOperator for Leg {
    fn cost(&self) -> Cost {
        Cost::Finite(match *self {
            Self::Edge { cost, .. } => cost,
            _ => 0,
        })
    }
}

impl WeightedOperator for Leg {
    fn weight(&self) -> Rational {
        match *self {
            Self::Edge { cost, .. } => Rational::new(1, (cost + 1) as u128).unwrap(),
            _ => Rational::ONE,
        }
    }
}

fn graph_chart(graph: &Graph, anchored: bool) -> Result<Chart<Leg>, Error> {
    let n = graph.len();
    let all = (1 << n) - 1;
    let cell = |set, last| set * n + last;
    let root = (all + 1) * n;
    let mut rows = vec![Vec::new(); root + 1];
    for set in 1..=all {
        for last in 0..n {
            let bit = 1 << last;
            if set & bit == 0 {
                continue;
            }
            let rank = cell(set, last);
            if set == bit && (!anchored || last == ANCHOR) {
                rows[rank].push(Rule::new(Leg::Begin(last), []));
            }
            for (prior, edges) in graph.iter().enumerate() {
                if prior != last && set & (1 << prior) != 0 {
                    if let Some(cost) = edges[last] {
                        rows[rank].push(Rule::new(
                            Leg::Edge {
                                from: prior,
                                to: last,
                                cost,
                            },
                            [cell(set ^ bit, prior)],
                        ));
                    }
                }
            }
        }
    }
    for (last, edges) in graph.iter().enumerate() {
        let child = [cell(all, last)];
        if !anchored || n == 1 {
            rows[root].push(Rule::new(Leg::Finish(last), child));
        } else if let Some(cost) = edges[ANCHOR] {
            rows[root].push(Rule::new(
                Leg::Edge {
                    from: last,
                    to: ANCHOR,
                    cost,
                },
                child,
            ));
        }
    }
    Chart::new(rows, root)
}

fn held_karp(graph: &Graph, anchored: bool) -> Vec<Option<i64>> {
    let n = graph.len();
    let mut best = vec![None; (1 << n) * n];
    for start in 0..n {
        if !anchored || start == ANCHOR {
            best[(1 << start) * n + start] = Some(0);
        }
    }
    // Extend a known prefix by a currently unvisited vertex.
    for visited in 1..1 << n {
        for from in 0..n {
            if let Some(prefix) = best[visited * n + from] {
                for (to, edge) in graph[from].iter().enumerate() {
                    if visited & (1 << to) == 0 {
                        if let Some(cost) = edge {
                            let rank = (visited | 1 << to) * n + to;
                            let candidate = prefix + cost;
                            best[rank] = Some(
                                best[rank].map_or(candidate, |previous| previous.min(candidate)),
                            );
                        }
                    }
                }
            }
        }
    }
    let full = &best[best.len() - n..];
    let score = full
        .iter()
        .enumerate()
        .filter_map(|(last, prefix)| {
            let cost = (*prefix)?;
            if anchored && n > 1 {
                Some(cost + graph[last][ANCHOR]?)
            } else {
                Some(cost)
            }
        })
        .min();
    best.push(score);
    best
}

fn permutations(n: usize, prefix: &mut Vec<usize>, emit: &mut impl FnMut(&[usize])) {
    if prefix.len() == n {
        emit(prefix);
        return;
    }
    for i in 0..n {
        if prefix.contains(&i) {
            continue;
        }
        prefix.push(i);
        permutations(n, prefix, emit);
        prefix.pop();
    }
}

fn graphs() -> impl Iterator<Item = Graph> {
    const VERTICES: usize = 3; // Both orientations and an interior vertex.
    let edges: Vec<_> = (0..VERTICES)
        .flat_map(|from| {
            (0..VERTICES)
                .filter(move |&to| from != to)
                .map(move |to| (from, to))
        })
        .collect();
    (0..1 << edges.len()).map(move |mask| {
        let mut graph = vec![vec![None; VERTICES]; VERTICES];
        for (index, &(from, to)) in edges.iter().enumerate() {
            if mask & (1 << index) != 0 {
                graph[from][to] = Some((index + 1) as i64);
            }
        }
        graph
    })
}
fn direct_paths(
    graph: &Graph,
    anchored: bool,
) -> impl Iterator<Item = (Vec<usize>, Vec<i64>)> + '_ {
    let mut paths = Vec::new();
    permutations(graph.len(), &mut Vec::new(), &mut |path| {
        if !anchored || path[0] == ANCHOR {
            let mut closed = path.to_vec();
            if anchored && graph.len() > 1 {
                closed.push(ANCHOR);
            }
            if let Some(edges) = closed.windows(2).map(|w| graph[w[0]][w[1]]).collect() {
                paths.push((closed, edges));
            }
        }
    });
    paths.into_iter()
}

fn check_routes(anchored: bool) -> Result<Checks, Error> {
    let mut checks = Checks::default();
    for graph in graphs().chain([vec![vec![None]]]) {
        let chart = graph_chart(&graph, anchored)?;
        checks.chart(&chart);
        let scores = tabulate_cells(&chart, &Minimum)?;
        let direct = held_karp(&graph, anchored);
        for (bag, cost) in scores.iter().zip(&direct) {
            assert!(bag.iter().copied().eq(cost.map(Cost::Finite)));
        }
        let paths: Vec<_> = direct_paths(&graph, anchored).collect();
        let best = paths
            .iter()
            .map(|(_, costs)| costs.iter().sum::<i64>())
            .min();
        assert_eq!(direct[chart.root()], best);
        if anchored {
            continue;
        }
        let n = graph.len();
        let mut occurrences = vec![vec![Rational::ZERO; n]; n];
        let mut starts = vec![Rational::ZERO; n];
        let mut ends = vec![Rational::ZERO; n];
        let mut partition = Rational::ZERO;
        for (path, costs) in paths {
            let mass = costs.iter().try_fold(Rational::ONE, |m, &c| {
                m.checked_mul(Rational::new(1, (c + 1) as u128).unwrap())
            })?;
            partition = partition.checked_add(mass)?;
            for pair in path.windows(2) {
                let value = &mut occurrences[pair[0]][pair[1]];
                *value = value.checked_add(mass)?;
            }
            starts[path[0]] = starts[path[0]].checked_add(mass)?;
            let last = *path.last().unwrap();
            ends[last] = ends[last].checked_add(mass)?;
        }
        let weights = inside_outside(&chart)?;
        assert_eq!(*weights.partition(), partition);
        let mut edge_mass = vec![vec![Rational::ZERO; n]; n];
        for (cell, rules) in chart.cells().iter().enumerate() {
            for rule in rules {
                let child = rule
                    .children
                    .first()
                    .map_or(Rational::ONE, |&x| weights.inside()[x]);
                let mass = weights.outside()[cell]
                    .checked_mul(rule.operator.weight())?
                    .checked_mul(child)?;
                match rule.operator {
                    Leg::Begin(v) => assert_eq!(mass, starts[v]),
                    Leg::Finish(v) => assert_eq!(mass, ends[v]),
                    Leg::Edge { from, to, .. } => {
                        edge_mass[from][to] = edge_mass[from][to].checked_add(mass)?;
                    }
                }
            }
        }
        assert_eq!(edge_mass, occurrences);
        if partition != Rational::ZERO {
            // A full path uses exactly n - 1 directed edges.
            let total = occurrences
                .into_iter()
                .flatten()
                .try_fold(Rational::ZERO, Rational::checked_add)?;
            assert_eq!(
                total.checked_div(partition)?,
                Rational::new((n - 1) as u128, 1)
            );
        }
    }
    Ok(checks)
}

pub fn hamiltonian() -> Result<Checks, Error> {
    check_routes(false)
}
pub fn tour() -> Result<Checks, Error> {
    check_routes(true)
}
