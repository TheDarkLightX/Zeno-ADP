//! Run the 22 recipes with `cargo run --example cookbook`.

#[path = "cookbook/alignment.rs"]
mod alignment;
#[path = "cookbook/forests.rs"]
mod forests;
#[path = "cookbook/intervals.rs"]
mod intervals;
#[path = "cookbook/languages.rs"]
mod languages;
#[path = "cookbook/routes.rs"]
mod routes;
#[path = "cookbook/structures.rs"]
mod structures;
#[path = "cookbook/weighted.rs"]
mod weighted;

use zeno_adp::algebras::{Cost, ScoredOperator};
use zeno_adp::compiled::{self, Program};
use zeno_adp::fast::Fold;
use zeno_adp::{tabulate_cells, Algebra, Chart, Error, Operator, Rule};

#[derive(Default)]
struct Checks {
    inputs: usize,
    ranks: usize,
    fast_values: usize,
}

impl Checks {
    fn chart<O>(&mut self, chart: &Chart<O>) {
        self.inputs += 1;
        self.ranks += chart.cells().len();
    }

    fn compiled<G, A, V>(
        &mut self,
        program: &G,
        chart: &Chart<G::Op>,
        algebra: &A,
    ) -> Result<(), Error>
    where
        G: Program,
        A: Algebra<G::Op, Value = V> + Fold<G::Op, Value = V>,
        V: Clone + Eq + std::fmt::Debug,
    {
        let expected = tabulate_cells(chart, algebra)?;
        let got = compiled::tabulate(program, algebra)?;
        self.equal_values(got.cells(), &expected);
        Ok(())
    }

    fn equal_values<V: Eq + std::fmt::Debug>(&mut self, values: &[Option<V>], bags: &[Vec<V>]) {
        assert_eq!(values.len(), bags.len());
        for (rank, (value, bag)) in values.iter().zip(bags).enumerate() {
            assert!(value.iter().eq(bag), "rank {rank}: {value:?} vs {bag:?}");
        }
        self.fast_values += values.len();
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Step {
    name: &'static str,
    cost: i64,
    arity: usize,
}

impl Operator for Step {
    fn arity(&self) -> usize {
        self.arity
    }
}

impl ScoredOperator for Step {
    fn cost(&self) -> Cost {
        Cost::Finite(self.cost)
    }
}

fn step<const N: usize>(name: &'static str, cost: i64, children: [usize; N]) -> Rule<Step> {
    Rule::new(
        Step {
            name,
            cost,
            arity: N,
        },
        children,
    )
}

fn words<T: Copy>(alphabet: &[T], max_len: usize) -> Vec<Vec<T>> {
    let mut all = vec![Vec::new()];
    let mut frontier = all.clone();
    for _ in 0..max_len {
        frontier = frontier
            .iter()
            .flat_map(|prefix| {
                alphabet.iter().map(move |&last| {
                    let mut word = prefix.clone();
                    word.push(last);
                    word
                })
            })
            .collect();
        all.extend(frontier.iter().cloned());
    }
    all
}

type Recipe = (&'static str, fn() -> Result<Checks, Error>);

fn main() -> Result<(), Error> {
    let recipes: [Recipe; 22] = [
        ("Arithmetic parenthesization", intervals::arithmetic),
        ("Minimum matrix-chain work", intervals::matrix_chain),
        ("Matrix work and memory", intervals::matrix_frontier),
        ("Optimal search tree", intervals::search_tree),
        ("Equal wings around a center", intervals::palindrome),
        ("Global alignment", alignment::global),
        ("Local alignment with starts", alignment::local),
        ("Affine gap runs", alignment::affine),
        ("Semiglobal infix match", alignment::infix),
        ("Three-way alignment", alignment::three_tracks),
        ("Edit trade-offs", alignment::trade_offs),
        ("Hidden dice", weighted::hidden_dice),
        ("Weighted span parsing", weighted::span_parser),
        ("Ordered forest alignment", forests::alignment),
        ("Promoting tree edit mappings", forests::edit),
        ("Hamiltonian paths and edge mass", routes::hamiltonian),
        ("Anchored tours", routes::tour),
        ("Repeated halves", languages::repeated_half),
        ("Cross-serial runs", languages::cross_serial),
        ("Noncrossing paired-count folding", structures::nussinov),
        ("Folds by shape", structures::shapes),
        ("Two crossing pairs", structures::single_crossing),
    ];
    for (index, (name, run)) in recipes.into_iter().enumerate() {
        let checks = run()?;
        println!(
            "{:02} | {name} | {} inputs | {} reference ranks | {} fast value comparisons",
            index + 1,
            checks.inputs,
            checks.ranks,
            checks.fast_values
        );
    }
    Ok(())
}

#[cfg(test)]
#[test]
fn all_recipes() -> Result<(), Error> {
    main()
}
