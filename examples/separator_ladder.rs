//! A weighted independent set on a ladder with a supplied width-three decomposition.

#[path = "support/ladder.rs"]
mod ladder;

use zeno_adp::decomposition::Compiled;
use zeno_adp::fast::RuleSource;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    const COLUMNS: usize = 64; // Large enough to contrast with enumerating 2^128 assignments.
    let weights = vec![[3, 2]; COLUMNS];
    let (factors, bags) = ladder::ladder(&weights);
    let program = Compiled::new(2 * weights.len(), factors, bags)?;
    let result = program.solve()?;
    let label = result.label();
    let result = result.into_inner();
    let optimum = result.table[program.root()]
        .as_ref()
        .expect("the empty set is feasible");
    let selected = result.assignment.expect("the optimum has a witness");
    println!(
        "{label}: maximum weight {}, {} selected vertices, {} ranked cells",
        -optimum,
        selected.iter().filter(|&&value| value).count(),
        program.cell_count()
    );
    Ok(())
}
