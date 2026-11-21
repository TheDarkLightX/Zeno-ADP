#[path = "support/optimal_bst.rs"]
mod optimal_bst;

use zeno_adp::{compiled, Error};

fn main() -> Result<(), Error> {
    let lookups = [8, 2, 5, 1];
    let input = optimal_bst::prepare(&lookups)?;
    let source = optimal_bst::grammar(&input)?;
    let scores = optimal_bst::minimum(&input)?;
    let baseline = optimal_bst::direct(&input)?;
    let best = compiled::best(&source)?.recover().first_minimum_tree()?;
    println!("lookups in key order {lookups:?}");
    println!(
        "minimum {:?}, direct {:?}",
        scores.answer(),
        baseline.last()
    );
    println!("one optimal search tree {best:?}");
    Ok(())
}
