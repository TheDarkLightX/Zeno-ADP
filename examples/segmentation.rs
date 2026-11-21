#[path = "support/segmentation.rs"]
mod segmentation;

use zeno_adp::{compiled, Error};

fn main() -> Result<(), Error> {
    let bits = [false, false, false, false, true, true, true, true];
    let input = segmentation::prepare(&bits);
    let source = segmentation::grammar(&input)?;
    let scores = segmentation::minimum(&input)?;
    let baseline = segmentation::direct(&input)?;
    let best = compiled::best(&source)?.recover().first_minimum_tree()?;
    println!("observations {bits:?}");
    println!(
        "minimum {:?}, direct {:?}",
        scores.answer(),
        baseline.last()
    );
    println!("one optimal partition {best:?}");
    Ok(())
}
