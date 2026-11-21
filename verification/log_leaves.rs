//! Observe the two public log algebras at every leaf of a ranked chart.

use std::error::Error;
use std::io::{self, BufRead, BufWriter, Write};
use zeno_adp::probability::{LogMaxProduct, LogSumProduct, Rational, WeightedOperator};
use zeno_adp::{tabulate_cells, Chart, Operator, Rule};

#[derive(Clone)]
struct Leaf(Rational);

impl Operator for Leaf {
    fn arity(&self) -> usize {
        0
    }
}

impl WeightedOperator for Leaf {
    fn weight(&self) -> Rational {
        self.0
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut cells = Vec::new();
    for line in io::stdin().lock().lines() {
        let line = line?;
        let (n, d) = line
            .split_once(' ')
            .ok_or("expected numerator and denominator")?;
        let weight = Rational::new(n.parse()?, d.parse()?).ok_or("denominator is zero")?;
        cells.push(vec![Rule::new(Leaf(weight), [])]);
    }
    let chart = Chart::new(cells, 0)?;
    let sums = tabulate_cells(&chart, &LogSumProduct)?;
    let maxima = tabulate_cells(&chart, &LogMaxProduct)?;
    let mut out = BufWriter::new(io::stdout().lock());
    for (sum, max) in sums.iter().zip(maxima) {
        let ([sum], [max]) = (sum.as_slice(), max.as_slice()) else {
            return Err("expected one observation per leaf and algebra".into());
        };
        writeln!(
            out,
            "{:016x} {:016x}",
            sum.ln().to_bits(),
            max.ln().to_bits()
        )?;
    }
    out.flush()?;
    Ok(())
}
