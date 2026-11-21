use zeno_adp::algebras::{Cost, ScoredOperator};
use zeno_adp::classification::Classification;
use zeno_adp::grammars::{nussinov, Fold};
use zeno_adp::{Chart, Error, Operator, Rule};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Folding {
    Base(Fold),
    Split,
}

impl Operator for Folding {
    fn arity(&self) -> usize {
        match self {
            Self::Base(operator) => operator.arity(),
            Self::Split => 2,
        }
    }
}

impl ScoredOperator for Folding {
    fn cost(&self) -> Cost {
        match self {
            Self::Base(operator) => operator.cost(),
            Self::Split => Cost::Finite(0),
        }
    }
}

/// Add a redundant concatenation at every split into two nonempty spans.
pub fn chart(sequence: &[u8], min_loop: usize, split: bool) -> Result<Chart<Folding>, Error> {
    let base = nussinov(sequence, min_loop)?;
    let mut cells: Vec<Vec<_>> = base
        .cells()
        .iter()
        .map(|rules| {
            rules
                .iter()
                .map(|rule| Rule::new(Folding::Base(rule.operator), rule.children.clone()))
                .collect()
        })
        .collect();

    if split {
        let n = sequence.len();
        // Nussinov places the shared empty span first, then spans by
        // increasing length and start position.
        let mut starts = vec![0];
        let mut next_cell = 1;
        for len in 1..=n {
            starts.push(next_cell);
            next_cell += n - len + 1;
        }
        for len in 2..=n {
            for left in 0..=n - len {
                for prefix in 1..len {
                    cells[starts[len] + left].push(Rule::new(
                        Folding::Split,
                        [starts[prefix] + left, starts[len - prefix] + left + prefix],
                    ));
                }
            }
        }
    }
    Chart::new(cells, base.root())
}

#[derive(Clone, Copy)]
pub struct DotBracket;

impl Classification<Folding> for DotBracket {
    type Class = String;

    fn classify(&self, operator: &Folding, children: &[&String]) -> Result<String, Error> {
        Ok(match operator {
            Folding::Base(Fold::Empty) => String::new(),
            Folding::Base(Fold::Unpaired { .. }) => format!(".{}", children[0]),
            Folding::Base(Fold::Pair { .. }) => format!("({}){}", children[0], children[1]),
            Folding::Split => format!("{}{}", children[0], children[1]),
        })
    }
}
