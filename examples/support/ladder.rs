use num_bigint::BigInt;
use zeno_adp::decomposition::{Bag, Decomposition, Factor};

pub fn unary(variable: usize, weight: i64) -> Factor {
    Factor::Unary {
        variable,
        costs: [Some(BigInt::ZERO), Some(-BigInt::from(weight))],
    }
}

pub fn edge(left: usize, right: usize) -> Factor {
    Factor::Pair {
        left,
        right,
        costs: [
            [Some(BigInt::ZERO), Some(BigInt::ZERO)],
            [Some(BigInt::ZERO), None],
        ],
    }
}

// Bags contain two adjacent columns when available. Shorter ladders use
// one bag. Each factor belongs to the first bag covering its scope.
pub fn ladder(weights: &[[i64; 2]]) -> (Vec<Factor>, Decomposition) {
    let columns = weights.len();
    let mut bags = (0..columns.saturating_sub(1).max(1))
        .map(|column| Bag {
            variables: (2 * column..2 * (column + 2).min(columns)).collect(),
            factors: Vec::new(),
        })
        .collect::<Vec<_>>();
    let edges = (1..bags.len()).map(|bag| (bag - 1, bag)).collect();
    let mut factors = Vec::new();
    for (column, values) in weights.iter().enumerate() {
        let owner = column.saturating_sub(1);
        for (row, &weight) in values.iter().enumerate() {
            bags[owner].factors.push(factors.len());
            factors.push(unary(2 * column + row, weight));
        }
        bags[owner].factors.push(factors.len());
        factors.push(edge(2 * column, 2 * column + 1));
        if column > 0 {
            for row in 0..2 {
                bags[owner].factors.push(factors.len());
                factors.push(edge(2 * (column - 1) + row, 2 * column + row));
            }
        }
    }
    (
        factors,
        Decomposition {
            bags,
            edges,
            root: 0,
        },
    )
}
