use super::{inside, Mass, Rational, SumProduct, WeightedOperator};
use crate::{Cell, Chart, Error, Tree};

/// Samples ordered derivations proportional to their exact weight. Equal tree
/// terms can occur at multiple derivation indices and contribute separately.
#[derive(Debug)]
pub struct ExactSampler<'a, O> {
    chart: &'a Chart<O>,
    inside: Vec<Rational>,
    branches: Vec<Vec<Rational>>,
}

impl<'a, O: WeightedOperator> ExactSampler<'a, O> {
    /// Prepare branch probabilities from all-cell exact inside weights.
    pub fn new(chart: &'a Chart<O>) -> Result<Self, Error> {
        let inside = inside(chart, &SumProduct)?;
        let branches = chart
            .cells()
            .iter()
            .map(|rules| {
                let mut remaining = Rational::ZERO;
                let mut branches = Vec::with_capacity(rules.len());
                for rule in rules.iter().rev() {
                    let mass = Rational::product(
                        rule.operator.weight(),
                        rule.children.iter().map(|&child| inside[child]),
                    )?;
                    remaining = remaining.checked_add(mass)?;
                    branches.push(mass.checked_div(remaining)?.unwrap_or(Rational::ZERO));
                }
                branches.reverse();
                Ok(branches)
            })
            .collect::<Result<_, Error>>()?;
        Ok(Self {
            chart,
            inside,
            branches,
        })
    }

    /// The exact probabilities of each rule in positional order, conditional
    /// on sampling a derivation at this cell. A missing or zero-mass cell
    /// returns `Ok(None)`.
    pub fn rule_probabilities(&self, cell: Cell) -> Result<Option<Vec<Rational>>, Error> {
        let Some(_) = self
            .inside
            .get(cell)
            .filter(|&&mass| mass != Rational::ZERO)
        else {
            return Ok(None);
        };
        let mut remaining = Rational::ONE;
        self.branches[cell]
            .iter()
            .map(|&conditional| {
                let probability = remaining.checked_mul(conditional)?;
                let failure = Rational::new(
                    conditional.denominator() - conditional.numerator(),
                    conditional.denominator(),
                )
                .expect("positive denominator");
                remaining = remaining.checked_mul(failure)?;
                Ok(probability)
            })
            .collect::<Result<_, _>>()
            .map(Some)
    }
}

impl<O: Clone> ExactSampler<'_, O> {
    /// Draw one tree at the chart root. Supply independent uniform `u64`
    /// words. Rejection sampling avoids modulo bias. A zero partition
    /// returns `None` without consuming any words.
    pub fn sample(&self, words: impl FnMut() -> u64) -> Option<Tree<O>> {
        self.sample_from(self.chart.root(), words)
    }

    /// Draw at any chart cell. Missing and zero-mass cells return `None`.
    pub fn sample_from(&self, cell: Cell, mut words: impl FnMut() -> u64) -> Option<Tree<O>> {
        self.inside
            .get(cell)
            .filter(|&&mass| mass != Rational::ZERO)?;
        Some(self.draw_tree(cell, &mut words))
    }

    fn draw_tree(&self, cell: Cell, words: &mut impl FnMut() -> u64) -> Tree<O> {
        let index = self.branches[cell]
            .iter()
            .position(|&probability| bernoulli(probability, words))
            .expect("positive cell has a final positive branch with probability one");
        let rule = &self.chart.cells()[cell][index];
        Tree {
            operator: rule.operator.clone(),
            children: rule
                .children
                .iter()
                .map(|&child| self.draw_tree(child, words))
                .collect(),
        }
    }
}

fn bernoulli(probability: Rational, words: &mut impl FnMut() -> u64) -> bool {
    if probability == Rational::ZERO || probability == Rational::ONE {
        return probability == Rational::ONE;
    }

    let denominator = probability.denominator();
    let bits = u128::BITS - (denominator - 1).leading_zeros();
    let mask = u128::MAX >> (u128::BITS - bits);
    loop {
        let ticket = if bits <= u64::BITS {
            u128::from(words())
        } else {
            (u128::from(words()) << u64::BITS) | u128::from(words())
        } & mask;
        if ticket < denominator {
            return ticket < probability.numerator();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_bernoulli_ticket_domains_and_rejection() {
        // Covers non-power-of-two rejection and the transition between
        // one and two bits in the accepted ticket domain.
        const MAX_SMALL_DENOMINATOR: u128 = 4;
        for denominator in 2..=MAX_SMALL_DENOMINATOR {
            for numerator in 1..denominator {
                let probability = Rational::new(numerator, denominator).unwrap();
                let mut accepted = 0;
                for ticket in 0..probability.denominator() {
                    accepted += usize::from(bernoulli(probability, &mut || ticket as u64));
                }
                assert_eq!(accepted as u128, probability.numerator());
            }
        }
        let mut words = [3, 2].into_iter();
        assert!(!bernoulli(Rational::new(1, 3).unwrap(), &mut || words
            .next()
            .unwrap()));
        assert_eq!(words.next(), None);

        let wide = Rational::new(1, u128::MAX).unwrap();
        let mut words = [u64::MAX, u64::MAX, 0, 0].into_iter();
        assert!(bernoulli(wide, &mut || words.next().unwrap()));
        assert_eq!(words.next(), None);
    }
}
