//! Least fixed points of finite grounded grammars for two scalar questions.
//!
//! Rules may revisit a cell. Every positive result has a finite derivation,
//! represented by an ordered rule choice per cell and strictly decreasing ranks.

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::fmt;
use std::str::FromStr;

use num_bigint::BigUint;

use crate::{Cell, Rule};

/// A ground production with a nonnegative integer weight and ordered child occurrences.
/// The weight is used by min-plus. Boolean existence treats every rule as enabled.
pub type Production = Rule<BigUint>;

/// Closed set of questions supported by the cyclic evaluator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Question {
    Boolean,
    NonnegativeMinPlus,
}

impl FromStr for Question {
    type Err = Error;

    fn from_str(name: &str) -> Result<Self, Error> {
        match name {
            "boolean" => Ok(Self::Boolean),
            "nonnegative-min-plus" => Ok(Self::NonnegativeMinPlus),
            _ => Err(Error::UnsupportedCarrier(name.into())),
        }
    }
}

/// Ordinal of a production in its cell and the rank of the finite witness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Witness {
    pub rule: usize,
    pub rank: usize,
}

/// One entry per cell. `None` means no finite derivation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Certificate<W> {
    pub values: Vec<Option<W>>,
    pub witnesses: Vec<Option<Witness>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Solution {
    /// `Some(())` means a finite derivation exists.
    Boolean(Certificate<()>),
    MinPlus(Certificate<BigUint>),
}

#[derive(Clone, Debug)]
pub struct GroundChart {
    cells: Vec<Vec<Production>>,
    root: Cell,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    UnsupportedCarrier(String),
    MissingRoot(Cell),
    InvalidChild {
        cell: Cell,
        rule: usize,
        child: Cell,
    },
    CertificateSize {
        cells: usize,
        values: usize,
        witnesses: usize,
    },
    Equation {
        cell: Cell,
    },
    Witness {
        cell: Cell,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedCarrier(name) => write!(
                f,
                "cyclic carrier {name:?} is unsupported; use boolean or nonnegative-min-plus"
            ),
            Self::MissingRoot(root) => write!(f, "root cell {root} does not exist"),
            Self::InvalidChild { cell, rule, child } => write!(
                f,
                "cell {cell}, production {rule} refers to absent child {child}"
            ),
            Self::CertificateSize {
                cells,
                values,
                witnesses,
            } => write!(
                f,
                "certificate gives {values} values and {witnesses} witnesses for {cells} cells"
            ),
            Self::Equation { cell } => write!(f, "grounded equation fails at cell {cell}"),
            Self::Witness { cell } => {
                write!(f, "cell {cell} lacks a matching finite ranked witness")
            }
        }
    }
}

impl std::error::Error for Error {}

struct Pending<W> {
    head: Cell,
    ordinal: usize,
    remaining: usize,
    cost: W,
}

impl GroundChart {
    /// Check root and child references while allowing arbitrary dependencies.
    pub fn new(cells: Vec<Vec<Production>>, root: Cell) -> Result<Self, Error> {
        if root >= cells.len() {
            return Err(Error::MissingRoot(root));
        }
        for (cell, rules) in cells.iter().enumerate() {
            for (rule, production) in rules.iter().enumerate() {
                for &child in &production.children {
                    if child >= cells.len() {
                        return Err(Error::InvalidChild { cell, rule, child });
                    }
                }
            }
        }
        Ok(Self { cells, root })
    }

    pub fn root(&self) -> Cell {
        self.root
    }

    pub fn cells(&self) -> &[Vec<Production>] {
        &self.cells
    }

    /// Return the **Exact** least fixed point and a finite ranked witness at
    /// every inhabited cell. Witness rules refer to this chart's ordered rows.
    pub fn solve(&self, question: Question) -> Result<crate::Exact<Solution>, Error> {
        let answer = match question {
            Question::Boolean => Solution::Boolean(self.agenda(|_| (), |_, _| {})),
            Question::NonnegativeMinPlus => {
                Solution::MinPlus(self.agenda(BigUint::clone, |a, b| *a += b))
            }
        };
        self.verify(&answer)?;
        Ok(crate::Exact(answer))
    }

    /// Check the grounded equations and finite attainment for all cells.
    /// This verifier needs neither the agenda nor the solver's tie order.
    pub fn verify(&self, solution: &Solution) -> Result<(), Error> {
        match solution {
            Solution::Boolean(certificate) => self.check(certificate, |_| (), |_, _| {}),
            Solution::MinPlus(certificate) => {
                self.check(certificate, BigUint::clone, |a, b| *a += b)
            }
        }
    }

    fn agenda<W: Clone + Default + Ord>(
        &self,
        weight: fn(&BigUint) -> W,
        add: fn(&mut W, &W),
    ) -> Certificate<W> {
        let n = self.cells.len();
        let mut uses = vec![Vec::new(); n];
        let mut pending = Vec::new();
        let mut ready = BinaryHeap::new();
        for (head, rules) in self.cells.iter().enumerate() {
            for (ordinal, rule) in rules.iter().enumerate() {
                if rule.children.is_empty() {
                    ready.push(Reverse((weight(&rule.operator), head, ordinal)));
                } else {
                    for &child in &rule.children {
                        uses[child].push(pending.len());
                    }
                    pending.push(Pending {
                        head,
                        ordinal,
                        remaining: rule.children.len(),
                        cost: weight(&rule.operator),
                    });
                }
            }
        }
        let mut values = vec![None; n];
        let mut witnesses = vec![None; n];
        let mut rank = 0;
        while let Some(Reverse((cost, cell, rule))) = ready.pop() {
            if witnesses[cell].is_some() {
                continue;
            }
            // A nonnegative production costs at least each of its children.
            // A cheaper finite tree would have a ready subtree before this pop.
            witnesses[cell] = Some(Witness { rule, rank });
            rank += 1;
            for &id in &uses[cell] {
                let production = &mut pending[id];
                production.remaining -= 1;
                add(&mut production.cost, &cost);
                if production.remaining == 0 && witnesses[production.head].is_none() {
                    ready.push(Reverse((
                        std::mem::take(&mut production.cost),
                        production.head,
                        production.ordinal,
                    )));
                }
            }
            values[cell] = Some(cost);
        }
        Certificate { values, witnesses }
    }

    fn check<W: Eq + Ord>(
        &self,
        certificate: &Certificate<W>,
        weight: fn(&BigUint) -> W,
        add: fn(&mut W, &W),
    ) -> Result<(), Error> {
        let Certificate { values, witnesses } = certificate;
        let cells = self.cells.len();
        if values.len() != cells || witnesses.len() != cells {
            return Err(Error::CertificateSize {
                cells,
                values: values.len(),
                witnesses: witnesses.len(),
            });
        }
        for (cell, rules) in self.cells.iter().enumerate() {
            let mut best = None;
            let mut attains = false;
            let witness = witnesses[cell];
            for (ordinal, rule) in rules.iter().enumerate() {
                let candidate =
                    rule.children
                        .iter()
                        .try_fold(weight(&rule.operator), |mut cost, &child| {
                            add(&mut cost, values[child].as_ref()?);
                            Some(cost)
                        });
                if let Some(witness) = witness {
                    if witness.rule == ordinal {
                        attains = candidate.is_some()
                            && candidate == values[cell]
                            && rule.children.iter().all(|&child| {
                                witnesses[child].is_some_and(|earlier| earlier.rank < witness.rank)
                            });
                    }
                }
                if let Some(cost) = candidate {
                    if best.as_ref().is_none_or(|old| &cost < old) {
                        best = Some(cost);
                    }
                }
            }
            if best != values[cell] {
                return Err(Error::Equation { cell });
            }
            if (values[cell].is_some() || witness.is_some()) && !attains {
                return Err(Error::Witness { cell });
            }
        }
        Ok(())
    }
}
