//! Distinct counts for ordered binary tree grammars at exact leaf counts.

use std::collections::{BTreeMap, BTreeSet};

use crate::{reserve_table, Chart, Error, Operator, Rule};

/// A production of a binary tree grammar. A branch has one fixed constructor
/// and ordered children. Nonterminals are indices into the grammar's rows.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Production<L> {
    Leaf(L),
    Branch { left: usize, right: usize },
}

/// A constructor of the underlying tree. Nonterminal indices and production
/// ordinals play no part in tree identity.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Constructor<L> {
    Leaf(L),
    Branch,
}

impl<L: Clone> Operator for Constructor<L> {
    fn arity(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::Branch => 2,
        }
    }
}

/// An ordered binary grammar with a finite set of nonterminals. Recursion is
/// ranked by leaf count, since each branch partitions a positive count into
/// two positive counts.
#[derive(Debug, Clone)]
pub struct BinaryTreeGrammar<L> {
    productions: Vec<Vec<Production<L>>>,
}

impl<L> BinaryTreeGrammar<L> {
    pub fn new(productions: Vec<Vec<Production<L>>>) -> Result<Self, Error> {
        let grammar = Self { productions };
        for production in grammar.productions.iter().flatten() {
            if let Production::Branch { left, right } = *production {
                check_nonterminal(grammar.productions.len(), left)?;
                check_nonterminal(grammar.productions.len(), right)?;
            }
        }
        Ok(grammar)
    }
}

impl<L: Clone> BinaryTreeGrammar<L> {
    /// Build the reference chart for a start and exact leaf count. A zero
    /// leaf count has no derivations. Repeated productions retain multiplicity.
    pub fn chart(&self, leaves: usize, start: usize) -> Result<Chart<Constructor<L>>, Error> {
        let width = self.productions.len();
        check_nonterminal(width, start)?;
        let length = leaves
            .checked_add(1)
            .and_then(|rows| rows.checked_mul(width))
            .ok_or(Error::Overflow)?;
        let mut cells = reserve_table(length)?;
        cells.resize_with(length, Vec::new);
        for size in 1..=leaves {
            for (parent, productions) in self.productions.iter().enumerate() {
                let rules = &mut cells[size * width + parent];
                for production in productions {
                    match production {
                        Production::Leaf(label) if size == 1 => {
                            rules.push(Rule::new(Constructor::Leaf(label.clone()), []));
                        }
                        Production::Leaf(_) => {}
                        Production::Branch { left, right } => {
                            for split in 1..size {
                                rules.push(Rule::new(
                                    Constructor::Branch,
                                    [split * width + left, (size - split) * width + right],
                                ));
                            }
                        }
                    }
                }
            }
        }
        Chart::new(cells, leaves * width + start)
    }
}

impl<L: Ord> BinaryTreeGrammar<L> {
    /// Count tree languages by grouped inclusion-exclusion. Each distinct
    /// tree belongs to exactly one acceptance profile, the set of
    /// nonterminals that accept it. All nonempty intersection terms for a
    /// profile sum to one for each nonterminal whose union accepts it.
    /// The number of reachable profiles can be exponential.
    pub fn distinct_counts(&self, max_leaves: usize) -> Result<DistinctCounts, Error> {
        let rows = max_leaves.checked_add(1).ok_or(Error::Overflow)?;
        let mut profiles = reserve_table(rows)?;
        profiles.resize_with(rows, BTreeMap::new);

        let mut leaves = BTreeMap::<_, BTreeSet<_>>::new();
        let mut branches = BTreeMap::<_, BTreeSet<_>>::new();
        for (parent, rules) in self.productions.iter().enumerate() {
            for rule in rules {
                match rule {
                    Production::Leaf(label) => {
                        leaves.entry(label).or_default().insert(parent);
                    }
                    &Production::Branch { left, right } => {
                        branches.entry((left, right)).or_default().insert(parent);
                    }
                }
            }
        }

        if let Some(single_leaf) = profiles.get_mut(1) {
            for parents in leaves.into_values() {
                increment(single_leaf, parents.into_iter().collect(), 1)?;
            }
        }
        let mut parents = BTreeSet::new();
        for size in 2..=max_leaves {
            let (smaller, current) = profiles.split_at_mut(size);
            for split in 1..size {
                for (left, &left_count) in &smaller[split] {
                    for (right, &right_count) in &smaller[size - split] {
                        parents.clear();
                        for &l in left {
                            for &r in right {
                                if let Some(accepted) = branches.get(&(l, r)) {
                                    parents.extend(accepted);
                                }
                            }
                        }
                        if !parents.is_empty() {
                            let count =
                                left_count.checked_mul(right_count).ok_or(Error::Overflow)?;
                            increment(&mut current[0], parents.iter().copied().collect(), count)?;
                        }
                    }
                }
            }
        }
        Ok(DistinctCounts {
            profiles,
            nonterminals: self.productions.len(),
        })
    }
}

type Profiles = BTreeMap<Vec<usize>, u128>;

fn increment(profiles: &mut Profiles, profile: Vec<usize>, count: u128) -> Result<(), Error> {
    let entry = profiles.entry(profile).or_default();
    *entry = entry.checked_add(count).ok_or(Error::Overflow)?;
    Ok(())
}

fn check_nonterminal(count: usize, nonterminal: usize) -> Result<(), Error> {
    if nonterminal >= count {
        return Err(Error::InvalidNonterminal(nonterminal));
    }
    Ok(())
}

/// Counts and semantic intersections for a binary grammar up to a supplied
/// exact leaf count. Counts and intermediate profile buckets use checked
/// `u128` arithmetic.
#[derive(Debug, Clone)]
pub struct DistinctCounts {
    profiles: Vec<Profiles>,
    nonterminals: usize,
}

impl DistinctCounts {
    pub fn count(&self, leaves: usize, start: usize) -> Result<u128, Error> {
        self.intersection(leaves, start, &[])
    }

    /// Count distinct trees accepted by all listed nonterminals. The first
    /// argument after the size makes the intersection nonempty. Repeated
    /// nonterminal indices leave its meaning unchanged.
    pub fn intersection(&self, leaves: usize, first: usize, rest: &[usize]) -> Result<u128, Error> {
        let profiles = self
            .profiles
            .get(leaves)
            .ok_or(Error::LeafCountOutOfRange(leaves))?;
        let nonterminals = std::iter::once(first).chain(rest.iter().copied());
        for nonterminal in nonterminals.clone() {
            check_nonterminal(self.nonterminals, nonterminal)?;
        }
        profiles
            .iter()
            .filter(|(profile, _)| {
                nonterminals
                    .clone()
                    .all(|nt| profile.binary_search(&nt).is_ok())
            })
            .try_fold(0u128, |sum, (_, &count)| {
                sum.checked_add(count).ok_or(Error::Overflow)
            })
    }
}
