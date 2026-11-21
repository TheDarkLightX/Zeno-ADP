//! Canonical answer classes and questions evaluated within each class.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;

use crate::{Algebra, Error};

/// Compute a canonical answer from a constructor and its children's canonical
/// answers. Use a key whose natural ordering agrees with its equality.
/// Implementations should be deterministic and free of side effects.
pub trait Classification<O> {
    type Class: Clone + Debug + Ord;

    fn classify(&self, operator: &O, children: &[&Self::Class]) -> Result<Self::Class, Error>;
}

/// The distinct-class question. Its answers are the sorted canonical keys.
#[derive(Debug, Clone, Copy)]
pub struct Classes<C> {
    classification: C,
}

impl<C> Classes<C> {
    pub fn new(classification: C) -> Self {
        Self { classification }
    }
}

impl<O, C: Classification<O>> Algebra<O> for Classes<C> {
    type Value = C::Class;

    fn apply(&self, operator: &O, children: &[&Self::Value]) -> Result<Self::Value, Error> {
        self.classification.classify(operator, children)
    }

    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
        Ok(candidates
            .iter()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .cloned()
            .collect())
    }
}

/// A classified product. The question's choice receives the ordered bag
/// within each class, including derivation multiplicity. Results are ordered
/// by class key and then by the question's choice order.
///
/// For example, an additive minimum returns one best score per nonempty class.
/// A derivation-count question returns the size of each class. If a constructor
/// maps several child classes into the same parent class, sorting the child
/// keys can change which witness an order-sensitive choice selects. Audit the
/// paired question with [`crate::AnswerOrder::Ordered`] when order matters.
/// Separate component audits do not establish the product's Bellman laws.
#[derive(Debug, Clone, Copy)]
pub struct Classified<C, Q> {
    classes: Classes<C>,
    question: Q,
}

impl<C, Q> Classified<C, Q> {
    pub fn new(classification: C, question: Q) -> Self {
        Self {
            classes: Classes::new(classification),
            question,
        }
    }

    pub fn classes(&self) -> &Classes<C> {
        &self.classes
    }
}

impl<O, C: Classification<O>, Q: Algebra<O>> Algebra<O> for Classified<C, Q> {
    type Value = (C::Class, Q::Value);

    fn apply(&self, operator: &O, children: &[&Self::Value]) -> Result<Self::Value, Error> {
        let keys: Vec<_> = children.iter().map(|pair| &pair.0).collect();
        let values: Vec<_> = children.iter().map(|pair| &pair.1).collect();
        Ok((
            self.classes.apply(operator, &keys)?,
            self.question.apply(operator, &values)?,
        ))
    }

    fn choose(&self, candidates: &[Self::Value]) -> Result<Vec<Self::Value>, Error> {
        let mut groups = BTreeMap::<&C::Class, Vec<Q::Value>>::new();
        for (class, value) in candidates {
            groups.entry(class).or_default().push(value.clone());
        }
        let mut answers = Vec::new();
        for (class, values) in groups {
            answers.extend(
                self.question
                    .choose(&values)?
                    .into_iter()
                    .map(|answer| (class.clone(), answer)),
            );
        }
        Ok(answers)
    }
}
