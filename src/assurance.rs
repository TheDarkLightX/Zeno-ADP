//! Labels that say what a certificate answers and how it was checked.
//!
//! Meta-query certificates name their [`QuestionKind`]s, [`Family`],
//! [`CertificateKind`] and [`Shape`]. The kind describes preservation within
//! the declared family, whose members are the candidates of the question.
//!
//! Checked solver returns carry the [`crate::Exact`] wrapper. The raw
//! `Common`, `ZeroRegret`, `WithinBudget` and `Quotient` types also expose
//! a `LABEL` constant describing their checked results. `ObserverCheck::label_for`
//! gives a label for a length, and `Solved::scorer_label` records the scorer
//! label for the chart instance. Raw `Collision`, `FeatureSets`, `Violation`,
//! `Refusal` and common `Witness` values get their assurance from successful
//! replay in context.

use std::fmt;

/// The question a certificate answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum QuestionKind {
    /// Some optimal candidate and the optimal value.
    OneOptimum,
    /// The set of all optimal candidates.
    AllTies,
    /// The optimal candidates in order, with multiplicity.
    OrderedMinimizers,
    /// The number of candidates with a property.
    Count,
    /// A specific candidate, identified by its derivation.
    WitnessIdentity,
    /// Whether any candidate has a property.
    Existence,
    /// A bound on a value. A bound is not an answer.
    Bound,
}

impl QuestionKind {
    pub const ALL: [Self; 7] = [
        Self::OneOptimum,
        Self::AllTies,
        Self::OrderedMinimizers,
        Self::Count,
        Self::WitnessIdentity,
        Self::Existence,
        Self::Bound,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            Self::OneOptimum => "one-optimum",
            Self::AllTies => "all-ties",
            Self::OrderedMinimizers => "ordered-minimizers",
            Self::Count => "count",
            Self::WitnessIdentity => "witness-identity",
            Self::Existence => "existence",
            Self::Bound => "bound",
        }
    }
}

/// How a certificate establishes its answer. Each kind says how the candidates
/// the answer was computed on (the retained list) relate to the original
/// candidates, and the certificate's own checker replays that relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CertificateKind {
    /// Every dropped candidate has a retained candidate that is no worse. The
    /// checker replays the retained candidates, for example one witness.
    Weak,
    /// Preserves every optimum within the declared family, including order and
    /// multiplicity when the shape requires them. If the restriction drops a
    /// member of the family, the checker establishes that it is strictly worse
    /// than a retained member.
    Strict,
    /// The retained list is the original list: nothing dropped, the same order and
    /// multiplicity, with every score kept. The checker replays every equation and
    /// witness against the declared model.
    ExactReplay,
    /// The retained list has the same members as the original list; order and
    /// multiplicity may differ. The checker enumerates every candidate of the
    /// declared finite domain.
    FullEnumeration,
}

impl CertificateKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Weak => "weak",
            Self::Strict => "strict",
            Self::ExactReplay => "exact-replay",
            Self::FullEnumeration => "full-enumeration",
        }
    }
}

/// The candidates a certificate's questions are asked over.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Family {
    /// Every candidate of the original list.
    AllCandidates,
    /// The candidates that are optimal, among the original list, in every selected
    /// model.
    OptimalInEveryModel,
    /// The candidates whose regret is within the budget of every world. A zero
    /// budget asks for an optimal completion in every world.
    WithinBudgetInEveryWorld,
}

impl Family {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::AllCandidates => "all-candidates",
            Self::OptimalInEveryModel => "optimal-in-every-model",
            Self::WithinBudgetInEveryWorld => "within-budget-in-every-world",
        }
    }
}

/// How the answer's candidates relate to the original candidates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Shape {
    /// A set of candidates, with no order or multiplicity promised.
    SetLevel,
    /// The original ordered candidates, filtered by a test on each candidate, so
    /// order and multiplicity are kept.
    LiteralFilter,
}

impl Shape {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::SetLevel => "set-level",
            Self::LiteralFilter => "literal-filter",
        }
    }
}

/// The assurance carried by a result.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Label {
    /// The answer is checked against the declared model.
    Exact,
    /// A checked feasible answer with a proven gap.
    Bounded,
    /// Within a stated error with a stated failure probability.
    Estimated,
    /// No guarantee.
    Unchecked,
}

impl Label {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Exact => "Exact",
            Self::Bounded => "Bounded",
            Self::Estimated => "Estimated",
            Self::Unchecked => "Unchecked",
        }
    }
}

impl fmt::Display for QuestionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Display for CertificateKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}
