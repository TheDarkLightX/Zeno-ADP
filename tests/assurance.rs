use zeno_adp::assurance::{CertificateKind, Family, Label, QuestionKind, Shape};
use zeno_adp::common_optimum::{Collision, Common};
use zeno_adp::robust_prefix::{WithinBudget, ZeroRegret};
use zeno_adp::state_discovery::{FeatureSets, ObserverCheck, Quotient, Refusal, Violation};

#[test]
fn certificate_vocabulary_words() {
    let questions: Vec<&str> = QuestionKind::ALL.iter().map(|q| q.as_str()).collect();
    assert_eq!(
        questions,
        [
            "one-optimum",
            "all-ties",
            "ordered-minimizers",
            "count",
            "witness-identity",
            "existence",
            "bound"
        ]
    );
    assert_eq!(CertificateKind::Weak.as_str(), "weak");
    assert_eq!(CertificateKind::Strict.as_str(), "strict");
    assert_eq!(CertificateKind::ExactReplay.as_str(), "exact-replay");
    assert_eq!(
        CertificateKind::FullEnumeration.as_str(),
        "full-enumeration"
    );
    assert_eq!(Shape::SetLevel.as_str(), "set-level");
    assert_eq!(Shape::LiteralFilter.as_str(), "literal-filter");
    assert_eq!(Label::Exact.as_str(), "Exact");
    assert_eq!(Family::AllCandidates.as_str(), "all-candidates");
    assert_eq!(
        Family::OptimalInEveryModel.as_str(),
        "optimal-in-every-model"
    );
    assert_eq!(
        Family::WithinBudgetInEveryWorld.as_str(),
        "within-budget-in-every-world"
    );
}

#[test]
fn each_certificate_names_the_family_its_kind_is_about() {
    assert_eq!(Common::FAMILY, Family::OptimalInEveryModel);
    assert_eq!(ZeroRegret::FAMILY, Family::WithinBudgetInEveryWorld);
    assert_eq!(WithinBudget::FAMILY, Family::WithinBudgetInEveryWorld);
    for family in [
        Quotient::FAMILY,
        ObserverCheck::FAMILY,
        Violation::FAMILY,
        Refusal::FAMILY,
        FeatureSets::FAMILY,
        Collision::FAMILY,
    ] {
        assert_eq!(family, Family::AllCandidates);
    }
    // A collision is one replayed pair of charts: existence, weak, set-level.
    assert_eq!(Collision::QUESTION, QuestionKind::Existence);
    assert_eq!(Collision::CERTIFICATE, CertificateKind::Weak);
    assert_eq!(Collision::SHAPE, Shape::SetLevel);
}

#[test]
fn ordered_answers_are_literal_filters_and_witnesses_are_set_level() {
    // Counts, ties and ranked witnesses keep the original ordered candidates.
    assert_eq!(Common::SHAPE, Shape::LiteralFilter);
    assert_eq!(ZeroRegret::SHAPE, Shape::LiteralFilter);
    assert_eq!(WithinBudget::SHAPE, Shape::LiteralFilter);
    assert_eq!(Quotient::SHAPE, Shape::LiteralFilter);
    // Existence witnesses and refusals name one pair or one probe.
    assert_eq!(ObserverCheck::SHAPE, Shape::SetLevel);
    assert_eq!(Violation::SHAPE, Shape::SetLevel);
    assert_eq!(Refusal::SHAPE, Shape::SetLevel);
    // Feature-set verification checks membership independently of list order.
    assert_eq!(FeatureSets::SHAPE, Shape::SetLevel);
    // The quotient chart's list is the raw chart's list.
    assert_eq!(Quotient::CERTIFICATE, CertificateKind::ExactReplay);
    // The common-winner restriction preserves the ordered common optima
    // (MetaCommon.restrict_unfold_optimal). Zero regret holds exactly when
    // every step has zero slack (MetaRobust.zero_regret_iff_tight).
    for kind in [
        Common::CERTIFICATE,
        ZeroRegret::CERTIFICATE,
        WithinBudget::CERTIFICATE,
    ] {
        assert_eq!(kind, CertificateKind::Strict);
    }
    // Ranked witnesses list every common optimum in order.
    assert!(Common::QUESTIONS.contains(&QuestionKind::OrderedMinimizers));
    // One replayed witness answers existence; the smallest sufficient feature sets
    // drop every larger set as strictly worse.
    assert_eq!(Violation::CERTIFICATE, CertificateKind::Weak);
    assert_eq!(Refusal::CERTIFICATE, CertificateKind::Weak);
    assert_eq!(FeatureSets::CERTIFICATE, CertificateKind::Strict);
}
