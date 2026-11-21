use zeno_adp::algebras::{Additive, Cost, ScoredOperator};
use zeno_adp::{compiled, compiled_grammar, tabulate_cells, Operator};

#[derive(Clone)]
struct Leaf(&'static str);

impl Operator for Leaf {
    fn arity(&self) -> usize {
        0
    }
}

impl ScoredOperator for Leaf {
    fn cost(&self) -> Cost {
        Cost::Finite(i64::from(self.0.contains("::source::")))
    }
}

compiled_grammar! {
    fn source(input: u8) -> Leaf {
        prefix |tokens, start, end|;
        empty Context => Ok(Some(Leaf(std::any::type_name_of_val(&|| {}))));
    }
    with fn minimum: Additive = Additive::default();
}

#[test]
fn paired_evaluation_calls_the_original_callback() {
    // Two expansions of a closure can have different names even with the
    // same body. Paired evaluation should call the original closure.
    let program = source(&[]).unwrap();
    let chart = compiled::reference_chart(&program).unwrap();
    let reference = tabulate_cells(&chart, &Additive::default()).unwrap();
    let paired = minimum(&[]).unwrap();
    assert_eq!(
        paired,
        compiled::tabulate(&program, &Additive::default()).unwrap()
    );
    assert!(paired.cells()[0].iter().eq(&reference[0]));
}
