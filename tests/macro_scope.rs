use zeno_adp::algebras::Count;
use zeno_adp::{compiled, compiled_grammar, Operator};

const PREFIX: bool = false;

#[derive(Clone)]
struct Leaf;

impl Operator for Leaf {
    fn arity(&self) -> usize {
        0
    }
}

compiled_grammar! {
    fn maybe_leaf(input: u8) -> Leaf {
        prefix |input, start, end|;
        empty Guarded => Ok(PREFIX.then_some(Leaf));
    }
    with fn count: Count = Count;
}

#[test]
fn false_caller_constant_keeps_the_cell_absent() {
    let program = maybe_leaf(&[]).unwrap();
    assert_eq!(count(&[]).unwrap().cells(), [None]);
    assert!(compiled::reference_chart(&program).unwrap().cells()[0].is_empty());
}
