use zeno_adp::algebras::Count;
use zeno_adp::{compiled, compiled_grammar, tabulate_cells, Chart, Operator, Rule};

#[derive(Clone)]
struct Leaf;

impl Operator for Leaf {
    fn arity(&self) -> usize {
        0
    }
}

fn enabled() -> bool {
    true
}

compiled_grammar! {
    fn grammar(enabled: u8) -> Leaf {
        prefix |tokens, start, end|;
        empty Base => Ok(enabled().then_some(Leaf));
    }
    with fn count: Count = {
        let _: &[u8] = enabled;
        Count
    };
}

#[test]
fn grammar_parameter_label_does_not_shadow_a_caller_item_in_a_clause() {
    let reference = Chart::new(vec![vec![Rule::new(Leaf, [])]], 0).unwrap();
    let program = grammar(&[]).unwrap();
    let paired = count(&[]).unwrap();
    assert_eq!(paired, compiled::tabulate(&program, &Count).unwrap());
    assert_eq!(paired.cells(), [Some(1)]);
    assert_eq!(tabulate_cells(&reference, &Count).unwrap(), [vec![1]]);
}
