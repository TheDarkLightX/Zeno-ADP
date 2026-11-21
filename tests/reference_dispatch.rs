use zeno_adp::compiled::{self, Program};

trait ClientChart {
    fn fill_reference() -> usize {
        7
    }

    fn emit_rows() -> usize {
        11
    }
}

impl<T: Program> ClientChart for T {}

fn client_chart_values<P: Program + ClientChart>(_: &P) -> (usize, usize) {
    (P::fill_reference(), P::emit_rows())
}

#[test]
fn generic_client_can_define_fill_reference() {
    zeno_adp::compiled_grammar! {
        fn empty(input: u8) -> zeno_adp::grammars::Align {
            prefix |tokens, start, end|;
            empty Start => Ok(Some(zeno_adp::grammars::Align::Start));
        }
    }
    let source = empty(b"").unwrap();
    assert_eq!(client_chart_values(&source), (7, 11));
    assert_eq!(compiled::reference_chart(&source).unwrap().cells().len(), 1);
}
