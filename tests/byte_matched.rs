use std::array::from_ref;
use zeno_adp::compiled::Matched;

#[test]
fn standalone_matched_literals_keep_byte_inference() {
    let empty_span = 0..0;
    let empty = Matched {
        inputs: [&[]],
        parent: from_ref(&empty_span),
        children: &[],
    };
    assert!(empty.inputs[0].is_empty());
    let one_span = 0..1;
    let one = Matched {
        inputs: [&[1]],
        parent: from_ref(&one_span),
        children: &[],
    };
    assert_eq!(std::mem::size_of_val(&one.inputs[0][0]), 1);
}

#[test]
fn typed_matched_literal_accepts_nonbyte_tokens() {
    let one_span = 0..1;
    let matched: zeno_adp::compiled::TokenMatched<'_, 1, char> = zeno_adp::compiled::TokenMatched {
        inputs: [&['a']],
        parent: from_ref(&one_span),
        children: &[],
    };
    assert_eq!(matched.inputs[0], ['a']);
}
