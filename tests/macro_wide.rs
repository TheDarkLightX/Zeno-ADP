use zeno_adp::algebras::Count;
use zeno_adp::{compiled, compiled_grammar, tabulate_cells, Chart, Operator, Rule};

#[derive(Clone)]
struct Leaf;

impl Operator for Leaf {
    fn arity(&self) -> usize {
        0
    }
}

compiled_grammar! {
    fn wide(input: u8) -> Leaf {
        prefix |tokens, start, end|;
        empty Site000 => Ok(Some(Leaf));
        empty Site001 => Ok(Some(Leaf));
        empty Site002 => Ok(Some(Leaf));
        empty Site003 => Ok(Some(Leaf));
        empty Site004 => Ok(Some(Leaf));
        empty Site005 => Ok(Some(Leaf));
        empty Site006 => Ok(Some(Leaf));
        empty Site007 => Ok(Some(Leaf));
        empty Site008 => Ok(Some(Leaf));
        empty Site009 => Ok(Some(Leaf));
        empty Site010 => Ok(Some(Leaf));
        empty Site011 => Ok(Some(Leaf));
        empty Site012 => Ok(Some(Leaf));
        empty Site013 => Ok(Some(Leaf));
        empty Site014 => Ok(Some(Leaf));
        empty Site015 => Ok(Some(Leaf));
        empty Site016 => Ok(Some(Leaf));
        empty Site017 => Ok(Some(Leaf));
        empty Site018 => Ok(Some(Leaf));
        empty Site019 => Ok(Some(Leaf));
        empty Site020 => Ok(Some(Leaf));
        empty Site021 => Ok(Some(Leaf));
        empty Site022 => Ok(Some(Leaf));
        empty Site023 => Ok(Some(Leaf));
        empty Site024 => Ok(Some(Leaf));
        empty Site025 => Ok(Some(Leaf));
        empty Site026 => Ok(Some(Leaf));
        empty Site027 => Ok(Some(Leaf));
        empty Site028 => Ok(Some(Leaf));
        empty Site029 => Ok(Some(Leaf));
        empty Site030 => Ok(Some(Leaf));
        empty Site031 => Ok(Some(Leaf));
        empty Site032 => Ok(Some(Leaf));
        empty Site033 => Ok(Some(Leaf));
        empty Site034 => Ok(Some(Leaf));
        empty Site035 => Ok(Some(Leaf));
        empty Site036 => Ok(Some(Leaf));
        empty Site037 => Ok(Some(Leaf));
        empty Site038 => Ok(Some(Leaf));
        empty Site039 => Ok(Some(Leaf));
        empty Site040 => Ok(Some(Leaf));
        empty Site041 => Ok(Some(Leaf));
        empty Site042 => Ok(Some(Leaf));
        empty Site043 => Ok(Some(Leaf));
        empty Site044 => Ok(Some(Leaf));
        empty Site045 => Ok(Some(Leaf));
        empty Site046 => Ok(Some(Leaf));
        empty Site047 => Ok(Some(Leaf));
        empty Site048 => Ok(Some(Leaf));
        empty Site049 => Ok(Some(Leaf));
        empty Site050 => Ok(Some(Leaf));
        empty Site051 => Ok(Some(Leaf));
        empty Site052 => Ok(Some(Leaf));
        empty Site053 => Ok(Some(Leaf));
        empty Site054 => Ok(Some(Leaf));
        empty Site055 => Ok(Some(Leaf));
        empty Site056 => Ok(Some(Leaf));
        empty Site057 => Ok(Some(Leaf));
        empty Site058 => Ok(Some(Leaf));
        empty Site059 => Ok(Some(Leaf));
        empty Site060 => Ok(Some(Leaf));
        empty Site061 => Ok(Some(Leaf));
        empty Site062 => Ok(Some(Leaf));
        empty Site063 => Ok(Some(Leaf));
        empty Site064 => Ok(Some(Leaf));
        empty Site065 => Ok(Some(Leaf));
        empty Site066 => Ok(Some(Leaf));
        empty Site067 => Ok(Some(Leaf));
        empty Site068 => Ok(Some(Leaf));
        empty Site069 => Ok(Some(Leaf));
        empty Site070 => Ok(Some(Leaf));
        empty Site071 => Ok(Some(Leaf));
        empty Site072 => Ok(Some(Leaf));
        empty Site073 => Ok(Some(Leaf));
        empty Site074 => Ok(Some(Leaf));
        empty Site075 => Ok(Some(Leaf));
        empty Site076 => Ok(Some(Leaf));
        empty Site077 => Ok(Some(Leaf));
        empty Site078 => Ok(Some(Leaf));
        empty Site079 => Ok(Some(Leaf));
        empty Site080 => Ok(Some(Leaf));
        empty Site081 => Ok(Some(Leaf));
        empty Site082 => Ok(Some(Leaf));
        empty Site083 => Ok(Some(Leaf));
        empty Site084 => Ok(Some(Leaf));
        empty Site085 => Ok(Some(Leaf));
        empty Site086 => Ok(Some(Leaf));
        empty Site087 => Ok(Some(Leaf));
        empty Site088 => Ok(Some(Leaf));
        empty Site089 => Ok(Some(Leaf));
        empty Site090 => Ok(Some(Leaf));
        empty Site091 => Ok(Some(Leaf));
        empty Site092 => Ok(Some(Leaf));
        empty Site093 => Ok(Some(Leaf));
        empty Site094 => Ok(Some(Leaf));
        empty Site095 => Ok(Some(Leaf));
        empty Site096 => Ok(Some(Leaf));
        empty Site097 => Ok(Some(Leaf));
        empty Site098 => Ok(Some(Leaf));
        empty Site099 => Ok(Some(Leaf));
        empty Site100 => Ok(Some(Leaf));
        empty Site101 => Ok(Some(Leaf));
        empty Site102 => Ok(Some(Leaf));
        empty Site103 => Ok(Some(Leaf));
        empty Site104 => Ok(Some(Leaf));
        empty Site105 => Ok(Some(Leaf));
        empty Site106 => Ok(Some(Leaf));
        empty Site107 => Ok(Some(Leaf));
        empty Site108 => Ok(Some(Leaf));
        empty Site109 => Ok(Some(Leaf));
        empty Site110 => Ok(Some(Leaf));
        empty Site111 => Ok(Some(Leaf));
        empty Site112 => Ok(Some(Leaf));
        empty Site113 => Ok(Some(Leaf));
        empty Site114 => Ok(Some(Leaf));
        empty Site115 => Ok(Some(Leaf));
        empty Site116 => Ok(Some(Leaf));
        empty Site117 => Ok(Some(Leaf));
        empty Site118 => Ok(Some(Leaf));
        empty Site119 => Ok(Some(Leaf));
        empty Site120 => Ok(Some(Leaf));
        empty Site121 => Ok(Some(Leaf));
        empty Site122 => Ok(Some(Leaf));
        empty Site123 => Ok(Some(Leaf));
        empty Site124 => Ok(Some(Leaf));
        empty Site125 => Ok(Some(Leaf));
        empty Site126 => Ok(Some(Leaf));
        empty Site127 => Ok(Some(Leaf));
    }
    with fn count: Count = Count;
}

#[test]
fn wide_grammar_preserves_all_sites_under_the_default_recursion_limit() {
    // This declaration size exposed the compiler recursion regression.
    const WIDE_CLAUSES: usize = 128;
    let bound = wide(&[]).unwrap();
    let mut sites = Vec::new();
    compiled::replay(&bound, |rank, ordinal, site, _, children| {
        assert_eq!(rank, 0);
        assert_eq!(ordinal, sites.len());
        assert!(children.is_empty());
        sites.push(site.to_owned());
        Ok(())
    })
    .unwrap();
    assert_eq!(
        sites,
        (0..WIDE_CLAUSES)
            .map(|i| format!("Site{i:03}"))
            .collect::<Vec<_>>()
    );

    let reference = Chart::new(vec![vec![Rule::new(Leaf, []); WIDE_CLAUSES]], 0).unwrap();
    let expected = tabulate_cells(&reference, &Count).unwrap();
    let paired = count(&[]).unwrap();
    assert_eq!(paired, compiled::tabulate(&bound, &Count).unwrap());
    assert_eq!(paired.cells(), [Some(expected[0][0])]);
}
