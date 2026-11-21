use zeno_adp::Tree;

#[test]
fn replace_root_operator_and_keep_owned_children_in_order() {
    let tree = Tree {
        operator: String::from("old root"),
        children: ["left", "right"]
            .map(|name| Tree {
                operator: String::from(name),
                children: vec![],
            })
            .into(),
    };
    let (operator, children) = tree.into_parts();
    assert_eq!(operator, "old root");
    let updated = Tree {
        operator: String::from("new root"),
        children,
    };
    assert_eq!(updated.operator, "new root");
    assert_eq!(updated.children[0].operator, "left");
    assert_eq!(updated.children[1].operator, "right");
}

#[test]
fn drop_borrowing_tree_before_mutating_its_payload_source() {
    let mut text = String::from("a");
    let tree = Tree {
        operator: text.as_str(),
        children: vec![],
    };
    assert_eq!(tree.operator, "a");
    drop(tree);
    text.push('b');
    assert_eq!(text, "ab");
}
