use zeno_adp::compiled::Program;

trait LayoutHint {
    fn parallel_layout(&self) -> usize;
}

impl<T: Program> LayoutHint for T {
    fn parallel_layout(&self) -> usize {
        self.cell_count()
    }
}

fn layout<T: Program>(program: &T) -> usize {
    program.parallel_layout()
}

#[test]
fn internal_layout_dispatch_leaves_downstream_methods_available() {
    let source = zeno_adp::grammars::alignment_source(b"A", b"T").unwrap();
    assert_eq!(layout(&source), 4);
}
