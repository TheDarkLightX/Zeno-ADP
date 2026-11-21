use zeno_adp::{Chart, Operator, Rule};

pub const RANKS: usize = 4;

/// Two leaves, an absent rank, two uses of a repeated child, and a rule
/// referencing the absent rank. IDs are unique within the fixture.
pub fn fixture<O: Operator>(root: usize, mut op: impl FnMut(usize, usize, usize) -> O) -> Chart<O> {
    let mut rule =
        |id, group, children: &[usize]| Rule::new(op(id, group, children.len()), children);
    Chart::new(
        vec![
            vec![rule(0, 0, &[]), rule(1, 1, &[])],
            vec![],
            vec![rule(2, 2, &[]), rule(3, 2, &[0]), rule(4, 2, &[0, 0])],
            vec![rule(5, 3, &[1]), rule(6, 3, &[2]), rule(7, 3, &[2, 0])],
        ],
        root,
    )
    .unwrap()
}

pub fn at<O: Operator>(chart: &Chart<O>, cell: usize) -> Chart<O> {
    Chart::new(chart.cells().to_vec(), cell).unwrap()
}

pub fn assignments<T: Copy>(values: [T; 3]) -> impl Iterator<Item = [T; RANKS]> {
    (0..values.len().pow(RANKS as u32)).map(move |mut index| {
        std::array::from_fn(|_| {
            let value = values[index % values.len()];
            index /= values.len();
            value
        })
    })
}
