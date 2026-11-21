use zeno_adp::classification::Classification;
use zeno_adp::grammars::{Align, LocalAlign};
use zeno_adp::Error;

#[derive(Clone, Copy)]
pub struct Columns;

impl Classification<LocalAlign> for Columns {
    type Class = Vec<Align>;

    fn classify(
        &self,
        operator: &LocalAlign,
        children: &[&Vec<Align>],
    ) -> Result<Vec<Align>, Error> {
        Ok(match operator {
            LocalAlign::Empty | LocalAlign::Start { .. } => Vec::new(),
            LocalAlign::End => children[0].clone(),
            LocalAlign::Column(column) => {
                let mut columns = children[0].clone();
                columns.push(*column);
                columns
            }
        })
    }
}
