use std::ops::RangeInclusive;
use std::sync::Arc;

/// Admissible child end boundaries, stored as ascending disjoint inclusive intervals.
/// Construction discards empty ranges and coalesces overlapping or adjacent ones.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SplitEnds(Ranges);

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ranges {
    One(Option<RangeInclusive<usize>>),
    Many(Arc<[RangeInclusive<usize>]>),
}

impl Default for Ranges {
    fn default() -> Self {
        Self::One(None)
    }
}

impl SplitEnds {
    /// Normalize intervals supplied in any order. A union with no ranges admits no ends.
    pub fn new(ranges: impl IntoIterator<Item = RangeInclusive<usize>>) -> Self {
        let mut ranges: Vec<_> = ranges.into_iter().filter(|r| !r.is_empty()).collect();
        ranges.sort_unstable_by_key(|r| *r.start());
        // dedup_by passes the later range first. Keep and extend the earlier one.
        ranges.dedup_by(|next, previous| {
            if *next.start() <= previous.end().saturating_add(1) {
                *previous = *previous.start()..=(*previous.end()).max(*next.end());
                true
            } else {
                false
            }
        });
        if ranges.len() <= 1 {
            Self(Ranges::One(ranges.pop()))
        } else {
            Self(Ranges::Many(ranges.into()))
        }
    }

    /// Ascending normalized ranges. Each end belongs to at most one range.
    pub fn ranges(&self) -> &[RangeInclusive<usize>] {
        match &self.0 {
            Ranges::One(range) => range.as_slice(),
            Ranges::Many(ranges) => ranges,
        }
    }

    pub(super) fn clipped(&self, first: usize, last: usize) -> impl Iterator<Item = usize> + '_ {
        let ranges = self.ranges();
        let start = ranges.partition_point(|range| *range.end() < first);
        ranges[start..]
            .iter()
            .take_while(move |range| *range.start() <= last)
            .flat_map(move |range| first.max(*range.start())..=last.min(*range.end()))
    }
}

impl From<RangeInclusive<usize>> for SplitEnds {
    fn from(range: RangeInclusive<usize>) -> Self {
        Self(Ranges::One((!range.is_empty()).then_some(range)))
    }
}
