fn best_pair(bag: &[u64]) -> Option<(u64, Option<u64>)> {
    bag.iter().rev().copied().fold(None, |state, x| {
        Some(match state {
            None => (x, None),
            Some((low, None)) => (x.min(low), Some(x.max(low))),
            Some((low, Some(runner))) => (
                x.min(low.min(runner)),
                Some(x.max(low.min(runner)).min(low.max(runner))),
            ),
        })
    })
}

/// Keep a runner-up only if it ties now or can tie under the declared floor.
pub(super) fn floor_windowed_two_best(ceiling: u64, bag: &[u64]) -> Vec<u64> {
    let Some((low, runner)) = best_pair(bag) else {
        return Vec::new();
    };
    std::iter::once(low)
        .chain(runner.filter(|&r| r <= ceiling.max(low)))
        .collect()
}

/// Keep distinct scores at or below the target and the least higher score
/// if it strictly beats the best lower score. Ties favor the lower score.
pub(super) fn mirror_window(target: u64, bag: &[u64]) -> Vec<u64> {
    let mut below: Vec<_> = bag.iter().copied().filter(|&x| x <= target).collect();
    below.sort_unstable();
    below.dedup();
    let high = bag.iter().copied().filter(|&x| x > target).min();
    if let Some(high) =
        high.filter(|&high| below.last().is_none_or(|&low| high - target < target - low))
    {
        below.push(high);
    }
    below
}
