use std::time::Duration;

/// A conventional median and nearest-rank 95th percentile, in seconds.
pub struct Summary {
    pub median: f64,
    pub p95: f64,
}

pub fn summarize(samples: &[Duration]) -> Option<Summary> {
    if samples.is_empty() {
        return None;
    }
    let mut sorted = samples.to_vec();
    sorted.sort();
    let middle = sorted.len() / 2;
    let median =
        (sorted[(sorted.len() - 1) / 2].as_secs_f64() + sorted[middle].as_secs_f64()) / 2.0;
    let p95 = sorted[(sorted.len() * 95).div_ceil(100) - 1].as_secs_f64();
    Some(Summary { median, p95 })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_has_no_summary() {
        assert!(summarize(&[]).is_none());
    }

    #[test]
    fn single_sample_is_both_statistics() {
        let s = summarize(&[Duration::from_millis(125)]).unwrap();
        assert_eq!(s.median, 0.125);
        assert_eq!(s.p95, 0.125);
    }

    #[test]
    fn even_median_averages_middle_values_without_mutating_samples() {
        let samples = [8, 2, 4, 1].map(Duration::from_secs);
        let s = summarize(&samples).unwrap();
        assert_eq!(s.median, 3.0);
        assert_eq!(s.p95, 8.0);
        assert_eq!(samples[0], Duration::from_secs(8));
    }

    #[test]
    fn odd_median_uses_the_middle_value() {
        let s = summarize(&[9, 1, 2].map(Duration::from_secs)).unwrap();
        assert_eq!(s.median, 2.0);
    }

    #[test]
    fn p95_uses_ceiling_rank_not_always_the_maximum() {
        let twenty: Vec<_> = (1..=20).map(Duration::from_secs).collect();
        let s = summarize(&twenty).unwrap();
        assert_eq!(s.median, 10.5);
        assert_eq!(s.p95, 19.0);
        let twenty_one: Vec<_> = (1..=21).map(Duration::from_secs).collect();
        assert_eq!(summarize(&twenty_one).unwrap().p95, 20.0);
    }
}
