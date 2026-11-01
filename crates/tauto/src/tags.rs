//! Tag sets, mirroring `lean/Proto/Tags.lean`: equality is extensional, so
//! order and duplicates do not matter.

use std::collections::BTreeSet;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TagSet(BTreeSet<String>);

impl TagSet {
    pub fn new<I, S>(tags: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self(tags.into_iter().map(Into::into).collect())
    }

    pub fn contains(&self, tag: &str) -> bool {
        self.0.contains(tag)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn order_and_duplicates_are_irrelevant() {
        assert_eq!(TagSet::new(["a", "b", "a"]), TagSet::new(["b", "a"]));
    }
}
