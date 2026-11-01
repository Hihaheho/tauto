//! Capture rows: an upper bound of the levels in the frontier of a value.

use std::collections::BTreeSet;

use super::levels::LevelVar;

/// A variable standing for a set of levels.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RowVar(pub u32);

/// `{levels} ∪ row variables`, or `Unknown`. `Unknown` is not the empty row: it
/// stands for a frontier nothing is known about, and no level precedes it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CaptureRow {
    pub levels: BTreeSet<LevelVar>,
    pub vars: BTreeSet<RowVar>,
    pub unknown: bool,
}

impl CaptureRow {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn unknown() -> Self {
        Self {
            unknown: true,
            ..Self::default()
        }
    }

    pub fn level(l: LevelVar) -> Self {
        Self {
            levels: BTreeSet::from([l]),
            ..Self::default()
        }
    }

    pub fn var(v: RowVar) -> Self {
        Self {
            vars: BTreeSet::from([v]),
            ..Self::default()
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        Self {
            levels: self.levels.union(&other.levels).copied().collect(),
            vars: self.vars.union(&other.vars).copied().collect(),
            unknown: self.unknown || other.unknown,
        }
    }
}
