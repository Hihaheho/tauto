//! Where a piece of syntax is in the source.

/// A byte range of the source, end exclusive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    pub fn merge(self, other: Span) -> Span {
        if self.is_empty() && self.start == 0 {
            return other;
        }
        if other.is_empty() && other.start == 0 {
            return self;
        }
        Span::new(self.start.min(other.start), self.end.max(other.end))
    }

    pub fn is_empty(self) -> bool {
        self.start >= self.end
    }

    pub fn contains(self, offset: u32) -> bool {
        self.start <= offset && offset <= self.end
    }

    pub fn text(self, source: &str) -> &str {
        source
            .get(self.start as usize..self.end as usize)
            .unwrap_or_default()
    }
}
