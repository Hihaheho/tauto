//! How a value may be used and how an arm may resume: the kinds, the
//! quantities of continuations, and the widths of integers, as the checker
//! and every later stage name them.

use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Width {
    W8,
    W16,
    W32,
    W64,
    U8,
    U16,
    U32,
    U64,
    /// The unsigned integer of the machine the program runs on (`uhost`):
    /// its operations are host effects, and it holds what the target's
    /// word holds, at most 2^64 - 1.
    Host,
    Nat,
}

impl Width {
    pub fn fits(self, n: i128) -> bool {
        match self {
            Width::W8 => i8::try_from(n).is_ok(),
            Width::W16 => i16::try_from(n).is_ok(),
            Width::W32 => i32::try_from(n).is_ok(),
            Width::W64 => i64::try_from(n).is_ok(),
            Width::U8 => u8::try_from(n).is_ok(),
            Width::U16 => u16::try_from(n).is_ok(),
            Width::U32 => u32::try_from(n).is_ok(),
            Width::U64 => u64::try_from(n).is_ok(),
            // A literal of `uhost` fits every target's word: below 2^32. A larger
            // number goes through the effect `uhost_of_u64`.
            Width::Host => u32::try_from(n).is_ok(),
            Width::Nat => n >= 0,
        }
    }
}

/// How freely a value may be copied and dropped: `copy ⊑ shared ⊑ affine ⊑
/// linear`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Kind {
    Copy,
    Shared,
    Affine,
    Linear,
}

impl Kind {
    pub fn join(self, other: Kind) -> Kind {
        self.max(other)
    }

    /// Copied and dropped freely: `copy` or `shared`.
    pub fn dup(self) -> bool {
        self <= Kind::Shared
    }

    pub fn parse(word: &str) -> Option<Kind> {
        Some(match word {
            "copy" => Kind::Copy,
            "shared" => Kind::Shared,
            "affine" => Kind::Affine,
            "linear" => Kind::Linear,
            _ => return None,
        })
    }

    /// `(k₁)->k₂`, the bound of a type constructor variable: what it takes
    /// and what it makes.
    pub fn parse_ctor(word: &str) -> Option<(Kind, Kind)> {
        let rest = word.strip_prefix('(')?;
        let (arg, result) = rest.split_once(")->")?;
        Some((Kind::parse(arg)?, Kind::parse(result)?))
    }

    /// `self` may stand where `bound` is expected; the two duplicable kinds
    /// differ only in their run-time cost.
    pub fn fits(self, bound: Kind) -> bool {
        self <= bound || (self.dup() && bound.dup())
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Kind::Copy => "copy",
            Kind::Shared => "shared",
            Kind::Affine => "affine",
            Kind::Linear => "linear",
        })
    }
}

/// How many times an arm may call its continuation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Quant {
    /// `resume 0`: the arm has no `k`.
    Zero,
    /// `resume <=1`, the default.
    AtMostOne,
    /// `resume 1`.
    One,
    /// `resume ω`.
    Many,
    /// `direct`: the arm continues with `k(e)` at the end of every path.
    Direct,
}

impl Quant {
    pub fn parse(written: &str) -> Option<Quant> {
        Some(match written {
            "0" => Quant::Zero,
            "<=1" => Quant::AtMostOne,
            "1" => Quant::One,
            "ω" => Quant::Many,
            "direct" => Quant::Direct,
            _ => return None,
        })
    }

    /// The kind of `k`: `<=1` an affine function, `1` a linear one, `ω` a
    /// duplicable one.
    pub fn continuation_kind(self) -> Kind {
        match self {
            Quant::Zero | Quant::AtMostOne => Kind::Affine,
            Quant::One | Quant::Direct => Kind::Linear,
            Quant::Many => Kind::Shared,
        }
    }
}

impl fmt::Display for Quant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Quant::Zero => "0",
            Quant::AtMostOne => "<=1",
            Quant::One => "1",
            Quant::Many => "ω",
            Quant::Direct => "direct",
        })
    }
}
