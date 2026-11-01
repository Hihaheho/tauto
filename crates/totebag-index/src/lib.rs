//! The core of the distributed index, as checked in `totes/index`, and the
//! facts read from Git given to it.

/// A message of this crate as text, for the `String` errors and reasons it
/// returns: `say!("totebag-…", name = value, …)`.
macro_rules! say {
    ($($t:tt)*) => {
        ::tauto_message::msg!($($t)*).to_string()
    };
}

pub mod engine;
pub mod explain;
pub mod facts;

pub mod core {
    include!(concat!(env!("OUT_DIR"), "/tauto_index.rs"));
}
