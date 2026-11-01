//! The distributed index: each user's or organization's own record of the
//! revisions it observed and its judgement of them, in Git, read here into
//! checked facts for the core in `totes/index`.

pub mod checkpoint;
pub mod ledger;
pub mod policy;
pub mod state;
pub mod strict;
pub mod user;
