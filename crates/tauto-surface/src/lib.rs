pub mod direct;
pub mod generated;
pub mod identity;
pub mod inductive_data;
pub mod macros;
pub mod nibstd;
pub mod suggest;
pub mod surface;
pub mod syntax;

pub mod diagnostic;

/// The name of the record that carries a constructor pattern's implicit
/// arguments written by name (`C<n: m>(…)`), as its first argument. It holds
/// `@`, so no source can name it.
pub const IMPLICITS: &str = "@implicits";
