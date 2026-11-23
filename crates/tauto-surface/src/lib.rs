pub mod direct;
pub mod generated;
pub mod identity;
pub mod inductive_data;
pub mod kinds;
pub mod macros;
pub mod nibstd;
pub mod records;
pub mod suggest;
pub mod surface;

pub mod diagnostic;

/// The name of the record that carries a constructor pattern's implicit
/// arguments written by name (`C<n: m>(…)`), as its first argument. It holds
/// `@`, so no source can name it.
pub const IMPLICITS: &str = "@implicits";

/// The field of the implicit record that carries the `i`-th argument of the
/// class in `C(T)::m(…)`: the class's parameters lead the method's generics,
/// so the field names the generic by its place. It holds `@`, so no source
/// can write it.
pub fn class_argument(i: usize) -> String {
    format!("@class{i}")
}

/// The place of the class argument a field of the implicit record names
/// ([`class_argument`]), if it names one.
pub fn class_argument_index(field: &str) -> Option<usize> {
    field.strip_prefix("@class")?.parse().ok()
}

/// What is read of `C(T)::m` when no call follows it.
pub const CLASS_MEMBER_NOT_CALLED: &str = "`C(T)::m` names the method `m` of the instance of `C` for `T`, and is called: write `C(T)::m(…)`";
/// What is read of `e::m` when `e` is not a class with its arguments.
pub const CLASS_MEMBER_NOT_CLASS: &str = "`::m` after `(…)` names the method `m` of a class with its arguments, as in `C(T)::m(…)`";

pub mod bindings;
pub mod checker;
pub mod resolve;

pub mod sources;
pub mod span;
