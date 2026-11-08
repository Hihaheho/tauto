//! Standalone JavaScript modules from checked NIR.
use tauto_nir::*;

/// Node host services and permission parsing for generated entry modules.
pub const NODE_OPTIONS: &str = include_str!("node_options.js");
mod borrowed_returns;

/// The functions of `Float` and `Float32` (`std/prelude/Num.taut`): pure, and computed by
/// `pureBuiltin` (`builtins.js`) with `float.js`.
pub(crate) const FLOAT_BUILTINS: &[&str] = &[
    "Float::of_i64",
    "I64::of_float",
    "Float::of_text",
    "Text::of_float",
    "Float::bits",
    "Float::of_bits",
    "Float::is_nan",
    "Float::abs",
    "Float::floor",
    "Float::ceil",
    "Float::trunc",
    "Float::round",
    "Float::sqrt",
    "Float::cbrt",
    "Float::exp",
    "Float::ln",
    "Float::log2",
    "Float::log10",
    "Float::pow",
    "Float::sin",
    "Float::cos",
    "Float::tan",
    "Float::asin",
    "Float::acos",
    "Float::atan",
    "Float::atan2",
    "Float::sinh",
    "Float::cosh",
    "Float::tanh",
    "Float32::of_float",
    "Float::of_float32",
    "Float32::bits",
    "Float32::of_bits",
    "Float32::is_nan",
    "Float32::abs",
    "Float32::floor",
    "Float32::ceil",
    "Float32::trunc",
    "Float32::round",
    "Float32::sqrt",
    "Float32::cbrt",
    "Float32::exp",
    "Float32::ln",
    "Float32::log2",
    "Float32::log10",
    "Float32::pow",
    "Float32::sin",
    "Float32::cos",
    "Float32::tan",
    "Float32::asin",
    "Float32::acos",
    "Float32::atan",
    "Float32::atan2",
    "Float32::sinh",
    "Float32::cosh",
    "Float32::tanh",
];
mod chunks;
mod cps;
mod declarations;
mod direct;
mod shake;
mod syntax;
mod tail_calls;
pub use cps::{Modules, Options, generate, generate_modules, generate_with};
pub use declarations::{generate_declarations, generate_declarations_with};
type R<T> = Result<T, String>;
fn quote(s: &str) -> String {
    serde_json::to_string(s).unwrap()
}
fn unsupported<T>(what: impl Into<tauto_message::Message>) -> R<T> {
    Err(tauto_message::msg!("jsgen-unsupported", what = what.into()).to_string())
}
fn bounds(w: Width) -> String {
    let (min, max) = match w {
        // A `nat` has no largest value.
        Width::Nat => return "0n,Infinity".into(),
        Width::W32 => (i32::MIN as i128, i32::MAX as i128),
        Width::W64 => (i64::MIN as i128, i64::MAX as i128),
        Width::U8 => (0, u8::MAX as i128),
        Width::U32 => (0, u32::MAX as i128),
        Width::U64 => (0, u64::MAX as i128),
    };
    format!("{min}n,{max}n")
}

/// Runtime data symbols are assigned by the package's declaration table.
/// Unique public names keep the host representation; collisions use table slots.
/// The bundled representations retain the symbols used by runtime primitives.
pub fn owner_symbol(pkg: &Package, name: &Name) -> String {
    if tauto::bindings::is_library(&name, name.as_str()) {
        return name.to_string();
    }
    let index = pkg
        .datas
        .iter()
        .position(|data| data.name == *name)
        .expect("a constructor's owner belongs to its package");
    if tauto::bindings::library_reference(name.as_str()).is_none()
        && pkg
            .datas
            .iter()
            .filter(|data| data.name.as_str() == name.as_str())
            .count()
            == 1
    {
        name.to_string()
    } else {
        format!("@data:{index}")
    }
}

/// The library's constructors use the tags produced by runtime primitives.
/// Other declarations keep their package owner and constructor label.
pub fn constructor_symbol<'a>(pkg: &'a Package, name: &'a Name) -> &'a str {
    if tauto::bindings::is_library(name, name.as_str()) {
        name.strip_suffix("::Mk")
            .unwrap_or_else(|| name.rsplit("::").next().unwrap())
    } else if tauto::bindings::library_reference(name.as_str()).is_some() {
        name.as_str()
    } else if let Some(data) = pkg.datas.iter().find(|data| {
        data.is_struct
            && data
                .ctors
                .iter()
                .any(|constructor| constructor.name == *name)
    }) {
        data.name.as_str()
    } else {
        name.rsplit("::").next().unwrap()
    }
}

pub(crate) fn operation_symbol(pkg: &Package, name: &Name) -> String {
    if tauto::bindings::is_library(&name, name.as_str()) {
        return name.to_string();
    }
    let operation = pkg
        .ops
        .iter()
        .find(|operation| operation.name == *name)
        .expect("an operation belongs to its package");
    format!("@operation:{}", operation.id)
}

#[cfg(test)]
mod identity_tests {
    use super::*;

    #[test]
    fn data_symbols_preserve_unique_host_names_and_separate_colliding_ids() {
        let data = |name: Name| tauto_nir::DataDef {
            name,
            generics: Vec::new(),
            kind: tauto_nir::Kind::Shared,
            is_struct: false,
            ctors: Vec::new(),
            clone: true,
            copy: false,
            linear: false,
            view: false,
            host: false,
        };
        let first = Name::Global(tauto::identity::DeclRef::fresh("Shape"));
        let second = Name::Global(tauto::identity::DeclRef::fresh("Shape"));
        let foreign_list = Name::Global(tauto::identity::DeclRef::fresh("List"));
        let mut pkg = Package {
            datas: vec![data(first.clone())],
            ..Package::default()
        };
        assert_eq!(owner_symbol(&pkg, &first), "Shape");
        pkg.datas.push(data(second.clone()));
        assert_ne!(owner_symbol(&pkg, &first), owner_symbol(&pkg, &second));
        pkg.datas.push(data(foreign_list.clone()));
        assert_ne!(owner_symbol(&pkg, &foreign_list), "List");
    }

    #[test]
    fn runtime_constructor_tags_require_the_library_identity() {
        let some = tauto::bindings::library_name("Some");
        assert_eq!(constructor_symbol(&Package::default(), &some), "Some");
        let foreign = Name::Global(tauto::identity::DeclRef::fresh(some.as_str()));
        assert_eq!(
            constructor_symbol(&Package::default(), &foreign),
            some.as_str()
        );
        assert_ne!(
            constructor_symbol(&Package::default(), &foreign),
            constructor_symbol(&Package::default(), &some)
        );
        assert_eq!(
            constructor_symbol(
                &Package::default(),
                &tauto::bindings::library_name("Pair::Mk")
            ),
            "Pair"
        );
    }
}
