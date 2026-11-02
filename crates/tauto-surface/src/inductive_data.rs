//! `inductive struct` and `inductive enum`: a program's type that the proofs
//! see too. The program runs it as the `struct` or `enum` it wrote; the
//! kernel is given the inductive family of the same shape ([`family`]) and
//! checks it as it checks an `inductive`, so no rule is added to the kernel
//! (`crates/tauto/src/read/runtime.rs`, `docs/design/program-data.md`).
use crate::surface::{Constructor, DataDecl, Generates, InductiveDecl, SurfaceTerm, TermKind};
use tauto_parol::Span;

/// The kind written before `struct` or `enum` that makes it a family.
pub const KIND: &str = "inductive";

pub fn is_inductive(d: &DataDecl) -> bool {
    d.kind.as_deref() == Some(KIND)
}

/// The name of the one constructor of a `struct` read as a family: programs
/// and proofs build it by its fields (`Pt { x: 1 }`).
pub fn struct_constructor(name: &str) -> String {
    format!("{name}::Mk")
}

/// The inductive family of `d`, a `struct` (`is_struct`) or an `enum`: a
/// positional field is `_0`, `_1`, …, and a struct's one constructor is
/// [`struct_constructor`]. The kernel reads the prelude's shared data this
/// way too. It makes nothing besides the eliminators.
pub fn family(d: &DataDecl, is_struct: bool) -> InductiveDecl {
    let span = d.span;
    let ty = |n: &str| SurfaceTerm::var(n, span);
    let result = if d.generics.is_empty() {
        ty(&d.name)
    } else {
        SurfaceTerm::app(&d.name, d.generics.iter().map(|g| ty(g)).collect(), span)
    };
    InductiveDecl {
        vis: Default::default(),
        name: d.name.clone(),
        params: d.generics.iter().map(|g| (g.clone(), ty("Type"))).collect(),
        sort: ty("Type"),
        constructors: d
            .constructors
            .iter()
            .map(|c| Constructor {
                name: if is_struct {
                    struct_constructor(&d.name)
                } else {
                    c.name.clone()
                },
                implicit: 0,
                params: c
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, (n, t))| (n.clone().unwrap_or(format!("_{i}")), t.clone()))
                    .collect(),
                result: result.clone(),
            })
            .collect(),
        generates: Generates {
            items: Vec::new(),
            written: false,
            at: Span::new(span.end, span.end),
            breaks: true,
        },
        span,
    }
}

/// The proof side's family of a program's type that has another name: the
/// inverse of extraction's table (`crates/tauto/src/extract.rs`).
pub fn proof_type(name: &str) -> Option<&'static str> {
    Some(match name {
        "nat" => "Nat",
        "u8" => "U8",
        "u32" => "U32",
        "u64" => "U64",
        "i32" => "I32",
        "i64" => "I64",
        _ => return None,
    })
}

/// Why `d`, written `inductive struct` (`is_struct`) or `inductive enum`,
/// cannot be given to the kernel; empty when it can. What is left (a field
/// whose type the kernel does not have, a nested use of the type itself) the
/// kernel reports when it checks the family.
pub fn problems(d: &DataDecl, is_struct: bool) -> Vec<(String, Span)> {
    let keyword = if is_struct { "struct" } else { "enum" };
    let what = format!("`inductive {keyword} {}`", d.name);
    let mut out = Vec::new();
    if d.host {
        out.push((
            format!("{what} is a host's type; the kernel has no definition of it"),
            d.span,
        ));
    }
    if !d.row_parameters(&Default::default()).is_empty() {
        out.push((
            format!("{what} has a row parameter; only the rows of functions mention one, and a family holds no function"),
            d.span,
        ));
    }
    for c in &d.constructors {
        for (i, (n, ty)) in c.fields.iter().enumerate() {
            let mut function = false;
            crate::surface::walk::term(&mut ty.clone(), &mut |t| {
                if let TermKind::Pi { .. } = &*t.kind {
                    function = true;
                }
            });
            if function {
                let field = n.clone().unwrap_or_else(|| i.to_string());
                out.push((
                    format!(
                        "{what}: the field `{field}` holds a function; a family holds data, and the kernel would read a function without its effects"
                    ),
                    ty.span,
                ));
            }
        }
    }
    out
}
