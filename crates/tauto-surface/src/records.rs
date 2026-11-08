//! Records without a name: the type `{ a: A, b: B }` and the value `#{ a: x, b: y }`.
//!
//! A record is the struct `@record.a.b`, one for each set of field names: its
//! generics are the fields' types, in the order of the names, so
//! `{ a: A, b: B }` is `@record.a.b(A, B)` and `{ b: B, a: A }` is the same
//! type. Two records are the same type when they have the same names with the
//! same types; the order the fields are written in is not part of the type.
//! The `@` keeps the struct apart from every name a program writes.
//!
//! The reader writes the type and the value with the struct's name
//! (`surface::Reader::record_type`, `surface::Reader::anon_record`), and
//! [`declare`] adds the structs a program's statements name, once for the whole
//! program, so a record is the same type in every file.

use std::collections::BTreeSet;

use crate::identity::Name;
use crate::surface::{DataConstructor, DataDecl, Stmt, SurfaceTerm, TermKind, Vis, walk};

/// The prefix of a record's struct.
pub const PREFIX: &str = "@record.";

/// What a `#{ a: 1, ..r }` is read as: a record's fields are its type, so the
/// fields not written cannot be taken from another value.
pub const BASE_MESSAGE: &str = "`..` takes the fields from another value only in a struct with a name: write each field of a record";

/// The struct of a record whose field names are `names`, in order.
pub fn struct_name(names: &[&str]) -> String {
    format!("{PREFIX}{}", names.join("."))
}

/// The field names of a record's struct, `@record.a.b`.
pub fn fields_of(name: &str) -> Option<Vec<&str>> {
    let rest = name.strip_prefix(PREFIX)?;
    if rest.is_empty() || rest.contains("::") {
        return None;
    }
    Some(rest.split('.').collect())
}

/// The first name of the sorted `names` written twice.
pub fn repeated<'a>(names: &[&'a str]) -> Option<&'a str> {
    names.windows(2).find(|w| w[0] == w[1]).map(|w| w[0])
}

pub fn repeated_message(field: &str) -> String {
    format!("`{field}` is written twice in the record")
}

/// The records `stmts` name, as the names of their structs: as written, or
/// as the reference a file that was bound before names it by.
pub fn used(stmts: &mut [Stmt]) -> BTreeSet<Name> {
    let mut out = BTreeSet::new();
    for s in stmts.iter_mut() {
        walk::stmt(s, &mut |t| {
            let name = match &*t.kind {
                TermKind::Var(n) => n,
                TermKind::Record { name, .. } => name,
                _ => return,
            };
            if matches!(name, Name::Spelled(_) | Name::Global(_))
                && fields_of(name.as_str()).is_some()
            {
                out.insert(name.clone());
            }
        });
    }
    out
}

/// `pub(open) struct @record.a.b(A0, A1) { a: A0, b: A1 }`.
pub fn decl(name: &str) -> Option<Stmt> {
    decl_of(
        Name::Spelled(name.to_string()),
        Name::Spelled(name.to_string()),
    )
}

/// The struct of the record `name`, which a file bound before names by a
/// reference: the reference is the struct's, and its constructor's is derived.
fn decl_named(name: &Name) -> Option<Stmt> {
    match name {
        Name::Spelled(_) => decl(name.as_str()),
        Name::Global(r) => decl_of(name.clone(), Name::Global(r.constructor(0, name.as_str()))),
        _ => None,
    }
}

fn decl_of(name: Name, constructor: Name) -> Option<Stmt> {
    let fields = fields_of(name.as_str())?
        .into_iter()
        .map(str::to_string)
        .collect::<Vec<_>>();
    let span = tauto_parol::Span::default();
    let generics: Vec<String> = (0..fields.len()).map(|i| format!("A{i}")).collect();
    Some(Stmt::Struct(DataDecl {
        kind: None,
        name,
        vis: Vis::Open,
        generics: generics.iter().map(|g| Name::Spelled(g.clone())).collect(),
        rows: vec![false; fields.len()],
        constructors: vec![DataConstructor {
            name: constructor,
            fields: fields
                .iter()
                .zip(&generics)
                .map(|(f, g)| (Some(f.to_string()), SurfaceTerm::var(g.as_str(), span)))
                .collect(),
        }],
        host: false,
        span,
    }))
}

/// Puts the struct of each record the files name in the first of `files`
/// that names it, so that every file that reads a field of the record, a
/// dependency's among them, comes at or after the declaration. A file bound
/// before names a record by a reference of its own; each reference gets the
/// struct it names. Returns whether it added any.
pub fn declare(files: &mut [Vec<Stmt>]) -> bool {
    let mut declared: BTreeSet<Name> = files
        .iter()
        .flatten()
        .filter_map(|s| match s {
            Stmt::Struct(d) => Some(d.name.clone()),
            _ => None,
        })
        .collect();
    let mut added = false;
    for f in files.iter_mut() {
        let mut add = Vec::new();
        for n in used(f) {
            if declared.contains(&n) {
                continue;
            }
            if let Some(d) = decl_named(&n) {
                declared.insert(n);
                add.push(d);
            }
        }
        added |= !add.is_empty();
        f.extend(add);
    }
    added
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::identity::DeclRef;

    fn reading(reference: &DeclRef) -> Stmt {
        let term = SurfaceTerm::new(
            TermKind::Var(Name::Global(reference.clone())),
            tauto_parol::Span::default(),
        );
        Stmt::Expr(term)
    }

    fn struct_names(file: &[Stmt]) -> Vec<Name> {
        file.iter()
            .filter_map(|s| match s {
                Stmt::Struct(d) => Some(d.name.clone()),
                _ => None,
            })
            .collect()
    }

    // A file bound before names a record by a reference of its own; the struct is declared
    // for that reference, in the first file that names it, and only once.
    #[test]
    fn a_record_named_by_a_bound_reference_gets_its_struct() {
        let first = DeclRef::fresh("@record.body.failed");
        let second = DeclRef::fresh("@record.body.failed");
        let mut files = vec![
            vec![],
            vec![reading(&first)],
            vec![reading(&first), reading(&second)],
        ];
        assert!(declare(&mut files));
        assert!(struct_names(&files[0]).is_empty());
        assert_eq!(struct_names(&files[1]), vec![Name::Global(first.clone())]);
        assert_eq!(struct_names(&files[2]), vec![Name::Global(second.clone())]);
        assert!(!declare(&mut files));
    }
}
