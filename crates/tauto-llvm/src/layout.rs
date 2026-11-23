//! How a value of each type is laid out.
//!
//! A value is a row of 64-bit words, and a type says how many: a number, a
//! `Bool`, a borrow and a shown text are one word; `Unit` is none; a
//! product is its members one after another; a type with constructors is a
//! word for which constructor it is, then room for the largest
//! constructor's fields one after another. A field stored behind an
//! indirection (`Indirect`) is one word: the address of a box, whose first
//! word counts the values that share it and whose other words are the
//! field. Nothing else is on the heap, and every word a constructor does
//! not use is zero, so two values of a type with no box in it are equal
//! when their words are.

use tauto_nir::ownership::subst;
use tauto_nir::*;

use crate::{R, refuse};

/// A value of one word.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Scalar {
    /// A number of the width given: its bits and whether it is signed. The
    /// word holds it extended to 64 bits.
    Int(u32, bool),
    Bool,
    /// The address of the value a borrow stands for.
    Borrow,
    /// The address of a text ended with a zero byte, which the value owns.
    Shown,
    /// The address of a `Text`'s box: a count of the values that share it,
    /// the number of bytes, then the bytes, ended with a zero byte.
    Text,
    /// The address of a function value's box: a count of the values that
    /// share it, the number of its function, then what it captured.
    Fn,
    /// The address of a `Vec`'s header, which the value owns: the address of
    /// its elements, how many there are and how many there is room for. The
    /// elements are rows of the words of one element.
    Vec,
    /// The address of the header of a `Slots`, which the value owns: the
    /// address of its elements, the capacity, the address of its flags, the
    /// address of its marks, then the words of its state.
    Slots,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: Option<String>,
    pub ty: Ty,
    pub indirect: Indirect,
}

#[derive(Debug, Clone)]
pub struct Ctor {
    /// The name `show` writes.
    pub name: String,
    pub fields: Vec<Field>,
}

#[derive(Debug, Clone)]
pub enum Shape {
    Scalar(Scalar),
    Unit,
    /// A product of two members (`Pair`), with no word for a constructor.
    Pair(Field, Field),
    /// A type with constructors: the first word says which.
    Sum {
        ctors: Vec<Ctor>,
        /// A `struct`: `show` writes the type's name, not the constructor's.
        is_struct: bool,
    },
}

pub fn int(w: Width) -> R<(u32, bool)> {
    Ok(match w {
        Width::W8 => (8, true),
        Width::W16 => (16, true),
        Width::W32 => (32, true),
        Width::W64 => (64, true),
        Width::U8 => (8, false),
        Width::U16 => (16, false),
        Width::U32 => (32, false),
        Width::U64 | Width::Host => (64, false),
        // A `Nat` is one 64-bit word like a `u64`: the program stops when a
        // result does not fit, and a number beyond 64 bits is refused.
        Width::Nat => (64, false),
    })
}

fn field(ty: &Ty) -> Field {
    Field {
        name: None,
        ty: ty.clone(),
        indirect: Indirect::None,
    }
}

fn short(name: &Name) -> String {
    let n = display_name(name);
    n.rsplit("::").next().unwrap_or(n).to_string()
}

pub fn shape(pkg: &Package, t: &Ty) -> R<Shape> {
    Ok(match t {
        Ty::Int(w) => {
            let (bits, signed) = int(*w)?;
            Shape::Scalar(Scalar::Int(bits, signed))
        }
        Ty::Bool => Shape::Scalar(Scalar::Bool),
        Ty::Unit | Ty::Never => Shape::Unit,
        Ty::Ref(a) | Ty::RefMut(a) => match &**a {
            Ty::Slice(_) => return refuse("a `Slice`"),
            _ => Shape::Scalar(Scalar::Borrow),
        },
        Ty::Shown => Shape::Scalar(Scalar::Shown),
        Ty::Pair(a, b) => Shape::Pair(field(a), field(b)),
        Ty::Option(a) => Shape::Sum {
            ctors: vec![
                Ctor {
                    name: "None".into(),
                    fields: Vec::new(),
                },
                Ctor {
                    name: "Some".into(),
                    fields: vec![field(a)],
                },
            ],
            is_struct: false,
        },
        Ty::Result(a, b) => Shape::Sum {
            ctors: vec![
                Ctor {
                    name: "Ok".into(),
                    fields: vec![field(a)],
                },
                Ctor {
                    name: "Err".into(),
                    fields: vec![field(b)],
                },
            ],
            is_struct: false,
        },
        Ty::Data(name, args) => {
            let Some(d) = pkg.datas.iter().find(|d| &d.name == name) else {
                return refuse(format!("the type `{}`", display_name(name)));
            };
            if d.host {
                return refuse("an extern type (the native backend has no host)");
            }
            if d.linear {
                return refuse("a `linear` type");
            }
            if d.generics.len() != args.len() {
                return refuse(format!(
                    "the type `{}` without all its arguments",
                    display_name(name)
                ));
            }
            Shape::Sum {
                ctors: d
                    .ctors
                    .iter()
                    .map(|c| Ctor {
                        name: if d.is_struct {
                            d.shown.clone()
                        } else {
                            short(&c.name)
                        },
                        fields: c
                            .fields
                            .iter()
                            .map(|f| Field {
                                name: f.name.clone(),
                                ty: subst(&f.ty, &d.generics, args),
                                indirect: f.indirect,
                            })
                            .collect(),
                    })
                    .collect(),
                is_struct: d.is_struct,
            }
        }
        Ty::Float | Ty::Float32 => return refuse("a `Float`"),
        Ty::Text => Shape::Scalar(Scalar::Text),
        Ty::Buf => return refuse("a `Buf`"),
        // An element read through a borrow of the `Vec` would be a borrow of
        // a borrow, which a value of the backend does not stand for.
        Ty::Vec(a) if matches!(&**a, Ty::Ref(_) | Ty::RefMut(_)) => {
            return refuse("a `Vec` of borrows");
        }
        Ty::Vec(_) => Shape::Scalar(Scalar::Vec),
        Ty::Array(_) => return refuse("an `Array`"),
        Ty::Slice(_) => return refuse("a `Slice`"),
        Ty::Std(StdType::Slots, a) if a.iter().any(|t| matches!(t, Ty::Ref(_) | Ty::RefMut(_))) => {
            return refuse("a `Slots` of borrows");
        }
        Ty::Std(StdType::Slots, _) => Shape::Scalar(Scalar::Slots),
        Ty::Std(s, _) => return refuse(format!("a `{s}`")),
        Ty::Union(_) => return refuse("a union"),
        Ty::Fn(_) => Shape::Scalar(Scalar::Fn),
        Ty::SharedVar(..) => return refuse("a `var` shared with a closure"),
        Ty::Info(_) | Ty::BudgetAnswer(_) => return refuse("a `budget`"),
        Ty::Param(p) => return refuse(format!("the type parameter `{p}`")),
    })
}

/// How deep a type may hold types without an indirection: past this, a
/// type holds itself with none, and has no size.
const DEPTH: usize = 64;

/// The number of words of a value of the type.
pub fn words(pkg: &Package, t: &Ty) -> R<usize> {
    words_in(pkg, t, 0)
}

fn words_in(pkg: &Package, t: &Ty, depth: usize) -> R<usize> {
    if depth > DEPTH {
        return refuse("a type that holds itself with no indirection");
    }
    let of = |f: &Field| -> R<usize> {
        if f.indirect.is_indirect() {
            Ok(1)
        } else {
            words_in(pkg, &f.ty, depth + 1)
        }
    };
    Ok(match shape(pkg, t)? {
        Shape::Scalar(_) => 1,
        Shape::Unit => 0,
        Shape::Pair(a, b) => of(&a)? + of(&b)?,
        Shape::Sum { ctors, .. } => {
            let mut most = 0;
            for c in &ctors {
                let mut n = 0;
                for f in &c.fields {
                    n += of(f)?;
                }
                most = most.max(n);
            }
            1 + most
        }
    })
}

/// The word a field starts at in a value: after the constructor's word of
/// a type with constructors, and after the fields before it.
pub fn offset(pkg: &Package, tagged: bool, fields: &[Field], index: usize) -> R<usize> {
    let mut at = usize::from(tagged);
    for f in &fields[..index] {
        at += if f.indirect.is_indirect() {
            1
        } else {
            words(pkg, &f.ty)?
        };
    }
    Ok(at)
}

/// Whether a value of the type holds nothing on the heap: copying its
/// words copies it, and dropping it does nothing.
pub fn plain(pkg: &Package, t: &Ty) -> R<bool> {
    plain_in(pkg, t, 0)
}

fn plain_in(pkg: &Package, t: &Ty, depth: usize) -> R<bool> {
    if depth > DEPTH {
        return refuse("a type that holds itself with no indirection");
    }
    let of = |f: &Field| -> R<bool> {
        Ok(!f.indirect.is_indirect() && plain_in(pkg, &f.ty, depth + 1)?)
    };
    Ok(match shape(pkg, t)? {
        Shape::Scalar(Scalar::Shown | Scalar::Text | Scalar::Fn | Scalar::Vec | Scalar::Slots) => {
            false
        }
        Shape::Scalar(_) | Shape::Unit => true,
        Shape::Pair(a, b) => of(&a)? && of(&b)?,
        Shape::Sum { ctors, .. } => {
            for c in &ctors {
                for f in &c.fields {
                    if !of(f)? {
                        return Ok(false);
                    }
                }
            }
            true
        }
    })
}
