//! The glue of each type: the functions that drop a value, make a copy of
//! one its own, and show one, written once for each type the program does
//! that to. Each takes the address of the value.

use tauto_nir::*;

use crate::build::Body;
use crate::layout::{self, Ctor, Field, Scalar, Shape};
use crate::{Glue, Module, R, refuse};

/// Where a field of a value is.
pub struct At {
    /// The address of the field's word in the value: the field itself, or
    /// the address of its box.
    pub slot: String,
    /// The address of the field's own words.
    pub content: String,
    /// The address of the box the field is stored in.
    pub boxed: Option<String>,
}

/// Field `i` of `fields` in the value at `p`.
pub fn field_at(
    m: &Module,
    b: &mut Body,
    p: &str,
    tagged: bool,
    fields: &[Field],
    i: usize,
) -> R<At> {
    let off = layout::offset(m.pkg, tagged, fields, i)?;
    let slot = b.gep(p, off);
    if !fields[i].indirect.is_indirect() {
        return Ok(At {
            content: slot.clone(),
            slot,
            boxed: None,
        });
    }
    let w = b.def(format!("load i64, ptr {slot}"));
    let boxed = b.ptr(&w);
    let content = b.gep(&boxed, 1);
    Ok(At {
        slot,
        content,
        boxed: Some(boxed),
    })
}

/// The constructors of a type that has them, and whether a word says which
/// one a value is.
pub fn ctors(shape: Shape) -> Option<(bool, Vec<Ctor>)> {
    match shape {
        Shape::Pair(a, b) => Some((
            false,
            vec![Ctor {
                name: String::new(),
                fields: vec![a, b],
            }],
        )),
        Shape::Sum { ctors, .. } => Some((true, ctors)),
        Shape::Scalar(_) | Shape::Unit => None,
    }
}

/// Runs `each` for the constructor the value at `p` is: on its word, when
/// the type has one.
fn for_ctor(
    m: &mut Module,
    b: &mut Body,
    p: &str,
    tagged: bool,
    ctors: &[Ctor],
    each: &mut dyn FnMut(&mut Module, &mut Body, usize, &Ctor) -> R<()>,
) -> R<()> {
    if !tagged {
        return each(m, b, 0, &ctors[0]);
    }
    let tag = b.def(format!("load i64, ptr {p}"));
    let labels: Vec<String> = ctors.iter().map(|_| b.label()).collect();
    let (other, done) = (b.label(), b.label());
    let cases: Vec<String> = labels
        .iter()
        .enumerate()
        .map(|(i, l)| format!("i64 {i}, label %{l}"))
        .collect();
    b.end(format!(
        "switch i64 {tag}, label %{other} [ {} ]",
        cases.join(" ")
    ));
    for (i, c) in ctors.iter().enumerate() {
        b.start(&labels[i]);
        each(m, b, i, c)?;
        b.br(&done);
    }
    b.start(&other);
    b.end("unreachable");
    b.start(&done);
    Ok(())
}

pub fn function(m: &mut Module, g: Glue, t: &Ty) -> R<String> {
    let name = m.glue(g, t);
    let mut b = Body::new();
    let header = match g {
        Glue::Drop => {
            drop(m, &mut b, "%p", t)?;
            format!("define internal fastcc void {name}(ptr %p)")
        }
        Glue::Dup => {
            dup(m, &mut b, "%p", t)?;
            format!("define internal fastcc void {name}(ptr %p)")
        }
        Glue::Show => {
            show(m, &mut b, "%b", "%p", t)?;
            format!("define internal fastcc void {name}(ptr %b, ptr %p)")
        }
    };
    b.end("ret void");
    Ok(format!("; {g:?} of {t:?}\n{}", b.finish(&header)))
}

/// Calls the glue of `t` on the value at `p`: nothing for a type that
/// holds nothing on the heap.
pub fn call(m: &mut Module, b: &mut Body, g: Glue, p: &str, t: &Ty) -> R<()> {
    if layout::plain(m.pkg, t)? {
        return Ok(());
    }
    let f = m.glue(g, t);
    b.ins(format!("call fastcc void {f}(ptr {p})"));
    Ok(())
}

fn drop(m: &mut Module, b: &mut Body, p: &str, t: &Ty) -> R<()> {
    let shape = layout::shape(m.pkg, t)?;
    if let Shape::Scalar(Scalar::Shown) = shape {
        let w = b.def(format!("load i64, ptr {p}"));
        let s = b.ptr(&w);
        b.ins(format!("call void @rt_free(ptr {s})"));
        return Ok(());
    }
    if let Shape::Scalar(Scalar::Text) = shape {
        let w = b.def(format!("load i64, ptr {p}"));
        let s = b.ptr(&w);
        b.ins(format!("call void @rt_text_drop(ptr {s})"));
        return Ok(());
    }
    if let Shape::Scalar(Scalar::Fn) = shape {
        let w = b.def(format!("load i64, ptr {p}"));
        let s = b.ptr(&w);
        b.ins(format!("call fastcc void @fn.drop(ptr {s})"));
        return Ok(());
    }
    if let Shape::Scalar(Scalar::Vec) = shape {
        let Ty::Vec(a) = t else {
            return refuse("internal: a `Vec` that is not one");
        };
        let w = b.def(format!("load i64, ptr {p}"));
        let v = b.ptr(&w);
        let n = layout::words(m.pkg, a)?;
        drop_rows(m, b, &v, "0", n, a, 0, &Ty::Unit)?;
        b.ins(format!("call void @rt_vec_free(ptr {v})"));
        return Ok(());
    }
    if let Shape::Scalar(Scalar::Slots) = shape {
        let Ty::Std(_, args) = t else {
            return refuse("internal: a `Slots` that is not one");
        };
        let (s, mark, a) = (&args[0], &args[1], &args[2]);
        let n = layout::words(m.pkg, a)?;
        let mn = layout::words(m.pkg, mark)?;
        let w = b.def(format!("load i64, ptr {p}"));
        let h = b.ptr(&w);
        // The state, every mark and the vacant mark are owned; only flagged
        // slots hold an element.
        if !layout::plain(m.pkg, s)? {
            let sp = b.gep(&h, 5);
            call(m, b, Glue::Drop, &sp, s)?;
        }
        let capp = b.gep(&h, 1);
        let cap = b.def(format!("load i64, ptr {capp}"));
        let drop_marks = !layout::plain(m.pkg, mark)?;
        let drop_elems = !layout::plain(m.pkg, a)?;
        if drop_marks || drop_elems {
            let ip = b.alloca(1);
            b.ins(format!("store i64 0, ptr {ip}"));
            let (head, body, next, done, full) = (
                b.label(),
                b.label(),
                b.label(),
                b.label(),
                b.label(),
            );
            b.br(&head);
            b.start(&head);
            let i = b.def(format!("load i64, ptr {ip}"));
            let more = b.def(format!("icmp ult i64 {i}, {cap}"));
            b.condbr(&more, &body, &done);
            b.start(&body);
            if drop_marks {
                let mp = b.def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {i}, i64 {mn})"));
                call(m, b, Glue::Drop, &mp, mark)?;
            }
            if drop_elems {
                let fp = b.def(format!("call ptr @rt_slots_flag(ptr {h}, i64 {i})"));
                let f = b.def(format!("load i64, ptr {fp}"));
                let filled = b.def(format!("icmp ne i64 {f}, 0"));
                b.condbr(&filled, &full, &next);
                b.start(&full);
                let at = b.def(format!("call ptr @rt_slots_elem(ptr {h}, i64 {i}, i64 {n})"));
                call(m, b, Glue::Drop, &at, a)?;
                b.br(&next);
            } else {
                b.br(&next);
            }
            b.start(&next);
            let i1 = b.def(format!("add i64 {i}, 1"));
            b.ins(format!("store i64 {i1}, ptr {ip}"));
            b.br(&head);
            b.start(&done);
        }
        if drop_marks {
            let vacp = b.def(format!("call ptr @rt_slots_mark(ptr {h}, i64 {cap}, i64 {mn})"));
            call(m, b, Glue::Drop, &vacp, mark)?;
        }
        b.ins(format!("call void @rt_slots_free(ptr {h})"));
        return Ok(());
    }
    let Some((tagged, cs)) = ctors(shape) else {
        return Ok(());
    };
    for_ctor(m, b, p, tagged, &cs, &mut |m, b, _, c| {
        for (i, f) in c.fields.iter().enumerate() {
            let plain = layout::plain(m.pkg, &f.ty)?;
            if f.indirect == Indirect::None && plain {
                continue;
            }
            let at = field_at(m, b, p, tagged, &c.fields, i)?;
            match (f.indirect, &at.boxed) {
                (Indirect::Shared, Some(boxed)) => {
                    // The last value that shares the box releases it.
                    let rc = b.def(format!("load i64, ptr {boxed}"));
                    let last = b.def(format!("icmp eq i64 {rc}, 1"));
                    let (free, keep, done) = (b.label(), b.label(), b.label());
                    b.condbr(&last, &free, &keep);
                    b.start(&free);
                    call(m, b, Glue::Drop, &at.content, &f.ty)?;
                    b.ins(format!("call void @rt_free(ptr {boxed})"));
                    b.br(&done);
                    b.start(&keep);
                    let less = b.def(format!("sub i64 {rc}, 1"));
                    b.ins(format!("store i64 {less}, ptr {boxed}"));
                    b.start(&done);
                }
                (Indirect::Unique, Some(boxed)) => {
                    call(m, b, Glue::Drop, &at.content, &f.ty)?;
                    b.ins(format!("call void @rt_free(ptr {boxed})"));
                }
                _ => call(m, b, Glue::Drop, &at.content, &f.ty)?,
            }
        }
        Ok(())
    })
}

/// Drops the rows of the `Vec` at `v` from the one at `from` (a word) to its
/// last, and leaves it as long as it was: the caller sets its length. A row
/// is `rown` words: a value of the type `first`, and at the word `off` one of
/// `second` (`Unit` for a row of one value).
/// Drops every flagged slot of `h` from `from` up to `to`, and clears those
/// flags. A plain element needs no drop; its flag is still cleared.
pub fn drop_slots_range(
    m: &mut Module,
    b: &mut Body,
    h: &str,
    from: &str,
    to: &str,
    n: usize,
    a: &Ty,
) -> R<()> {
    let plain = layout::plain(m.pkg, a)?;
    let ip = b.alloca(1);
    b.ins(format!("store i64 {from}, ptr {ip}"));
    let (head, body, full, next, done) = (b.label(), b.label(), b.label(), b.label(), b.label());
    b.br(&head);
    b.start(&head);
    let i = b.def(format!("load i64, ptr {ip}"));
    let more = b.def(format!("icmp ult i64 {i}, {to}"));
    b.condbr(&more, &body, &done);
    b.start(&body);
    let fp = b.def(format!("call ptr @rt_slots_flag(ptr {h}, i64 {i})"));
    let f = b.def(format!("load i64, ptr {fp}"));
    let filled = b.def(format!("icmp ne i64 {f}, 0"));
    b.condbr(&filled, &full, &next);
    b.start(&full);
    if !plain {
        let at = b.def(format!("call ptr @rt_slots_elem(ptr {h}, i64 {i}, i64 {n})"));
        call(m, b, Glue::Drop, &at, a)?;
    }
    b.ins(format!("store i64 0, ptr {fp}"));
    b.br(&next);
    b.start(&next);
    let i1 = b.def(format!("add i64 {i}, 1"));
    b.ins(format!("store i64 {i1}, ptr {ip}"));
    b.br(&head);
    b.start(&done);
    Ok(())
}

pub fn drop_rows(
    m: &mut Module,
    b: &mut Body,
    v: &str,
    from: &str,
    rown: usize,
    first: &Ty,
    off: usize,
    second: &Ty,
) -> R<()> {
    let (p1, p2) = (layout::plain(m.pkg, first)?, layout::plain(m.pkg, second)?);
    if p1 && p2 {
        return Ok(());
    }
    let n = rown;
    let lenp = b.gep(v, 1);
    let len = b.def(format!("load i64, ptr {lenp}"));
    let data = b.def(format!("load ptr, ptr {v}"));
    let ip = b.alloca(1);
    b.ins(format!("store i64 {from}, ptr {ip}"));
    let (head, body, done) = (b.label(), b.label(), b.label());
    b.br(&head);
    b.start(&head);
    let i = b.def(format!("load i64, ptr {ip}"));
    let more = b.def(format!("icmp ult i64 {i}, {len}"));
    b.condbr(&more, &body, &done);
    b.start(&body);
    let o = b.def(format!("mul i64 {i}, {n}"));
    let at = b.def(format!("getelementptr i64, ptr {data}, i64 {o}"));
    call(m, b, Glue::Drop, &at, first)?;
    if !p2 {
        let at2 = b.gep(&at, off);
        call(m, b, Glue::Drop, &at2, second)?;
    }
    let next = b.def(format!("add i64 {i}, 1"));
    b.ins(format!("store i64 {next}, ptr {ip}"));
    b.br(&head);
    b.start(&done);
    Ok(())
}

/// A box of its own holding the `words` words at `content`.
pub fn new_box(b: &mut Body, vals: &[String]) -> String {
    let boxed = b.def(format!("call ptr @rt_alloc(i64 {})", 8 * (1 + vals.len())));
    b.ins(format!("store i64 1, ptr {boxed}"));
    b.store(&boxed, 1, vals);
    boxed
}

fn dup(m: &mut Module, b: &mut Body, p: &str, t: &Ty) -> R<()> {
    let shape = layout::shape(m.pkg, t)?;
    if let Shape::Scalar(Scalar::Shown) = shape {
        let w = b.def(format!("load i64, ptr {p}"));
        let s = b.ptr(&w);
        let copy = b.def(format!("call ptr @rt_strdup(ptr {s})"));
        let w = b.word(&copy);
        b.ins(format!("store i64 {w}, ptr {p}"));
        return Ok(());
    }
    if let Shape::Scalar(Scalar::Text) = shape {
        // One more value shares the text's box.
        let w = b.def(format!("load i64, ptr {p}"));
        let s = b.ptr(&w);
        b.ins(format!("call void @rt_text_dup(ptr {s})"));
        return Ok(());
    }
    if let Shape::Scalar(Scalar::Vec) = shape {
        return refuse("a copy of a `Vec`");
    }
    if let Shape::Scalar(Scalar::Slots) = shape {
        return refuse("a copy of a `Slots`");
    }
    if let Shape::Scalar(Scalar::Fn) = shape {
        // One more value shares the function value's box.
        let w = b.def(format!("load i64, ptr {p}"));
        let s = b.ptr(&w);
        b.ins(format!("call void @rt_text_dup(ptr {s})"));
        return Ok(());
    }
    let Some((tagged, cs)) = ctors(shape) else {
        return Ok(());
    };
    for_ctor(m, b, p, tagged, &cs, &mut |m, b, _, c| {
        for (i, f) in c.fields.iter().enumerate() {
            let plain = layout::plain(m.pkg, &f.ty)?;
            if f.indirect == Indirect::None && plain {
                continue;
            }
            let at = field_at(m, b, p, tagged, &c.fields, i)?;
            match (f.indirect, &at.boxed) {
                (Indirect::Shared, Some(boxed)) => {
                    // One more value shares the box.
                    let rc = b.def(format!("load i64, ptr {boxed}"));
                    let more = b.def(format!("add i64 {rc}, 1"));
                    b.ins(format!("store i64 {more}, ptr {boxed}"));
                }
                (Indirect::Unique, Some(_)) => {
                    // The copy owns a box of its own, with a copy of the
                    // content.
                    let n = layout::words(m.pkg, &f.ty)?;
                    let vals = b.load(&at.content, 0, n);
                    let boxed = new_box(b, &vals);
                    let w = b.word(&boxed);
                    b.ins(format!("store i64 {w}, ptr {}", at.slot));
                    let content = b.gep(&boxed, 1);
                    call(m, b, Glue::Dup, &content, &f.ty)?;
                }
                _ => call(m, b, Glue::Dup, &at.content, &f.ty)?,
            }
        }
        Ok(())
    })
}

fn push(m: &mut Module, b: &mut Body, buf: &str, s: &str) {
    if s.is_empty() {
        return;
    }
    let c = m.string(s);
    b.ins(format!(
        "call void @rt_push(ptr {buf}, ptr {c}, i64 {})",
        s.len()
    ));
}

/// Shows the value at `p`, as every backend does (`show`'s format).
fn show(m: &mut Module, b: &mut Body, buf: &str, p: &str, t: &Ty) -> R<()> {
    let shape = layout::shape(m.pkg, t)?;
    match &shape {
        Shape::Unit => {
            push(m, b, buf, "()");
            return Ok(());
        }
        Shape::Scalar(s) => {
            let w = b.def(format!("load i64, ptr {p}"));
            match s {
                Scalar::Int(_, true) => {
                    b.ins(format!("call void @rt_push_i64(ptr {buf}, i64 {w})"))
                }
                Scalar::Int(_, false) => {
                    b.ins(format!("call void @rt_push_u64(ptr {buf}, i64 {w})"))
                }
                Scalar::Bool => {
                    let c = b.cond(&w);
                    let (yes, no, done) = (b.label(), b.label(), b.label());
                    b.condbr(&c, &yes, &no);
                    b.start(&yes);
                    push(m, b, buf, "true");
                    b.br(&done);
                    b.start(&no);
                    push(m, b, buf, "false");
                    b.start(&done);
                }
                Scalar::Shown => {
                    let s = b.ptr(&w);
                    b.ins(format!("call void @rt_push_str(ptr {buf}, ptr {s})"));
                }
                Scalar::Fn => return refuse("`show` of a function value"),
                Scalar::Vec => return refuse("`show` of a `Vec`"),
                Scalar::Slots => return refuse("`show` of a `Slots`"),
                Scalar::Text => {
                    let s = b.ptr(&w);
                    b.ins(format!("call void @rt_push_text(ptr {buf}, ptr {s})"));
                }
                Scalar::Borrow => {
                    let (Ty::Ref(inner) | Ty::RefMut(inner)) = t else {
                        return refuse("internal: a borrow of no type");
                    };
                    let q = b.ptr(&w);
                    show_at(m, b, buf, &q, inner)?;
                }
            }
            return Ok(());
        }
        Shape::Pair(..) | Shape::Sum { .. } => {}
    }
    if let Shape::Pair(first, rest) = &shape {
        // A product of more members is nested to the right, and shown flat.
        push(m, b, buf, "#(");
        let fields = [first.clone(), rest.clone()];
        let at = field_at(m, b, p, false, &fields, 0)?;
        show_at(m, b, buf, &at.content, &first.ty)?;
        let mut rest_at = field_at(m, b, p, false, &fields, 1)?.content;
        let mut rest_ty = rest.ty.clone();
        while let Shape::Pair(x, y) = layout::shape(m.pkg, &rest_ty)? {
            push(m, b, buf, ", ");
            let fields = [x.clone(), y.clone()];
            let at = field_at(m, b, &rest_at, false, &fields, 0)?;
            show_at(m, b, buf, &at.content, &x.ty)?;
            rest_at = field_at(m, b, &rest_at, false, &fields, 1)?.content;
            rest_ty = y.ty.clone();
        }
        push(m, b, buf, ", ");
        show_at(m, b, buf, &rest_at, &rest_ty)?;
        push(m, b, buf, ")");
        return Ok(());
    }
    let is_struct = matches!(
        &shape,
        Shape::Sum {
            is_struct: true,
            ..
        }
    );
    let Some((tagged, cs)) = ctors(shape) else {
        return Ok(());
    };
    for_ctor(m, b, p, tagged, &cs, &mut |m, b, _, c| {
        let named = c.fields.iter().all(|f| f.name.is_some());
        push(m, b, buf, &c.name);
        if (is_struct || !c.fields.is_empty()) && named {
            push(m, b, buf, " {");
            for (i, f) in c.fields.iter().enumerate() {
                let label = format!(
                    "{}{}: ",
                    if i == 0 { " " } else { ", " },
                    f.name.as_deref().unwrap_or("")
                );
                push(m, b, buf, &label);
                let at = field_at(m, b, p, tagged, &c.fields, i)?;
                show_at(m, b, buf, &at.content, &f.ty)?;
            }
            push(m, b, buf, if c.fields.is_empty() { "}" } else { " }" });
        } else if !c.fields.is_empty() {
            for (i, f) in c.fields.iter().enumerate() {
                push(m, b, buf, if i == 0 { "(" } else { ", " });
                let at = field_at(m, b, p, tagged, &c.fields, i)?;
                show_at(m, b, buf, &at.content, &f.ty)?;
            }
            push(m, b, buf, ")");
        }
        Ok(())
    })
}

/// Calls the `show` glue of `t` on the value at `p`.
pub fn show_at(m: &mut Module, b: &mut Body, buf: &str, p: &str, t: &Ty) -> R<()> {
    let f = m.glue(Glue::Show, t);
    b.ins(format!("call fastcc void {f}(ptr {buf}, ptr {p})"));
    Ok(())
}
