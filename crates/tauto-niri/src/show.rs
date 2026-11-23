//! The text `show` gives a value: the same as every other backend's.

use std::fmt::Write;

use tauto_nir::{DataRef, Package, display_name};

use crate::value::Val;

pub fn show(pkg: &Package, v: &Val, out: &mut String) -> Result<(), String> {
    let list = |out: &mut String, items: &[Val], open: &str, close: &str| -> Result<(), String> {
        out.push_str(open);
        for (i, x) in items.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            show(pkg, x, out)?;
        }
        out.push_str(close);
        Ok(())
    };
    match v {
        Val::Unit => out.push_str("()"),
        Val::Bool(b) => write!(out, "{b}").unwrap(),
        Val::Int(n, _) => write!(out, "{n}").unwrap(),
        Val::Big(n, _) => write!(out, "{n}").unwrap(),
        Val::Float(x) => write!(out, "{x}").unwrap(),
        Val::Text(t, _) => write!(out, "{:?}", &**t).unwrap(),
        Val::Shown(t, _) => out.push_str(t),
        Val::Inject(_, x) => show(pkg, x, out)?,
        Val::Seq(xs, _, false) => list(out, xs, "Vec[", "]")?,
        Val::Seq(xs, _, true) => list(out, xs, "Array[", "]")?,
        Val::Slots(..) => out.push_str("Slots"),
        Val::Buf(b, _) => write!(out, "Buf({:?})", &**b).unwrap(),
        Val::Shared(c, _) => {
            out.push_str("Ref(");
            let inner = c.borrow().clone();
            show(pkg, &inner, out)?;
            out.push(')');
        }
        Val::Data(d) => {
            let pair = |v: &Val| matches!(v, Val::Data(d) if d.ctor.data == DataRef::Pair);
            if d.ctor.data == DataRef::Pair {
                out.push_str("#(");
                show(pkg, &d.fields[0], out)?;
                let mut rest = &d.fields[1];
                while pair(rest) {
                    let Val::Data(r) = rest else { unreachable!() };
                    out.push_str(", ");
                    show(pkg, &r.fields[0], out)?;
                    rest = &r.fields[1];
                }
                out.push_str(", ");
                show(pkg, rest, out)?;
                out.push(')');
                return Ok(());
            }
            let (is_struct, owner) = match &d.ctor.data {
                DataRef::Gen(n) => pkg
                    .datas
                    .iter()
                    .find(|x| &x.name == n)
                    .map(|x| (x.is_struct, display_name(&x.name).to_string()))
                    .unwrap_or((false, String::new())),
                _ => (false, String::new()),
            };
            let ctor = display_name(&d.ctor.name);
            let ctor = ctor.rsplit("::").next().unwrap_or(ctor).to_string();
            let tag = if is_struct { owner } else { ctor };
            let named = d.ctor.fields.iter().all(Option::is_some);
            if (is_struct || !d.fields.is_empty()) && named {
                out.push_str(&tag);
                out.push_str(" {");
                if !d.fields.is_empty() {
                    out.push(' ');
                    for (i, x) in d.fields.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        out.push_str(d.ctor.fields[i].as_deref().unwrap_or(""));
                        out.push_str(": ");
                        show(pkg, x, out)?;
                    }
                    out.push(' ');
                }
                out.push('}');
            } else {
                out.push_str(&tag);
                if !d.fields.is_empty() {
                    list(out, &d.fields, "(", ")")?;
                }
            }
        }
        v => return Err(format!("cannot show a {}", v.kind())),
    }
    Ok(())
}
