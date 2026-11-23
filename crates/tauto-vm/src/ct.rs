//! The secret words (`Ct::` of `std/builtin/secret.taut`) on the machine
//! that runs a program in process. It computes them as plain words and
//! numbers, which take a time that depends on the values
//! (`docs/design/secret.md`); the bytecode written for `totes/vm` refuses
//! them (`wire::SECRET_WORDS`).

use std::rc::Rc;

use crate::builtins::Known;
use crate::value::{R, Value, fail};

/// Whether `name` is a secret word.
pub fn is_ct(name: &str) -> bool {
    name.starts_with("Ct::")
}

fn secret(v: &Value) -> R<Value> {
    match v.get()? {
        Value::Secret(x) => Ok((*x).clone()),
        x => fail(format!("internal: expected a Secret, got {}", x.kind())),
    }
}

fn word(v: &Value) -> R<i128> {
    secret(v)?.as_int()
}

fn flag(v: &Value) -> R<bool> {
    secret(v)?.as_bool()
}

fn wrap(v: Value) -> Value {
    Value::Secret(Rc::new(v))
}

fn width(name: &str) -> Option<u32> {
    match name {
        "u8" => Some(8),
        "u32" => Some(32),
        "u64" => Some(64),
        _ => None,
    }
}

/// Runs the secret word `name` (`Ct::u64_add`).
pub fn call(k: &Known, name: &str, a: &[Value]) -> R<Value> {
    let rest = name.strip_prefix("Ct::").unwrap_or(name);
    let arg = |i: usize| crate::value::arg(a, i);
    let Some((head, op)) = rest.split_once('_') else {
        return fail(format!("internal: no secret word {name}"));
    };
    if head == "bool" {
        return Ok(match op {
            "and" => wrap(Value::Bool(flag(arg(0)?)? & flag(arg(1)?)?)),
            "or" => wrap(Value::Bool(flag(arg(0)?)? | flag(arg(1)?)?)),
            "not" => wrap(Value::Bool(!flag(arg(0)?)?)),
            "select" => {
                let (c, x, y) = (flag(arg(0)?)?, flag(arg(1)?)?, flag(arg(2)?)?);
                wrap(Value::Bool(if c { x } else { y }))
            }
            _ => return fail(format!("internal: no secret word {name}")),
        });
    }
    if head == "bytes" {
        let bytes = match secret(arg(0)?)? {
            Value::Bytes(b) => b,
            x => return fail(format!("internal: expected Bytes, got {}", x.kind())),
        };
        return Ok(match op {
            "len" => Value::Int(bytes.len() as i128),
            "get" => {
                let i = usize::try_from(arg(1)?.as_int()?).ok();
                k.option(
                    i.and_then(|i| bytes.get(i))
                        .map(|b| wrap(Value::Int(i128::from(*b)))),
                )
            }
            _ => return fail(format!("internal: no secret word {name}")),
        });
    }
    let Some(w) = width(head) else {
        return fail(format!("internal: no secret word {name}"));
    };
    let mask: u128 = if w == 64 {
        u64::MAX as u128
    } else {
        (1u128 << w) - 1
    };
    let bits = |x: i128| (x as u128) & mask;
    let out = |x: u128| wrap(Value::Int((x & mask) as i128));
    // A change of width: `u64_of_u8`.
    if let Some(from) = op.strip_prefix("of_") {
        if width(from).is_none() {
            return fail(format!("internal: no secret word {name}"));
        }
        return Ok(out(bits(word(arg(0)?)?)));
    }
    if op == "select" {
        let (c, x, y) = (flag(arg(0)?)?, word(arg(1)?)?, word(arg(2)?)?);
        return Ok(out(bits(if c { x } else { y })));
    }
    let x = bits(word(arg(0)?)?);
    if op == "not" {
        return Ok(out(!x));
    }
    // The shifts and rotations take a public amount, modulo the width.
    if matches!(op, "shl" | "shr" | "rotl" | "rotr") {
        let s = (arg(1)?.as_int()? as u128 % u128::from(w)) as u32;
        let r = match op {
            "shl" => x << s,
            "shr" => x >> s,
            "rotl" => (x << s) | (x >> ((w - s) % w)),
            _ => (x >> s) | (x << ((w - s) % w)),
        };
        return Ok(out(r));
    }
    let y = bits(word(arg(1)?)?);
    Ok(match op {
        "add" => out(x.wrapping_add(y)),
        "sub" => out(x.wrapping_sub(y)),
        "mul" => out(x.wrapping_mul(y)),
        "and" => out(x & y),
        "or" => out(x | y),
        "xor" => out(x ^ y),
        "eq" => wrap(Value::Bool(x == y)),
        "lt" => wrap(Value::Bool(x < y)),
        "mul_hi" => out((x * y) >> w),
        _ => return fail(format!("internal: no secret word {name}")),
    })
}
