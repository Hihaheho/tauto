//! The runtime library's functions (`Callee::Builtin`), as the other
//! backends' runtimes define them.

use std::rc::Rc;

use tauto_rt::float;
use tauto_rt::host::{Host as _, System};

use crate::code::{Ctor, Program};
use crate::machine::{Machine, checked};
use crate::value::{
    Answer, Data, Error, GuardState, MutexState, Pending, PendingState, Place, R, Root, SharedKind,
    Signal, Step, TOO_LARGE, Value, equal, fail, temp_ref,
};

/// What a builtin answers: a value, or an operation it performs (with no
/// arguments and no resumption: `out_of_bounds`, `missing`).
pub enum Out {
    Value(Value),
    Perform(Rc<str>),
    /// Starts a task that runs the function, whose result is the pending.
    Spawn(Value, Rc<Pending>),
    /// Lets the other tasks run first, then answers whether the pending is
    /// ready.
    Yield(Rc<Pending>),
    /// A request of the host that waits: the task waits for its reply.
    Host(crate::hostcall::Job),
}

pub struct Known {
    some: Rc<Ctor>,
    none: Rc<Ctor>,
    ok: Rc<Ctor>,
    err: Rc<Ctor>,
    pair: Rc<Ctor>,
    cons: Rc<Ctor>,
    nil: Rc<Ctor>,
}

impl Known {
    pub fn new(p: &Program) -> Known {
        let find = |owner: &str, tag: &str| {
            p.ctors
                .iter()
                .find(|c| {
                    c.owner == tauto_nir::library_name(owner)
                        && c.tag == tauto_nir::library_name(tag)
                })
                .cloned()
                .expect("a constructor of the prelude")
        };
        Known {
            some: find("Option", "Some"),
            none: find("Option", "None"),
            ok: find("Result", "Ok"),
            err: find("Result", "Err"),
            pair: find("Pair", "Pair"),
            cons: find("List", "Cons"),
            nil: find("List", "Nil"),
        }
    }

    fn make(c: &Rc<Ctor>, fields: Vec<Value>) -> Value {
        Value::Data(Rc::new(Data {
            ctor: c.clone(),
            fields,
        }))
    }

    pub fn some(&self, v: Value) -> Value {
        Self::make(&self.some, vec![v])
    }
    pub fn none(&self) -> Value {
        Self::make(&self.none, Vec::new())
    }
    pub fn option(&self, v: Option<Value>) -> Value {
        match v {
            Some(v) => self.some(v),
            None => self.none(),
        }
    }
    pub fn ok(&self, v: Value) -> Value {
        Self::make(&self.ok, vec![v])
    }
    pub fn err(&self, v: Value) -> Value {
        Self::make(&self.err, vec![v])
    }
    pub fn result<E: std::fmt::Display>(&self, r: Result<Value, E>) -> Value {
        match r {
            Ok(v) => self.ok(v),
            Err(e) => self.err(Value::text(&e.to_string())),
        }
    }
    pub fn pair(&self, a: Value, b: Value) -> Value {
        Self::make(&self.pair, vec![a, b])
    }
    pub fn list(&self, items: impl DoubleEndedIterator<Item = Value>) -> Value {
        let mut out = Self::make(&self.nil, Vec::new());
        for x in items.rev() {
            out = Self::make(&self.cons, vec![x, out]);
        }
        out
    }
    pub fn items(&self, mut v: Value) -> R<Vec<Value>> {
        let mut out = Vec::new();
        loop {
            v = v.get()?;
            let Value::Data(d) = &v else {
                return fail("internal: expected a List");
            };
            if d.ctor.id == self.nil.id {
                return Ok(out);
            }
            out.push(d.fields[0].get()?);
            let next = d.fields[1].clone();
            v = next;
        }
    }
}

pub const NAMES: &[&str] = &[
    "clone",
    "replace",
    "Buf::new",
    "Buf::of",
    "Buf::clone",
    "Buf::push",
    "Text::of",
    "Vec::new",
    "Vec::push",
    "Vec::pop",
    "Vec::len",
    "Slice::len",
    "Array::len",
    "Vec::as_slice",
    "Vec::as_mut_slice",
    "Vec::clear",
    "Vec::truncate",
    "Vec::get",
    "Vec::get_mut",
    "Slice::get",
    "Vec::last_mut",
    "Vec::index",
    "Vec::swap",
    "Vec::into_list",
    "Array::to_list",
    "Vec::into_array",
    "Array::of_list",
    "Array::get",
    "Bytes::of_list",
    "Bytes::to_list",
    "Bytes::len",
    "Bytes::get",
    "Bytes::slice",
    "Bytes::concat",
    "Syn::same_declaration",
    "Syn::eliminator",
    "Bytes::eq",
    "Bytes::of_text",
    "Text::of_bytes",
    "HashMap::new",
    "HashMap::insert",
    "HashMap::get",
    "HashMap::get_mut",
    "HashMap::index",
    "HashMap::into_vec",
    "Text::byte",
    "Text::slice",
    "Text::of_code_point",
    "Text::of_utf8",
    "I64::of_i32",
    "I64::of_u64",
    "I32::of_i64",
    "Nat::of_u64",
    "U64::of_i64",
    "U64::of_u32",
    "U64::of_u8",
    "U64::of_nat",
    "U32::of_u64",
    "U8::of_u64",
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
    "words",
    "budget_value",
    "info_more",
    "info_unbounded",
    "U32::and",
    "U32::or",
    "U32::xor",
    "U32::shl",
    "U32::shr",
    "U32::rotl",
    "U32::rotr",
    "U64::and",
    "U64::or",
    "U64::xor",
    "U64::shl",
    "U64::shr",
    "U64::rotl",
    "U64::rotr",
    "Ref::new",
    "Ref::get",
    "Ref::set",
    "Weak::of",
    "Weak::get",
    "Atomic::new",
    "Atomic::load",
    "Atomic::store",
    "Atomic::fetch_add",
    "secret",
    "expose",
    "Os::args",
    "Os::print",
    "Os::eprint",
    "Os::read_file",
    "Os::write_file",
    "Os::read_bytes",
    "Os::write_bytes",
    "Os::read_under",
    "Os::read_bytes_under",
    "Os::create_dir",
    "Os::remove",
    "Os::stat",
    "Os::read_link",
    "Os::write_new",
    "Os::move_path",
    "Os::copy_file",
    "Os::canonicalize",
    "Os::temp_dir",
    "Os::read_line",
    "Os::read_stdin",
    "Os::flush",
    "Os::on_shutdown",
    "Os::env",
    "Os::wall_ms",
    "Os::monotonic_ns",
    "Os::random",
    "Os::secure_random",
    "Os::status",
    "Os::check",
    "Os::stop",
    "Os::exit",
    "Os::sleep_pending",
    "Os::offload",
    "pending_spawn",
    "Pending::ready",
    "Pending::take",
    "Pending::is_ready",
    "Pending::signal",
    "Mutex::new",
    "Mutex::claim",
    "Mutex::take_claimed",
    "Mutex::put",
    "MutexGuard::claimed",
    "MutexGuard::get",
    "MutexGuard::get_mut",
    "Signal::fresh",
    "Signal::raise",
    "Signal::is_raised",
    "Signal::either",
    "Signal::listen",
];

fn pending(v: &Value) -> R<Rc<Pending>> {
    match v.get()? {
        Value::Pending(p) => Ok(p),
        v => fail(format!("internal: expected a Pending, got {}", v.kind())),
    }
}

fn signal(v: &Value) -> R<Rc<Signal>> {
    match v.get()? {
        Value::Signal(s) => Ok(s),
        v => fail(format!("internal: expected a Signal, got {}", v.kind())),
    }
}

fn mutex(v: &Value) -> R<Rc<std::cell::RefCell<MutexState>>> {
    match v.get()? {
        Value::Mutex(m) => Ok(m),
        v => fail(format!("internal: expected a Mutex, got {}", v.kind())),
    }
}

fn int(v: &Value) -> R<i128> {
    v.as_int()
}

fn index(n: i128, len: usize) -> Option<usize> {
    usize::try_from(n).ok().filter(|i| *i < len)
}

/// A borrow of the place `v` is, or of a temporary holding it.
fn place(v: &Value) -> Rc<Place> {
    match v {
        Value::Ref(p) => p.clone(),
        v => match temp_ref(v.clone()) {
            Value::Ref(p) => p,
            _ => unreachable!(),
        },
    }
}

fn items(v: &Value) -> R<Rc<Vec<Value>>> {
    match v.get()? {
        Value::Vec(xs) | Value::Array(xs) => Ok(xs),
        v => fail(format!("internal: expected a Vec, got {}", v.kind())),
    }
}

fn bytes(v: &Value) -> R<Rc<[u8]>> {
    match v.get()? {
        Value::Bytes(b) => Ok(b),
        v => fail(format!("internal: expected Bytes, got {}", v.kind())),
    }
}

fn with_vec<T>(v: &Value, f: impl FnOnce(&mut Vec<Value>) -> T) -> R<T> {
    place(v).with_mut(|slot| match slot {
        Value::Vec(xs) | Value::Array(xs) => Ok(f(Rc::make_mut(xs))),
        v => fail(format!("internal: expected a Vec, got {}", v.kind())),
    })
}

fn with_map<T>(v: &Value, f: impl FnOnce(&mut Vec<(Value, Value)>) -> R<T>) -> R<T> {
    place(v).with_mut(|slot| match slot {
        Value::Map(m) => f(Rc::make_mut(m)),
        v => fail(format!("internal: expected a HashMap, got {}", v.kind())),
    })
}

fn find_key(m: &[(Value, Value)], k: &Value) -> R<Option<usize>> {
    for (i, (key, _)) in m.iter().enumerate() {
        if equal(key, k)? {
            return Ok(Some(i));
        }
    }
    Ok(None)
}

fn shared(v: &Value) -> R<Rc<std::cell::RefCell<Value>>> {
    match v.get()? {
        Value::Shared(_, c) => Ok(c),
        v => fail(format!(
            "internal: expected a shared slot, got {}",
            v.kind()
        )),
    }
}

fn text_of_utf8(bytes: &[u8]) -> Option<Value> {
    std::str::from_utf8(bytes).ok().map(Value::text)
}

fn rotl(a: u128, s: u32, bits: u32) -> u128 {
    let mask = (1u128 << bits) - 1;
    let s = s % bits;
    if s == 0 {
        return a & mask;
    }
    ((a << s) | (a >> (bits - s))) & mask
}

pub fn call(m: &mut Machine<'_>, name: &str, a: Vec<Value>) -> R<Out> {
    let k = &m.known;
    if crate::hostcall::NAMES.contains(&name) {
        return Ok(Out::Host(crate::hostcall::job(k, name, &a)?));
    }
    let v = |v: Value| Ok(Out::Value(v));
    match name {
        "clone" => v(a[0].get()?),
        "replace" => {
            let p = place(&a[0]);
            let old = p.get()?;
            p.set(a[1].clone())?;
            v(old)
        }
        "Buf::new" => v(Value::Buf(Rc::new(String::new()))),
        "Buf::of" | "Buf::clone" => v(Value::Buf(Rc::new(a[0].as_text()?.to_string()))),
        "Buf::push" => {
            let t = a[1].as_text()?;
            place(&a[0]).with_mut(|slot| match slot {
                Value::Buf(b) => {
                    Rc::make_mut(b).push_str(&t);
                    Ok(())
                }
                v => fail(format!("internal: expected a Buf, got {}", v.kind())),
            })?;
            v(Value::Unit)
        }
        "Text::of" => v(Value::Text(a[0].as_text()?)),
        "Vec::new" => v(Value::Vec(Rc::new(Vec::new()))),
        "Vec::push" => {
            let x = a[1].clone();
            with_vec(&a[0], |xs| xs.push(x))?;
            v(Value::Unit)
        }
        "Vec::pop" => {
            let x = with_vec(&a[0], |xs| xs.pop())?;
            v(k.option(x))
        }
        "Vec::len" | "Slice::len" | "Array::len" => v(Value::Int(items(&a[0])?.len() as i128)),
        "Vec::as_slice" | "Vec::as_mut_slice" => v(a[0].clone()),
        "Vec::clear" => {
            with_vec(&a[0], |xs| xs.clear())?;
            v(Value::Unit)
        }
        "Vec::truncate" => {
            let n = usize::try_from(int(&a[1])?).unwrap_or(usize::MAX);
            with_vec(&a[0], |xs| xs.truncate(n))?;
            v(Value::Unit)
        }
        "Vec::get" | "Vec::get_mut" | "Slice::get" | "Vec::index" => {
            let len = items(&a[0])?.len();
            match index(int(&a[1])?, len) {
                Some(i) => {
                    let r = Value::Ref(Rc::new(place(&a[0]).child(Step::Item(i))));
                    v(if name == "Vec::index" { r } else { k.some(r) })
                }
                None if name == "Vec::index" => Ok(Out::Perform(Rc::from("out_of_bounds"))),
                None => v(k.none()),
            }
        }
        "Vec::last_mut" => {
            let len = items(&a[0])?.len();
            if len == 0 {
                return v(k.none());
            }
            v(k.some(Value::Ref(Rc::new(place(&a[0]).child(Step::Item(len - 1))))))
        }
        "Vec::swap" => {
            let len = items(&a[0])?.len();
            match (index(int(&a[1])?, len), index(int(&a[2])?, len)) {
                (Some(i), Some(j)) => {
                    with_vec(&a[0], |xs| xs.swap(i, j))?;
                    v(Value::Unit)
                }
                _ => Ok(Out::Perform(Rc::from("out_of_bounds"))),
            }
        }
        "Vec::into_list" | "Array::to_list" => {
            let xs = items(&a[0])?;
            v(k.list(xs.iter().cloned()))
        }
        "Vec::into_array" => v(Value::Array(items(&a[0])?)),
        "Array::of_list" => v(Value::Array(Rc::new(k.items(a[0].clone())?))),
        "Array::get" => {
            let xs = items(&a[0])?;
            v(k.option(index(int(&a[1])?, xs.len()).map(|i| xs[i].clone())))
        }
        "Bytes::of_list" => {
            let mut out = Vec::new();
            for x in k.items(a[0].clone())? {
                out.push(u8::try_from(int(&x)?).map_err(|_| Error::Runtime(TOO_LARGE.into()))?);
            }
            v(Value::Bytes(Rc::from(out)))
        }
        "Bytes::to_list" => {
            let b = bytes(&a[0])?;
            v(k.list(b.iter().map(|x| Value::Int(*x as i128))))
        }
        "Bytes::len" => v(Value::Int(bytes(&a[0])?.len() as i128)),
        "Bytes::get" => {
            let b = bytes(&a[0])?;
            v(k.option(index(int(&a[1])?, b.len()).map(|i| Value::Int(b[i] as i128))))
        }
        "Bytes::slice" => {
            let b = bytes(&a[0])?;
            let (s, e) = (int(&a[1])?, int(&a[2])?);
            if s < 0 || e < s || e > b.len() as i128 {
                return v(k.none());
            }
            v(k.some(Value::Bytes(Rc::from(&b[s as usize..e as usize]))))
        }
        "Bytes::concat" => {
            let (x, y) = (bytes(&a[0])?, bytes(&a[1])?);
            let mut out = x.to_vec();
            out.extend_from_slice(&y);
            v(Value::Bytes(Rc::from(out)))
        }
        "Syn::same_declaration" => v(Value::Bool(crate::value::equal(&a[0], &a[1])?)),
        "Syn::eliminator" => match a[0].get()? {
            Value::Declaration(d) => v(Value::Declaration(tauto_rt::stdlib::syn_eliminator(d))),
            other => fail(format!("internal: expected a declaration reference, got {}", other.kind())),
        },
        "Bytes::eq" => v(Value::Bool(bytes(&a[0])? == bytes(&a[1])?)),
        "Bytes::of_text" => v(Value::Bytes(Rc::from(a[0].as_text()?.as_bytes()))),
        "Text::of_bytes" => v(k.option(text_of_utf8(&bytes(&a[0])?))),
        "HashMap::new" => v(Value::Map(Rc::new(Vec::new()))),
        "HashMap::insert" => {
            let (key, x) = (a[1].get()?, a[2].clone());
            let old = with_map(&a[0], |m| match find_key(m, &key)? {
                Some(i) => Ok(Some(std::mem::replace(&mut m[i].1, x))),
                None => {
                    m.push((key, x));
                    Ok(None)
                }
            })?;
            v(k.option(old))
        }
        "HashMap::get" | "HashMap::get_mut" | "HashMap::index" => {
            let key = a[1].get()?;
            let found = match a[0].get()? {
                Value::Map(m) => find_key(&m, &key)?,
                v => return fail(format!("internal: expected a HashMap, got {}", v.kind())),
            };
            match found {
                Some(i) => {
                    let r = Value::Ref(Rc::new(place(&a[0]).child(Step::Entry(i))));
                    v(if name == "HashMap::index" {
                        r
                    } else {
                        k.some(r)
                    })
                }
                None if name == "HashMap::index" => Ok(Out::Perform(Rc::from("missing"))),
                None => v(k.none()),
            }
        }
        "HashMap::into_vec" => match a[0].get()? {
            Value::Map(m) => v(Value::Vec(Rc::new(
                m.iter()
                    .map(|(x, y)| k.pair(x.clone(), y.clone()))
                    .collect(),
            ))),
            v => fail(format!("internal: expected a HashMap, got {}", v.kind())),
        },
        "Text::byte" => {
            let t = a[0].as_text()?;
            v(k.option(index(int(&a[1])?, t.len()).map(|i| Value::Int(t.as_bytes()[i] as i128))))
        }
        "Text::slice" => {
            let t = a[0].as_text()?;
            let (s, e) = (int(&a[1])?, int(&a[2])?);
            if s < 0 || e < s || e > t.len() as i128 {
                return v(k.none());
            }
            v(k.option(text_of_utf8(&t.as_bytes()[s as usize..e as usize])))
        }
        "Text::of_code_point" => {
            let n = int(&a[0])?;
            v(k.option(
                u32::try_from(n)
                    .ok()
                    .and_then(char::from_u32)
                    .map(|c| Value::text(c.encode_utf8(&mut [0; 4]))),
            ))
        }
        "Text::of_utf8" => {
            let mut out = Vec::new();
            for x in k.items(a[0].clone())? {
                match u8::try_from(int(&x)?) {
                    Ok(b) => out.push(b),
                    Err(_) => return v(k.none()),
                }
            }
            v(k.option(text_of_utf8(&out)))
        }
        "I64::of_i32" | "I64::of_u64" => v(Value::Int(checked(
            Some(int(&a[0])?),
            tauto_nir::Width::W64,
        )?)),
        "I32::of_i64" => v(Value::Int(checked(
            Some(int(&a[0])?),
            tauto_nir::Width::W32,
        )?)),
        "Nat::of_u64" => v(Value::Int(int(&a[0])?)),
        "U64::of_i64" | "U64::of_u32" | "U64::of_u8" | "U64::of_nat" => v(Value::Int(checked(
            Some(int(&a[0])?),
            tauto_nir::Width::U64,
        )?)),
        "U32::of_u64" => v(Value::Int(checked(
            Some(int(&a[0])?),
            tauto_nir::Width::U32,
        )?)),
        "U8::of_u64" => v(Value::Int(checked(
            Some(int(&a[0])?),
            tauto_nir::Width::U8,
        )?)),
        "Float::of_i64" => v(Value::Float(int(&a[0])? as f64)),
        "I64::of_float" => match float::i64_of_float_checked(a[0].as_float()?) {
            Some(n) => v(Value::Int(n as i128)),
            None => fail(TOO_LARGE),
        },
        "Float::of_text" => v(k.option(float::float_of_str(&a[0].as_text()?).map(Value::Float))),
        "Text::of_float" => v(Value::text(&float::text_of_float(a[0].as_float()?))),
        "Float::bits" => v(Value::Int(float::float_bits(a[0].as_float()?) as i128)),
        "Float::of_bits" => {
            let b = u64::try_from(int(&a[0])?).map_err(|_| Error::Runtime(TOO_LARGE.into()))?;
            v(Value::Float(float::float_of_bits(b)))
        }
        "Float::is_nan" => v(Value::Bool(a[0].as_float()?.is_nan())),
        "Float::of_float32" => v(Value::Float(f64::from(a[0].as_float32()?))),
        "Float32::of_float" => v(Value::Float32(float::float32_of_float(a[0].as_float()?))),
        "Float32::bits" => v(Value::Int(float::float32_bits(a[0].as_float32()?) as i128)),
        "Float32::of_bits" => {
            let b = u32::try_from(int(&a[0])?).map_err(|_| Error::Runtime(TOO_LARGE.into()))?;
            v(Value::Float32(float::float32_of_bits(b)))
        }
        "Float32::is_nan" => v(Value::Bool(a[0].as_float32()?.is_nan())),
        n if n.starts_with("Float32.") => {
            let x = a[0].as_float32()?;
            let y = match a.get(1) {
                Some(b) => b.as_float32()?,
                None => 0.0,
            };
            v(Value::Float32(match n {
                "Float32::abs" => float::float32_abs(x),
                "Float32::floor" => float::float32_floor(x),
                "Float32::ceil" => float::float32_ceil(x),
                "Float32::trunc" => float::float32_trunc(x),
                "Float32::round" => float::float32_round(x),
                "Float32::sqrt" => float::float32_sqrt(x),
                "Float32::cbrt" => float::float32_cbrt(x),
                "Float32::exp" => float::float32_exp(x),
                "Float32::ln" => float::float32_ln(x),
                "Float32::log2" => float::float32_log2(x),
                "Float32::log10" => float::float32_log10(x),
                "Float32::pow" => float::float32_pow(x, y),
                "Float32::sin" => float::float32_sin(x),
                "Float32::cos" => float::float32_cos(x),
                "Float32::tan" => float::float32_tan(x),
                "Float32::asin" => float::float32_asin(x),
                "Float32::acos" => float::float32_acos(x),
                "Float32::atan" => float::float32_atan(x),
                "Float32::atan2" => float::float32_atan2(x, y),
                "Float32::sinh" => float::float32_sinh(x),
                "Float32::cosh" => float::float32_cosh(x),
                "Float32::tanh" => float::float32_tanh(x),
                _ => return fail(format!("unknown builtin {n}")),
            }))
        }
        n if n.starts_with("Float.") => {
            let x = a[0].as_float()?;
            let y = match a.get(1) {
                Some(b) => b.as_float()?,
                None => 0.0,
            };
            v(Value::Float(match n {
                "Float::abs" => float::float_abs(x),
                "Float::floor" => float::float_floor(x),
                "Float::ceil" => float::float_ceil(x),
                "Float::trunc" => float::float_trunc(x),
                "Float::round" => float::float_round(x),
                "Float::sqrt" => float::float_sqrt(x),
                "Float::cbrt" => float::float_cbrt(x),
                "Float::exp" => float::float_exp(x),
                "Float::ln" => float::float_ln(x),
                "Float::log2" => float::float_log2(x),
                "Float::log10" => float::float_log10(x),
                "Float::pow" => float::float_pow(x, y),
                "Float::sin" => float::float_sin(x),
                "Float::cos" => float::float_cos(x),
                "Float::tan" => float::float_tan(x),
                "Float::asin" => float::float_asin(x),
                "Float::acos" => float::float_acos(x),
                "Float::atan" => float::float_atan(x),
                "Float::atan2" => float::float_atan2(x, y),
                "Float::sinh" => float::float_sinh(x),
                "Float::cosh" => float::float_cosh(x),
                "Float::tanh" => float::float_tanh(x),
                _ => return fail(format!("unknown builtin {n}")),
            }))
        }
        "words" => {
            let t = a[0].as_text()?;
            v(k.list(
                t.split(char::is_whitespace)
                    .filter(|w| !w.is_empty())
                    .map(Value::text)
                    .collect::<Vec<_>>()
                    .into_iter(),
            ))
        }
        n if n.starts_with("U32.") || n.starts_with("U64.") => {
            let bits = if n.starts_with("U32.") { 32 } else { 64 };
            let (x, y) = (int(&a[0])? as u128, int(&a[1])? as u128);
            let s = (y % bits as u128) as u32;
            let mask = (1u128 << bits) - 1;
            let r = match &n[4..] {
                "and" => x & y,
                "or" => x | y,
                "xor" => x ^ y,
                "shl" => (x << s) & mask,
                "shr" => x >> s,
                "rotl" => rotl(x, s, bits),
                "rotr" => rotl(x, (bits - s) % bits, bits),
                _ => return fail(format!("unknown builtin {n}")),
            };
            v(Value::Int(r as i128))
        }
        "budget_value" => v(Value::Answer(Rc::new(Answer::Value(a[0].clone())))),
        "info_more" => v(Value::Answer(Rc::new(Answer::More(Some(int(&a[1])?))))),
        "info_unbounded" => v(Value::Answer(Rc::new(Answer::More(None)))),
        "Ref::new" => v(Value::Shared(
            SharedKind::Ref,
            Rc::new(std::cell::RefCell::new(a[0].get()?)),
        )),
        "Ref::get" => v(shared(&a[0])?.borrow().clone()),
        "Ref::set" => {
            *shared(&a[0])?.borrow_mut() = a[1].clone();
            v(Value::Unit)
        }
        "Weak::of" => v(Value::Weak(Rc::downgrade(&shared(&a[0])?))),
        "Weak::get" => match a[0].get()? {
            Value::Weak(w) => v(k.option(w.upgrade().map(|c| Value::Shared(SharedKind::Ref, c)))),
            x => fail(format!("internal: expected a Weak, got {}", x.kind())),
        },
        "Atomic::new" => v(Value::Shared(
            SharedKind::Atomic,
            Rc::new(std::cell::RefCell::new(a[0].get()?)),
        )),
        "Atomic::load" => v(shared(&a[0])?.borrow().clone()),
        "Atomic::store" => {
            *shared(&a[0])?.borrow_mut() = a[1].get()?;
            v(Value::Unit)
        }
        "Atomic::fetch_add" => {
            let c = shared(&a[0])?;
            let old = int(&c.borrow())?;
            let new = (old as u128).wrapping_add(int(&a[1])? as u128) as u64;
            *c.borrow_mut() = Value::Int(new as i128);
            v(Value::Int(old))
        }
        "Os::args" => {
            let args = m.host.args();
            v(m.known.list(
                args.iter()
                    .map(|s| Value::text(s))
                    .collect::<Vec<_>>()
                    .into_iter(),
            ))
        }
        "Os::print" => {
            let t = a[0].as_text()?;
            m.host.stdout(&t);
            v(Value::Unit)
        }
        "Os::eprint" => {
            let t = a[0].as_text()?;
            m.host.stderr(&t);
            v(Value::Unit)
        }
        "Os::read_file" => v(k.result(System.read_file(&a[0].as_text()?).map(|t| Value::text(&t)))),
        "Os::write_file" => v(k.result(
            System
                .write_file(&a[0].as_text()?, &a[1].as_text()?)
                .map(|()| Value::Unit),
        )),
        "Os::read_bytes" => v(k.result(
            System
                .read_bytes(&a[0].as_text()?)
                .map(|b| Value::Bytes(Rc::from(b))),
        )),
        "Os::write_bytes" => v(k.result(
            System
                .write_bytes(&a[0].as_text()?, &bytes(&a[1])?)
                .map(|()| Value::Unit),
        )),
        "Os::read_under" => v(k.result(
            tauto_rt::stdlib::os_read_under(
                tauto_rt::Text::from(&*a[0].as_text()?),
                tauto_rt::Text::from(&*a[1].as_text()?),
            )
            .map(|t| Value::text(&t)),
        )),
        "Os::read_bytes_under" => v(k.result(
            System
                .read_bytes_under(&a[0].as_text()?, &a[1].as_text()?)
                .map(|b| Value::Bytes(Rc::from(b))),
        )),
        "Os::create_dir" => v(k.result(System.create_dir(&a[0].as_text()?).map(|()| Value::Unit))),
        "Os::remove" => v(k.result(System.remove(&a[0].as_text()?).map(|()| Value::Unit))),
        "Os::stat" => v(k.result(System.stat(&a[0].as_text()?).map(|found| {
            let items = match found {
                None => Vec::new(),
                Some(s) => vec![
                    Value::text(s.kind),
                    Value::text(&s.size.to_string()),
                    Value::text(&s.modified_ms.to_string()),
                ],
            };
            k.list(items.into_iter())
        }))),
        "Os::read_link" => v(k.result(System.read_link(&a[0].as_text()?).map(|found| {
            k.list(found.iter().map(|t| Value::text(t)).collect::<Vec<_>>().into_iter())
        }))),
        "Os::write_new" => v(k.result(
            System
                .create_new(&a[0].as_text()?, a[1].as_text()?.as_bytes())
                .map(|()| Value::Unit),
        )),
        "Os::move_path" => v(k.result(
            System
                .rename(&a[0].as_text()?, &a[1].as_text()?)
                .map(|()| Value::Unit),
        )),
        "Os::copy_file" => v(k.result(
            System
                .copy(&a[0].as_text()?, &a[1].as_text()?)
                .map(|()| Value::Unit),
        )),
        "Os::canonicalize" => v(k.result(
            System
                .canonicalize(&a[0].as_text()?)
                .map(|p| Value::text(&p)),
        )),
        // The run may read and write under the directory, as under one the
        // user picked (`Permissions::choose`).
        "Os::temp_dir" => {
            let made = System
                .temp_dir()
                .map_err(|e| e.to_string())
                .and_then(|dir| {
                    let p = m.host.permissions();
                    p.choose("read", &dir, true);
                    p.choose("write", &dir, true)
                        .ok_or_else(|| format!("{dir}: cannot be resolved"))
                });
            v(k.result(made.map(|d| Value::text(&d))))
        }
        "Os::read_stdin" => v(Value::Bytes(Rc::from(
            System.read_stdin(a[0].as_int()?.clamp(0, 1 << 24) as usize),
        ))),
        "Os::on_shutdown" => {
            let outside = tauto_rt::signal::Signal::new();
            tauto_rt::shutdown::register(outside.clone());
            *signal(&a[0])?.outside.borrow_mut() = Some(outside);
            v(Value::Unit)
        }
        "Os::flush" => {
            System.flush();
            v(Value::Unit)
        }
        "Os::read_line" => v(k.option(System.read_line().map(|t| Value::text(&t)))),
        "Os::env" => v(k.option(System.env(&a[0].as_text()?).map(|t| Value::text(&t)))),
        "Os::wall_ms" => v(Value::Int(System.wall_ms() as i128)),
        "Os::monotonic_ns" => v(Value::Int(System.monotonic_ns() as i128)),
        "Os::random" => v(Value::Int((System.random() >> 1) as i128)),
        "secret" => v(Value::Secret(Rc::new(a[0].clone()))),
        "expose" => match a[0].get()? {
            Value::Secret(x) => v((*x).clone()),
            x => fail(format!("internal: expected a Secret, got {}", x.kind())),
        },
        "Os::secure_random" => {
            let n = usize::try_from(int(&a[0])?).unwrap_or(usize::MAX);
            v(k.result(System.secure_random(n).map(|b| Value::Bytes(Rc::from(b)))))
        }
        "Os::status" => v(Value::Int(
            a[0].as_text()?.parse::<u64>().unwrap_or(0) as i128
        )),
        "Os::check" => {
            let (kind, target) = (a[0].as_text()?, a[1].as_text()?);
            let t = m.host.permissions().check_or_ask(&kind, &target);
            v(m.known.option(t.map(|t| Value::text(&t))))
        }
        "Os::sleep_pending" => {
            let ms = u64::try_from(int(&a[0])?).unwrap_or(u64::MAX);
            let at = std::time::Instant::now()
                .checked_add(std::time::Duration::from_millis(ms))
                .unwrap_or_else(|| {
                    std::time::Instant::now() + std::time::Duration::from_secs(1 << 32)
                });
            let p = Pending::new(PendingState::Timer(at));
            m.timers.push(p.clone());
            v(Value::Pending(p))
        }
        "Os::offload" | "pending_spawn" => {
            let p = Pending::new(PendingState::Running);
            Ok(Out::Spawn(a[0].get()?, p))
        }
        "Pending::ready" => v(Value::Pending(Pending::new(PendingState::Ready(
            a[0].clone(),
        )))),
        "Pending::take" => {
            let p = pending(&a[0])?;
            p.ready();
            let state = std::mem::replace(&mut *p.state.borrow_mut(), PendingState::Taken);
            match state {
                PendingState::Ready(x) => v(x),
                _ => fail("internal: a result taken before it was there"),
            }
        }
        "Pending::is_ready" => {
            let p = pending(&a[0])?;
            if p.ready() {
                v(Value::Bool(true))
            } else {
                Ok(Out::Yield(p))
            }
        }
        "Signal::listen" => v(a[0].get()?),
        "Signal::fresh" => v(Value::Signal(Rc::new(Signal::default()))),
        "Signal::raise" => {
            signal(&a[0])?.raise();
            v(Value::Unit)
        }
        "Signal::is_raised" => v(Value::Bool(signal(&a[0])?.is_raised())),
        "Signal::either" => {
            let mut seen = std::collections::HashSet::new();
            let inputs = [signal(&a[0])?, signal(&a[1])?]
                .into_iter()
                .flat_map(|s| {
                    if s.inputs.is_empty() {
                        vec![s]
                    } else {
                        s.inputs.clone()
                    }
                })
                .filter(|s| seen.insert(Rc::as_ptr(s) as usize))
                .collect();
            v(Value::Signal(Rc::new(Signal {
                inputs,
                ..Signal::default()
            })))
        }
        "Pending::signal" => {
            let p = pending(&a[0])?;
            p.ready();
            v(Value::Signal(p.signal.clone()))
        }
        "Mutex::new" => v(Value::Mutex(Rc::new(std::cell::RefCell::new(MutexState {
            value: Some(a[0].clone()),
            waiting: Default::default(),
        })))),
        "Mutex::claim" => {
            let mx = mutex(&a[0])?;
            let mut mx = mx.borrow_mut();
            let s = Rc::new(Signal::default());
            if mx.value.is_some() && mx.waiting.is_empty() {
                *s.handed.borrow_mut() = mx.value.take();
                s.raise();
            } else {
                mx.waiting.push_back(s.clone());
            }
            v(Value::Signal(s))
        }
        "Mutex::take_claimed" => {
            let s = signal(&a[1])?;
            let x = s.handed.borrow_mut().take();
            match x {
                Some(x) => v(x),
                None => fail("internal: a mutex's content taken before it was handed"),
            }
        }
        "MutexGuard::claimed" => {
            let mx = mutex(&a[0])?;
            let s = signal(&a[1])?;
            let x = s.handed.borrow_mut().take();
            match x {
                Some(x) => v(Value::Guard(Rc::new(GuardState {
                    mutex: mx,
                    content: Rc::new(std::cell::RefCell::new(x)),
                }))),
                None => fail("internal: a mutex's content taken before it was handed"),
            }
        }
        "MutexGuard::get" | "MutexGuard::get_mut" => match a[0].get()? {
            Value::Guard(g) => v(Value::Ref(Rc::new(Place {
                root: Root::Cell(g.content.clone()),
                path: Vec::new(),
            }))),
            other => fail(format!(
                "internal: expected a MutexGuard, got {}",
                other.kind()
            )),
        },
        "Mutex::put" => {
            let mx = mutex(&a[0])?;
            let mut mx = mx.borrow_mut();
            match mx.waiting.pop_front() {
                Some(s) => {
                    *s.handed.borrow_mut() = Some(a[1].clone());
                    s.raise();
                }
                None => mx.value = Some(a[1].clone()),
            }
            v(Value::Unit)
        }
        "Os::stop" => Err(Error::Runtime(a[0].as_text()?.to_string())),
        "Os::exit" => {
            let code = checked(Some(int(&a[0])?), tauto_nir::Width::U8)?;
            Err(Error::Exit(code as i32))
        }
        n => fail(format!("unknown builtin {n}")),
    }
}
