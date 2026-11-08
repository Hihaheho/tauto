//! Rust values to the machine's and back. The facade `tauto-build` writes
//! declares its own conversion trait with [`conversions!`](crate::conversions),
//! which implements it for the types of the standard library, and
//! implements it for each data type and extern type of the tote. The trait
//! is the facade's own so that it can be implemented for an extern type,
//! which is another crate's.

use std::rc::Rc;

use tauto_vm::Value;
use tauto_vm::builtins::Known;
use tauto_vm::code::{Ctor, Program};
use tauto_vm::value::Data;

/// The constructors of the running program: the prelude's, and each data
/// type's of the package by its index in `Package::datas`.
pub struct Cx {
    known: Known,
    /// The prelude's data types the conversions read: owner, then its
    /// constructors' ids by tag.
    prelude: Vec<(&'static str, Vec<(&'static str, u32)>)>,
    ctors: Vec<Vec<Option<Rc<Ctor>>>>,
}

impl Cx {
    /// `datas` holds the ids of each data type's constructors in the
    /// program, by the data type's index in the package
    /// (`tauto_vm::image::Image::datas`).
    pub(crate) fn new(program: &Program, datas: &[Vec<Option<u32>>]) -> Cx {
        let ctors = datas
            .iter()
            .map(|d| {
                d.iter()
                    .map(|c| c.map(|id| program.ctors[id as usize].clone()))
                    .collect()
            })
            .collect();
        let prelude = [
            ("Option", &["Some", "None"][..]),
            ("Result", &["Ok", "Err"][..]),
            ("Pair", &["Pair"][..]),
        ]
        .into_iter()
        .map(|(owner, tags)| {
            let ids = tags
                .iter()
                .filter_map(|tag| {
                    // By scanning, not `ctor_of`: a program read from bytes
                    // has no index of its constructors by name.
                    let (o, t) = (tauto_nir::library_name(owner), tauto_nir::library_name(tag));
                    let c = program.ctors.iter().find(|c| c.owner == o && c.tag == t)?;
                    Some((*tag, c.id))
                })
                .collect();
            (owner, ids)
        })
        .collect();
        Cx {
            known: Known::new(program),
            prelude,
            ctors,
        }
    }

    /// A value of constructor `ctor` of data type `data`.
    pub fn data(&self, data: usize, ctor: usize, fields: Vec<Value>) -> Value {
        let ctor = self.ctors[data][ctor]
            .clone()
            .unwrap_or_else(|| panic!("tauto-embed: the program has no constructor {data}.{ctor}"));
        Value::Data(Rc::new(Data { ctor, fields }))
    }

    /// Which constructor of data type `data` the value is, and its fields.
    pub fn match_data(&self, data: usize, v: Value) -> Result<(usize, Vec<Value>), String> {
        let v = v
            .get()
            .map_err(|_| "a borrow that cannot be read".to_string())?;
        let Value::Data(d) = v else {
            return Err(format!("expected a value of data type {data}"));
        };
        let at = self.ctors[data]
            .iter()
            .position(|c| c.as_ref().is_some_and(|c| c.id == d.ctor.id))
            .ok_or_else(|| {
                format!(
                    "{} is not a constructor of data type {data}",
                    d.ctor.tag.as_str()
                )
            })?;
        Ok((at, Rc::unwrap_or_clone(d).fields))
    }

    pub fn some(&self, v: Value) -> Value {
        self.known.some(v)
    }
    pub fn none(&self) -> Value {
        self.known.none()
    }
    pub fn ok(&self, v: Value) -> Value {
        self.known.ok(v)
    }
    pub fn err(&self, v: Value) -> Value {
        self.known.err(v)
    }
    pub fn pair(&self, a: Value, b: Value) -> Value {
        self.known.pair(a, b)
    }

    /// A value of the prelude's `owner` (`Option`, `Result`, `Pair`): its
    /// constructor's tag and its fields.
    pub fn prelude(&self, v: Value, owner: &str) -> Result<(String, Vec<Value>), String> {
        let tags = &self
            .prelude
            .iter()
            .find(|(o, _)| *o == owner)
            .expect("a prelude type")
            .1;
        match v
            .get()
            .map_err(|_| "a borrow that cannot be read".to_string())?
        {
            Value::Data(d) => match tags.iter().find(|(_, id)| *id == d.ctor.id) {
                Some((tag, _)) => Ok((tag.to_string(), Rc::unwrap_or_clone(d).fields)),
                None => Err(format!("expected a value of {owner}")),
            },
            _ => Err(format!("expected a value of {owner}")),
        }
    }
}

/// A value of an extern type, which the machine holds for the host.
pub fn host<T: 'static>(name: &str, v: T) -> Value {
    Value::Host(Rc::from(name), Rc::new(v))
}

/// The host's value of extern type `T` that `v` holds, borrowed: what an
/// extern function that takes `&T` is passed.
pub fn host_ref<T: 'static>(v: &Value) -> Result<Rc<dyn std::any::Any>, String> {
    match v
        .get()
        .map_err(|_| "a borrow that cannot be read".to_string())?
    {
        Value::Host(_, any) if any.is::<T>() => Ok(any),
        _ => Err(format!(
            "expected a value of {}",
            std::any::type_name::<T>()
        )),
    }
}

/// The host's value of extern type `T` that `v` holds, taken: the machine
/// gives it up.
pub fn host_take<T: 'static>(v: Value) -> Result<T, String> {
    match v {
        Value::Host(_, any) => match any.downcast::<T>() {
            Ok(rc) => Rc::try_unwrap(rc).map_err(|_| {
                format!(
                    "a value of {} still held elsewhere",
                    std::any::type_name::<T>()
                )
            }),
            Err(_) => Err(format!(
                "expected a value of {}",
                std::any::type_name::<T>()
            )),
        },
        _ => Err(format!(
            "expected a value of {}",
            std::any::type_name::<T>()
        )),
    }
}

/// Declares the trait `$vm` that converts Rust values to the machine's and
/// back, and implements it for the types of the standard library.
#[macro_export]
macro_rules! conversions {
    ($vm:ident) => {
        pub trait $vm: Sized {
            fn into_vm(self, cx: &$crate::Cx) -> $crate::Value;
            fn from_vm(v: $crate::Value, cx: &$crate::Cx) -> Result<Self, String>;
        }
        $crate::conversions!(@ints $vm: i8, i16, i32, i64, u8, u16, u32, u64);
        impl $vm for bool {
            fn into_vm(self, _: &$crate::Cx) -> $crate::Value {
                $crate::Value::Bool(self)
            }
            fn from_vm(v: $crate::Value, _: &$crate::Cx) -> Result<Self, String> {
                match v.get().map_err(|_| "a borrow".to_string())? {
                    $crate::Value::Bool(b) => Ok(b),
                    _ => Err("expected Bool".into()),
                }
            }
        }
        impl $vm for () {
            fn into_vm(self, _: &$crate::Cx) -> $crate::Value {
                $crate::Value::Unit
            }
            fn from_vm(v: $crate::Value, _: &$crate::Cx) -> Result<Self, String> {
                match v.get().map_err(|_| "a borrow".to_string())? {
                    $crate::Value::Unit => Ok(()),
                    _ => Err("expected Unit".into()),
                }
            }
        }
        impl $vm for f64 {
            fn into_vm(self, _: &$crate::Cx) -> $crate::Value {
                $crate::Value::Float(self)
            }
            fn from_vm(v: $crate::Value, _: &$crate::Cx) -> Result<Self, String> {
                match v.get().map_err(|_| "a borrow".to_string())? {
                    $crate::Value::Float(x) => Ok(x),
                    _ => Err("expected Float".into()),
                }
            }
        }
        impl $vm for f32 {
            fn into_vm(self, _: &$crate::Cx) -> $crate::Value {
                $crate::Value::Float32(self)
            }
            fn from_vm(v: $crate::Value, _: &$crate::Cx) -> Result<Self, String> {
                match v.get().map_err(|_| "a borrow".to_string())? {
                    $crate::Value::Float32(x) => Ok(x),
                    _ => Err("expected Float32".into()),
                }
            }
        }
        impl $vm for tauto_rt::Text {
            fn into_vm(self, _: &$crate::Cx) -> $crate::Value {
                $crate::Value::text(&self)
            }
            fn from_vm(v: $crate::Value, _: &$crate::Cx) -> Result<Self, String> {
                match v.get().map_err(|_| "a borrow".to_string())? {
                    $crate::Value::Text(t) => Ok(tauto_rt::Text::from(&*t)),
                    _ => Err("expected Text".into()),
                }
            }
        }
        impl $vm for String {
            fn into_vm(self, _: &$crate::Cx) -> $crate::Value {
                $crate::Value::Buf(std::rc::Rc::new(self))
            }
            fn from_vm(v: $crate::Value, _: &$crate::Cx) -> Result<Self, String> {
                match v.get().map_err(|_| "a borrow".to_string())? {
                    $crate::Value::Buf(b) => Ok(std::rc::Rc::unwrap_or_clone(b)),
                    _ => Err("expected Buf".into()),
                }
            }
        }
        impl<A: $vm> $vm for Vec<A> {
            fn into_vm(self, cx: &$crate::Cx) -> $crate::Value {
                $crate::Value::Vec(std::rc::Rc::new(
                    self.into_iter().map(|a| a.into_vm(cx)).collect(),
                ))
            }
            fn from_vm(v: $crate::Value, cx: &$crate::Cx) -> Result<Self, String> {
                match v.get().map_err(|_| "a borrow".to_string())? {
                    $crate::Value::Vec(items) => std::rc::Rc::unwrap_or_clone(items)
                        .into_iter()
                        .map(|a| A::from_vm(a, cx))
                        .collect(),
                    _ => Err("expected Vec".into()),
                }
            }
        }
        impl<A: $vm> $vm for Option<A> {
            fn into_vm(self, cx: &$crate::Cx) -> $crate::Value {
                match self {
                    Some(a) => cx.some(a.into_vm(cx)),
                    None => cx.none(),
                }
            }
            fn from_vm(v: $crate::Value, cx: &$crate::Cx) -> Result<Self, String> {
                let (tag, mut fields) = cx.prelude(v, "Option")?;
                match (tag.as_str(), fields.pop()) {
                    ("Some", Some(a)) => Ok(Some(A::from_vm(a, cx)?)),
                    ("None", None) => Ok(None),
                    _ => Err("expected Option".into()),
                }
            }
        }
        impl<A: $vm, E: $vm> $vm for Result<A, E> {
            fn into_vm(self, cx: &$crate::Cx) -> $crate::Value {
                match self {
                    Ok(a) => cx.ok(a.into_vm(cx)),
                    Err(e) => cx.err(e.into_vm(cx)),
                }
            }
            fn from_vm(v: $crate::Value, cx: &$crate::Cx) -> Result<Self, String> {
                let (tag, mut fields) = cx.prelude(v, "Result")?;
                match (tag.as_str(), fields.pop()) {
                    ("Ok", Some(a)) => Ok(Ok(A::from_vm(a, cx)?)),
                    ("Err", Some(e)) => Ok(Err(E::from_vm(e, cx)?)),
                    _ => Err("expected Result".into()),
                }
            }
        }
        impl<A: $vm, B: $vm> $vm for (A, B) {
            fn into_vm(self, cx: &$crate::Cx) -> $crate::Value {
                cx.pair(self.0.into_vm(cx), self.1.into_vm(cx))
            }
            fn from_vm(v: $crate::Value, cx: &$crate::Cx) -> Result<Self, String> {
                let (_, fields) = cx.prelude(v, "Pair")?;
                let [a, b]: [$crate::Value; 2] =
                    fields.try_into().map_err(|_| "expected Pair".to_string())?;
                Ok((A::from_vm(a, cx)?, B::from_vm(b, cx)?))
            }
        }
        impl<A: $vm> $vm for Box<A> {
            fn into_vm(self, cx: &$crate::Cx) -> $crate::Value {
                (*self).into_vm(cx)
            }
            fn from_vm(v: $crate::Value, cx: &$crate::Cx) -> Result<Self, String> {
                Ok(Box::new(A::from_vm(v, cx)?))
            }
        }
        impl<A: $vm + Clone> $vm for tauto_rt::Rc<A> {
            fn into_vm(self, cx: &$crate::Cx) -> $crate::Value {
                tauto_rt::Rc::unwrap_or_clone(self).into_vm(cx)
            }
            fn from_vm(v: $crate::Value, cx: &$crate::Cx) -> Result<Self, String> {
                Ok(tauto_rt::Rc::new(A::from_vm(v, cx)?))
            }
        }
    };
    (@ints $vm:ident: $($t:ty),*) => {$(
        impl $vm for $t {
            fn into_vm(self, _: &$crate::Cx) -> $crate::Value {
                $crate::Value::Int(self as i128)
            }
            fn from_vm(v: $crate::Value, _: &$crate::Cx) -> Result<Self, String> {
                match v.get().map_err(|_| "a borrow".to_string())? {
                    $crate::Value::Int(n) => <$t>::try_from(n)
                        .map_err(|_| format!("{n} does not fit {}", stringify!($t))),
                    _ => Err(format!("expected {}", stringify!($t))),
                }
            }
        }
    )*};
}
