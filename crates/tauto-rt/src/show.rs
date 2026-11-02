//! `show`: how a value is displayed, as the evaluator's `Display for Value`
//! does. The generator writes the impls for the
//! program's own types.

use crate::stdlib::{
    Atomic, Bytes, HashMap, Mutex, MutexGuard, Pending, Ref, Secret, Signal, Weak, atomic_load,
    ref_with,
};
use crate::{Nat, Never, Owned, Product, Rc, Shared, Text, Unlink};

/// A value already shown: what `show` carries to the host.
#[derive(Debug, Clone)]
pub struct Shown(pub String);

impl Shown {
    pub fn of<T: Show + ?Sized>(v: &T) -> Shown {
        Shown(v.show())
    }
}

pub trait Show {
    fn show(&self) -> String;
}

macro_rules! plain {
    ($($t:ty),*) => {$(
        impl Show for $t {
            fn show(&self) -> String {
                format!("{self}")
            }
        }
    )*};
}

plain!(i32, i64, u8, u32, u64, f64, bool, Nat);

// A `Float32` shows the digits of the same number as a `Float`, as the
// JavaScript backend, which keeps both as numbers, writes it.
impl Show for f32 {
    fn show(&self) -> String {
        format!("{}", f64::from(*self))
    }
}

impl Show for () {
    fn show(&self) -> String {
        "()".into()
    }
}

impl Show for Never {
    fn show(&self) -> String {
        match *self {}
    }
}

impl Show for Shown {
    fn show(&self) -> String {
        self.0.clone()
    }
}

impl Show for str {
    fn show(&self) -> String {
        format!("{self:?}")
    }
}

impl Show for Text {
    fn show(&self) -> String {
        format!("{:?}", &**self)
    }
}

impl Show for String {
    fn show(&self) -> String {
        format!("Buf({self:?})")
    }
}

impl<T: Show + ?Sized> Show for &T {
    fn show(&self) -> String {
        (**self).show()
    }
}

impl<T: Show + ?Sized> Show for &mut T {
    fn show(&self) -> String {
        (**self).show()
    }
}

impl<T: Show + ?Sized> Show for Box<T> {
    fn show(&self) -> String {
        (**self).show()
    }
}

impl<T: Show> Show for Rc<T> {
    fn show(&self) -> String {
        (**self).show()
    }
}

/// `Array(T)`, so an array nested in another value shows as the evaluator
/// shows it.
impl<T: Show> Show for Rc<[T]> {
    fn show(&self) -> String {
        let items: Vec<String> = self.iter().map(Show::show).collect();
        format!("Array[{}]", items.join(", "))
    }
}

impl<T: Show + Unlink> Show for Shared<T> {
    fn show(&self) -> String {
        (**self).show()
    }
}

impl<T: Show + Unlink> Show for Owned<T> {
    fn show(&self) -> String {
        (**self).show()
    }
}

impl<T: Show> Show for Option<T> {
    fn show(&self) -> String {
        match self {
            Some(v) => format!("Some({})", v.show()),
            None => "None".into(),
        }
    }
}

impl<T: Show, E: Show> Show for Result<T, E> {
    fn show(&self) -> String {
        match self {
            Ok(v) => format!("Ok({})", v.show()),
            Err(e) => format!("Err({})", e.show()),
        }
    }
}

macro_rules! product_show {
    ($($t:ident $i:tt),+) => {
        impl<$($t: Show),+> Show for Product<($($t,)+)> {
            fn show(&self) -> String {
                let members: Vec<String> = vec![$(self.0.$i.show()),+];
                members.join(" × ")
            }
        }
    };
}

product_show!(A 0, B 1);
product_show!(A 0, B 1, C 2);
product_show!(A 0, B 1, C 2, D 3);
product_show!(A 0, B 1, C 2, D 3, E 4);
product_show!(A 0, B 1, C 2, D 3, E 4, F 5);
product_show!(A 0, B 1, C 2, D 3, E 4, F 5, G 6);
product_show!(A 0, B 1, C 2, D 3, E 4, F 5, G 6, H 7);

impl<A: Show, B: Show> Show for (A, B) {
    fn show(&self) -> String {
        format!("Pair {{ fst: {}, snd: {} }}", self.0.show(), self.1.show())
    }
}

impl<T: Show> Show for Vec<T> {
    fn show(&self) -> String {
        let items: Vec<String> = self.iter().map(Show::show).collect();
        format!("Vec[{}]", items.join(", "))
    }
}

impl<T: Show> Show for [T] {
    fn show(&self) -> String {
        let items: Vec<String> = self.iter().map(Show::show).collect();
        format!("Vec[{}]", items.join(", "))
    }
}

impl<K: Show, V: Show> Show for HashMap<K, V> {
    fn show(&self) -> String {
        let items: Vec<String> = self
            .iter()
            .map(|(k, v)| format!("{}: {}", k.show(), v.show()))
            .collect();
        format!("HashMap{{{}}}", items.join(", "))
    }
}

impl<T: Show> Show for Ref<T> {
    fn show(&self) -> String {
        format!("Ref({})", ref_with(self, |v| v.show()))
    }
}

impl<T> Show for Weak<T> {
    fn show(&self) -> String {
        "Weak".to_string()
    }
}

impl<T> Show for Mutex<T> {
    fn show(&self) -> String {
        "Mutex".to_string()
    }
}

impl<T> Show for MutexGuard<T> {
    fn show(&self) -> String {
        "MutexGuard".to_string()
    }
}

impl Show for Atomic {
    fn show(&self) -> String {
        format!("Atomic({})", atomic_load(self.clone()))
    }
}

impl Show for Signal {
    fn show(&self) -> String {
        "Signal".to_string()
    }
}

impl Show for Bytes {
    fn show(&self) -> String {
        let items: Vec<String> = self.iter().map(|b| b.to_string()).collect();
        format!("Bytes[{}]", items.join(", "))
    }
}

// As the evaluator shows it: a secret hides what it holds.
impl<T> Show for Secret<T> {
    fn show(&self) -> String {
        "Secret".into()
    }
}

impl<T> Show for Pending<T> {
    fn show(&self) -> String {
        "Pending".to_string()
    }
}
