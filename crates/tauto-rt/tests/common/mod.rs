//! Helpers for runtime integration tests: a host that records `show`, and a
//! value that records when it is dropped (`DropProbe`).

#![allow(dead_code)]

use std::cell::RefCell;
use std::rc::Rc;

use tauto_rt::ev::Ev;
use tauto_rt::{Loc, Payload, Text};

pub const L: Loc = Loc {
    file: "runtime_test.taut",
    line: 1,
    col: 1,
};

thread_local! {
    static DROPS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

/// Records its name when dropped.
pub struct DropProbe(pub &'static str);

impl Drop for DropProbe {
    fn drop(&mut self) {
        DROPS.with(|d| d.borrow_mut().push(self.0.to_string()));
    }
}

pub fn drops() -> Vec<String> {
    DROPS.with(|d| std::mem::take(&mut *d.borrow_mut()))
}

/// A host that collects `name = value` for each `show` whose payload is
/// `(Text, String)`: the generated code sends the displayed value.
pub fn host(shown: &Rc<RefCell<Vec<String>>>) -> Ev<'static> {
    let shown = shown.clone();
    Ev::host(move |args: Payload| {
        let (name, value) = *args
            .downcast::<(Text, String)>()
            .expect("tauto: payload type");
        shown.borrow_mut().push(format!("{name} = {value}"));
    })
}

pub fn text(s: &str) -> Text {
    Text::from(s)
}
