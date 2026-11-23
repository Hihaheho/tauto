//! Values and their tokens.
//!
//! The data is an immutable tree (`Rc` where it is shared); who owns it is
//! told by tokens, kept apart from the data so that the interpreter stays
//! small and the check is only the rules of the tokens.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use tauto_nir::{ClosureNode, CtorRef, FieldRef, Span};

pub type TokId = usize;
pub type Tok = Option<TokId>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TokState {
    Live,
    Dropped(Span),
    /// Taken by a builtin, an operator, or a pattern that split it.
    Consumed(Span),
}

#[derive(Debug, Clone)]
pub struct Token {
    pub state: TokState,
    pub made: Span,
    pub linear: bool,
}

/// A frame: the slots of one call (or of one closure's environment).
pub type Frame<'p> = Rc<FrameCell<'p>>;

thread_local! {
    static WRITES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many times a slot that a kept read went through was written so far
/// (`FrameCell::memo`): a kept read is still the value there while the
/// count is the same.
pub fn writes() -> u64 {
    WRITES.with(|w| w.get())
}

fn wrote() {
    WRITES.with(|w| w.set(w.get() + 1));
}

/// The slots of a frame, behind a cell that counts a write of a slot that
/// a kept read went through (`writes`).
#[derive(Debug, Default)]
pub struct FrameCell<'p> {
    data: RefCell<FrameData<'p>>,
    /// The slots a kept read went through: a write of one of them is
    /// counted.
    watched: RefCell<std::collections::HashSet<Key>>,
}

impl<'p> FrameCell<'p> {
    pub fn borrow(&self) -> std::cell::Ref<'_, FrameData<'p>> {
        self.data.borrow()
    }

    /// The slots to write: a write of every watched one.
    pub fn borrow_mut(&self) -> std::cell::RefMut<'_, FrameData<'p>> {
        if !self.watched.borrow().is_empty() {
            wrote();
        }
        self.data.borrow_mut()
    }

    /// The slots to write without counting it: the caller counts what it
    /// changes (`wrote_slot`).
    pub fn borrow_mut_uncounted(&self) -> std::cell::RefMut<'_, FrameData<'p>> {
        self.data.borrow_mut()
    }

    /// A kept read goes through slot `k`.
    pub fn watch(&self, k: Key) {
        self.watched.borrow_mut().insert(k);
    }

    /// Slot `k` was written.
    pub fn wrote_slot(&self, k: Key) {
        if self.watched.borrow().contains(&k) {
            wrote();
        }
    }

    /// Puts a slot in; a write when it takes the place of one.
    pub fn insert(&self, k: Key, slot: Slot<'p>) -> Option<Slot<'p>> {
        let old = self.data.borrow_mut().slots.insert(k, slot);
        if old.is_some() {
            self.wrote_slot(k);
        }
        old
    }
}

#[derive(Debug, Default)]
pub struct FrameData<'p> {
    pub slots: HashMap<Key, Slot<'p>>,
    /// The call has returned: borrows into it dangle.
    pub dead: bool,
    /// The environment of a closure.
    pub closure: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Key {
    Local(u32),
    /// The value of a `&(e)`.
    Temp(u32),
}

#[derive(Debug)]
pub enum Slot<'p> {
    Owned {
        name: String,
        /// `Val::Moved` once moved out.
        val: Val<'p>,
    },
    /// The same slot of another frame: what a closure uses of the frame it
    /// was made in, and what a call of a closure uses of its environment.
    Alias(Frame<'p>, Key),
}

#[derive(Debug, Clone)]
pub enum Root<'p> {
    Slot(Frame<'p>, Key),
    Cell(Rc<RefCell<Val<'p>>>),
    /// The place another borrow names: a borrow of a part of what a
    /// borrow names is one step from it, not a copy of its whole path.
    Via(Rc<Via<'p>>),
}

#[derive(Debug)]
pub struct Via<'p> {
    pub place: PlaceRef<'p>,
    /// What the place held, and the count of writes then (`writes`): a
    /// call that walks a list by borrowing its tail reads the tail here in
    /// one step, not by following every borrow from the head.
    pub kept: RefCell<Option<(u64, Val<'p>)>>,
}

/// A place: a slot or a shared cell, then field positions.
#[derive(Debug, Clone)]
pub struct PlaceRef<'p> {
    pub root: Root<'p>,
    pub path: Vec<FieldRef>,
}

#[derive(Debug, Clone)]
pub struct DataVal<'p> {
    pub ctor: &'p CtorRef,
    pub fields: Vec<Val<'p>>,
    pub tok: Tok,
}

#[derive(Debug, Clone)]
pub enum FnVal<'p> {
    Inst(usize),
    Closure {
        node: &'p ClosureNode,
        env: Frame<'p>,
    },
}

#[derive(Debug, Clone)]
pub enum Answer<'p> {
    /// `k(v)`: the budget's value is `v`.
    Value(Val<'p>),
    /// `info.more(m)` (`u64::MAX` for `info.unbounded()`).
    More(u64),
}

/// What `Slots` holds: a slot that holds no value is `Moved`, and only the
/// others are released.
#[derive(Debug, Clone)]
pub struct SlotsVal<'p> {
    pub state: Val<'p>,
    pub vacant: Val<'p>,
    pub marks: Vec<Val<'p>>,
    pub items: Vec<Val<'p>>,
}

#[derive(Debug, Clone)]
pub enum Val<'p> {
    Unit,
    Bool(bool),
    Int(i128, Tok),
    /// A `Nat` past `i128`.
    Big(Rc<crate::nat::BigNat>, Tok),
    Float(f64),
    Text(Rc<str>, Tok),
    Shown(Rc<str>, Tok),
    /// Shared until written (`Rc::make_mut`), so that reading a value to
    /// match it does not copy it.
    Data(Rc<DataVal<'p>>),
    Inject(usize, Box<Val<'p>>),
    Fn(Rc<FnVal<'p>>, Tok),
    Ref(PlaceRef<'p>),
    /// A shared `var`: one cell held by the function and its closures.
    Cell(Rc<RefCell<Val<'p>>>),
    /// A `Vec` (or, with `true`, an `Array`): its items in order.
    Seq(Rc<Vec<Val<'p>>>, Tok, bool),
    Buf(Rc<str>, Tok),
    /// `Slots`.
    Slots(Rc<SlotsVal<'p>>, Tok),
    /// A `Ref`: one cell that every copy shares.
    Shared(Rc<RefCell<Val<'p>>>, Tok),
    /// The `info` of an `exceeded` arm: the budget stopped.
    Info,
    /// What an `exceeded` arm answers with.
    Answer(Rc<Answer<'p>>),
    /// A continuation an arm is given (`k`).
    Cont(Rc<crate::kont::ContVal<'p>>),
    /// A part moved out of a place, with where.
    Moved(Span),
}

impl<'p> Val<'p> {
    pub fn tok(&self) -> Tok {
        match self {
            Val::Int(_, t)
            | Val::Big(_, t)
            | Val::Text(_, t)
            | Val::Shown(_, t)
            | Val::Fn(_, t)
            | Val::Seq(_, t, _)
            | Val::Buf(_, t)
            | Val::Slots(_, t)
            | Val::Shared(_, t) => *t,
            Val::Data(d) => d.tok,
            _ => None,
        }
    }

    /// Calls `f` on the tokens of the value, the value's own first, not
    /// entering a closure's environment (the closure's token stands for it)
    /// or a shared cell.
    pub fn tokens(&self, f: &mut dyn FnMut(TokId)) {
        if let Some(t) = self.tok() {
            f(t);
        }
        match self {
            Val::Data(d) => d.fields.iter().for_each(|x| x.tokens(f)),
            Val::Inject(_, x) => x.tokens(f),
            Val::Answer(a) => {
                if let Answer::Value(x) = &**a {
                    x.tokens(f)
                }
            }
            Val::Seq(xs, ..) => xs.iter().for_each(|x| x.tokens(f)),
            Val::Slots(r, _) => {
                r.state.tokens(f);
                r.items.iter().for_each(|x| x.tokens(f));
            }
            _ => {}
        }
    }

    /// The first token, depth first, that `pred` holds of; it stops there,
    /// so asking whether a long list owns anything looks at its head only.
    pub fn find_token(&self, pred: &mut dyn FnMut(TokId) -> bool) -> Option<TokId> {
        if let Some(t) = self.tok()
            && pred(t)
        {
            return Some(t);
        }
        match self {
            Val::Data(d) => d.fields.iter().find_map(|x| x.find_token(pred)),
            Val::Inject(_, x) => x.find_token(pred),
            Val::Answer(a) => match &**a {
                Answer::Value(x) => x.find_token(pred),
                Answer::More(_) => None,
            },
            Val::Seq(xs, ..) => xs.iter().find_map(|x| x.find_token(pred)),
            Val::Slots(r, _) => r
                .state
                .find_token(pred)
                .or_else(|| r.items.iter().find_map(|x| x.find_token(pred))),
            _ => None,
        }
    }

    /// Whether it carries a token.
    pub fn owns_token(&self) -> bool {
        self.find_token(&mut |_| true).is_some()
    }

    /// The first moved-out part, if any.
    pub fn moved_part(&self) -> Option<Span> {
        match self {
            Val::Moved(s) => Some(*s),
            Val::Data(d) => d.fields.iter().find_map(Val::moved_part),
            Val::Inject(_, x) => x.moved_part(),
            Val::Seq(xs, ..) => xs.iter().find_map(Val::moved_part),
            _ => None,
        }
    }

    pub fn kind(&self) -> &'static str {
        match self {
            Val::Unit => "unit",
            Val::Bool(_) => "bool",
            Val::Int(..) | Val::Big(..) => "int",
            Val::Float(_) => "float",
            Val::Text(..) => "text",
            Val::Shown(..) => "shown",
            Val::Data(_) => "data",
            Val::Inject(..) => "union",
            Val::Fn(..) => "function",
            Val::Ref(_) => "borrow",
            Val::Cell(_) => "shared var",
            Val::Cont(_) => "continuation",
            Val::Info => "budget info",
            Val::Answer(_) => "budget answer",
            Val::Seq(_, _, false) => "Vec",
            Val::Seq(_, _, true) => "Array",
            Val::Buf(..) => "Buf",
            Val::Slots(..) => "Slots",
            Val::Shared(..) => "Ref",
            Val::Moved(_) => "moved",
        }
    }
}
