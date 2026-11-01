//! A value of millions of cells held through links is dropped without a
//! recursion as deep as the value.

use tauto_rt::link::Cells;
use tauto_rt::{Owned, Shared, Unlink};

#[derive(Clone)]
enum List {
    Nil,
    Cons(u64, Shared<List>),
}

impl Unlink for List {
    fn unlink(&mut self, cells: &mut Cells<Self>) {
        if let List::Cons(_, t) = self {
            cells.shared(t);
        }
    }
}

enum Chain {
    End,
    Link(u64, Owned<Chain>),
}

impl Unlink for Chain {
    fn unlink(&mut self, cells: &mut Cells<Self>) {
        if let Chain::Link(_, t) = self {
            cells.owned(t);
        }
    }
}

const LONG: u64 = 4_000_000;

#[test]
fn a_long_shared_list_is_dropped() {
    let mut l = List::Nil;
    for i in 0..LONG {
        l = List::Cons(i, Shared::new(l));
    }
    drop(l);
}

#[test]
fn a_shared_tail_stays_while_another_value_holds_it() {
    let mut l = List::Nil;
    for i in 0..LONG {
        l = List::Cons(i, Shared::new(l));
    }
    let List::Cons(_, tail) = &l else {
        unreachable!()
    };
    let kept = tail.clone();
    drop(l);
    let List::Cons(n, _) = &*kept else {
        unreachable!()
    };
    assert_eq!(*n, LONG - 2);
}

#[test]
fn a_long_owned_chain_is_dropped() {
    let mut c = Chain::End;
    for i in 0..LONG {
        c = Chain::Link(i, Owned::new(c));
    }
    drop(c);
}

#[test]
fn a_match_moves_the_content_out() {
    let l = List::Cons(1, Shared::new(List::Cons(2, Shared::new(List::Nil))));
    let List::Cons(_, t) = l else { unreachable!() };
    let List::Cons(n, _) = tauto_rt::unrc(t) else {
        unreachable!()
    };
    assert_eq!(n, 2);
    let c = Chain::Link(1, Owned::new(Chain::Link(2, Owned::new(Chain::End))));
    let Chain::Link(_, t) = c else { unreachable!() };
    let Chain::Link(n, _) = tauto_rt::unbox(t) else {
        unreachable!()
    };
    assert_eq!(n, 2);
}
