//! ```nib
//! effect step(): () resume 1
//! ```
//! The `k` of a `resume 1` operation is linear: it carries a `Bomb`. Calling
//! it defuses; dropping it in a debug build panics.

use tauto_rt::Bomb;

fn make_k() -> impl FnOnce(i64) -> i64 {
    let bomb = Bomb::new("k of step");
    move |x| {
        bomb.defuse();
        x + 1
    }
}

#[test]
fn calling_k_does_not_ring() {
    assert_eq!(make_k()(1), 2);
}

#[test]
#[cfg(debug_assertions)]
fn dropping_k_rings_in_debug() {
    let r = std::panic::catch_unwind(|| {
        let k = make_k();
        drop(k);
    });
    assert!(r.is_err());
}

#[test]
fn a_panic_on_the_way_does_not_ring_twice() {
    // While unwinding, a dropped bomb stays quiet.
    let r = std::panic::catch_unwind(|| {
        let _k = make_k();
        panic!("an error of the program");
    });
    let msg = r.unwrap_err();
    assert_eq!(
        *msg.downcast_ref::<&str>().unwrap(),
        "an error of the program"
    );
}
