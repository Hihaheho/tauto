//! `array_set` writes the only reference to an array in place and copies a
//! shared one, so the other references still see the old elements.

use tauto_rt::stdlib::{Array, array_set};

#[test]
fn the_only_reference_is_written_in_place() {
    let a: Array<i64> = vec![1, 2, 3].into();
    let before = a.as_ptr();
    let a = array_set(a, 1, 20);
    assert_eq!(a.as_ptr(), before);
    assert_eq!(&*a, &[1, 20, 3]);
}

#[test]
fn a_shared_array_is_copied() {
    let a: Array<i64> = vec![1, 2, 3].into();
    let b = array_set(a.clone(), 0, 10);
    assert_eq!(&*a, &[1, 2, 3]);
    assert_eq!(&*b, &[10, 2, 3]);
}

#[test]
fn an_index_past_the_end_leaves_the_array() {
    let a: Array<i64> = vec![1, 2].into();
    let before = a.as_ptr();
    let a = array_set(a, 2, 9);
    assert_eq!(a.as_ptr(), before);
    assert_eq!(&*a, &[1, 2]);
}
