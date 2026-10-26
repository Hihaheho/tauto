pub fn identity<T>(value: T) -> T {
    value
}
pub fn rust_apply(f: &mut dyn FnMut(i64) -> i64) -> i64 {
    f(2) + f(3)
}
pub fn borrow_number(value: &mut i64) -> &mut i64 {
    value
}
pub fn adder(n: i64) -> impl Fn(i64) -> i64 {
    move |value| value + n
}
