pub use tauto_surface::checker;
pub mod macros {
    pub use tauto_surface::checker;
    pub use tauto_surface::macros::EXPANSION_BASE;
}
pub use tauto_surface::{generated, nibstd, surface};
pub mod check;
pub mod clock;

/// Files are declared on copies of a kernel on other threads
/// (`check/fork.rs`), so a kernel must be able to move between threads.
#[allow(dead_code)]
fn kernel_is_send() {
    fn is_send<T: Send>() {}
    is_send::<check::Kernel>();
}
