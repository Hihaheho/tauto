//! Compiles totes/snippet to Rust. Each tote the `tauto` command carries has a
//! crate of its own, so that Cargo compiles them side by side and compiles
//! again only the one whose sources changed.

fn main() {
    if let Err(e) = tauto_build::compile("../../totes/snippet/Tauto.eure") {
        eprintln!("{e}");
        std::process::exit(1);
    }
}
