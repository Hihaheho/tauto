//! Compiles the reader of the words of a grammar (`totes/parlex`) to Rust: the editor colours a
//! grammar by the same words the table generators read.

fn main() {
    if let Err(e) = tauto_build::compile("../../totes/parlex/Tauto.eure") {
        eprintln!("{e}");
        std::process::exit(1);
    }
}
