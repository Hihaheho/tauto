//! Compiles the totes the `tauto` command runs to Rust, so that the command
//! carries them and never compiles its own Tauto when it runs.

fn main() {
    for tote in ["vm", "syntaxgen"] {
        if let Err(e) = tauto_build::compile(format!("../../totes/{tote}/Tauto.eure")) {
            eprintln!("{e}");
            std::process::exit(1);
        }
    }
}
