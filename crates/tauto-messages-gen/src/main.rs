//! `cargo run -p tauto-messages-gen`: writes `crates/tauto-messages/src/fluent.rs`
//! again from `totes/fluent`. tauto-build writes its own messages through
//! tauto-messages, so tauto-messages cannot compile the tote in a build
//! script; its code is kept in the repository and a test there says when it
//! is out of date.

use std::path::Path;

fn main() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tauto-messages");
    // Named relative to tauto-messages, as the file says where it came from.
    std::env::set_current_dir(&dir).expect("crates/tauto-messages");
    let (_, text, warnings) =
        tauto_build::generate(Path::new("../../totes/fluent/Tauto.eure"), None).unwrap_or_else(
            |e| {
                eprintln!("{e}");
                std::process::exit(1)
            },
        );
    for w in warnings {
        eprintln!("{w}");
    }
    std::fs::write("src/fluent.rs", text).expect("src/fluent.rs");
}
