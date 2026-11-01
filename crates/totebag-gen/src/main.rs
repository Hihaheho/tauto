//! `cargo run -p totebag-gen`: writes `crates/totebag/src/core.rs` again from
//! `totes/totebag`. The compiler reads totes through totebag, so totebag
//! cannot compile the tote in a build script; its code is kept in the
//! repository and a test there says when it is out of date.

use std::path::Path;

fn main() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../totebag");
    // Named relative to totebag, as the file says where it came from.
    std::env::set_current_dir(&dir).expect("crates/totebag");
    let (_, text, warnings) =
        tauto_build::generate(Path::new("../../totes/totebag/Tauto.eure"), None).unwrap_or_else(
            |e| {
                eprintln!("{e}");
                std::process::exit(1)
            },
        );
    for w in warnings {
        eprintln!("{w}");
    }
    std::fs::write("src/core.rs", text).expect("src/core.rs");
}
