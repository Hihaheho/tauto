//! `std::time::Instant::now` and `SystemTime::now` panic on wasm32-unknown-unknown, so the
//! crates a browser runs read the time only through `tauto_rt::clock` or `tauto_kernel::clock`.

use std::path::Path;

fn scan(dir: &Path, bad: &mut Vec<String>) {
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.is_dir() {
            scan(&p, bad);
        } else if p.extension().is_some_and(|x| x == "rs") {
            let s = std::fs::read_to_string(&p).unwrap();
            let body = s.split("#[cfg(test)]").next().unwrap();
            for (i, l) in body.lines().enumerate() {
                let code = l.split("//").next().unwrap();
                if code.contains("std::time::Instant::now") || code.contains("SystemTime::now") {
                    bad.push(format!("{}:{}", p.display(), i + 1));
                }
            }
        }
    }
}

#[test]
fn browser_crates_do_not_read_the_system_clock_directly() {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut bad = Vec::new();
    for c in ["tauto", "tauto-vm", "tauto-kernel", "tauto-rt"] {
        scan(&crates.join(c).join("src"), &mut bad);
    }
    // The clocks themselves are the only readers; they are cfg-gated off wasm32.
    // `child` runs processes, which a browser cannot.
    bad.retain(|b| !b.contains("/clock.rs:") && !b.contains("/child.rs:"));
    assert!(bad.is_empty(), "read the clock through `clock`: {bad:?}");
}
