//! The secret words of `src/ct.rs` compile to code without a conditional
//! branch: each is compiled with optimizations into an exported function, and
//! the assembly of those functions holds no conditional jump.
#![cfg(target_arch = "x86_64")]

use std::fmt::Write as _;
use std::process::Command;

const WORDS: [&str; 3] = ["u8", "u32", "u64"];

/// An exported function for each secret word, so the compiler keeps it.
fn wrappers() -> String {
    let mut out = String::new();
    let mut add = |name: &str, params: &str, result: &str, call: &str| {
        writeln!(
            out,
            "#[unsafe(no_mangle)] pub extern \"C\" fn probe_{name}({params}) -> {result} {{ expose({call}) }}"
        )
        .unwrap();
    };
    for w in WORDS {
        for op in ["add", "sub", "mul", "and", "or", "xor"] {
            let name = format!("ct_{w}_{op}");
            add(
                &name,
                &format!("a: {w}, b: {w}"),
                w,
                &format!("{name}(secret(a), secret(b))"),
            );
        }
        for op in ["shl", "shr", "rotl", "rotr"] {
            let name = format!("ct_{w}_{op}");
            add(
                &name,
                &format!("a: {w}, s: u64"),
                w,
                &format!("{name}(secret(a), s)"),
            );
        }
        for op in ["eq", "lt"] {
            let name = format!("ct_{w}_{op}");
            add(
                &name,
                &format!("a: {w}, b: {w}"),
                "bool",
                &format!("{name}(secret(a), secret(b))"),
            );
        }
        let name = format!("ct_{w}_not");
        add(&name, &format!("a: {w}"), w, &format!("{name}(secret(a))"));
        let name = format!("ct_{w}_select");
        add(
            &name,
            &format!("c: bool, a: {w}, b: {w}"),
            w,
            &format!("{name}(secret(c), secret(a), secret(b))"),
        );
    }
    add(
        "ct_u64_mul_hi",
        "a: u64, b: u64",
        "u64",
        "ct_u64_mul_hi(secret(a), secret(b))",
    );
    for op in ["and", "or"] {
        let name = format!("ct_bool_{op}");
        add(
            &name,
            "a: bool, b: bool",
            "bool",
            &format!("{name}(secret(a), secret(b))"),
        );
    }
    add("ct_bool_not", "a: bool", "bool", "ct_bool_not(secret(a))");
    add(
        "ct_bool_select",
        "c: bool, a: bool, b: bool",
        "bool",
        "ct_bool_select(secret(c), secret(a), secret(b))",
    );
    out
}

#[test]
fn secret_words_have_no_conditional_branch() {
    let dir = std::env::temp_dir().join(format!("tauto-ct-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!("../src/ct.rs").replace("#[cfg(test)]", "#[cfg(any())]");
    let lib = dir.join("probe.rs");
    // `ct.rs` names the runtime's byte list; a vector stands in for it here.
    let stdlib = "mod stdlib { pub type Bytes = Vec<u8>; }";
    std::fs::write(&lib, format!("{source}\n{stdlib}\n{}", wrappers())).unwrap();
    let asm = dir.join("probe.s");
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let out = Command::new(rustc)
        .args([
            "--edition",
            "2024",
            "--crate-type",
            "cdylib",
            "-C",
            "opt-level=3",
        ])
        .args(["--emit", "asm", "-o"])
        .arg(&asm)
        .arg(&lib)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = std::fs::read_to_string(&asm).unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    let mut probes = 0;
    let mut current: Option<&str> = None;
    let mut branches = Vec::new();
    for line in text.lines() {
        if let Some(label) = line.strip_suffix(':')
            && !label.starts_with('.')
            && !label.starts_with(char::is_whitespace)
        {
            current = label.strip_prefix("probe_");
            probes += usize::from(current.is_some());
            continue;
        }
        let Some(name) = current else { continue };
        let op = line.split_whitespace().next().unwrap_or("");
        if op.starts_with('j') && op != "jmp" && !op.starts_with("jmp") {
            branches.push(format!("{name}: {}", line.trim()));
        }
    }
    assert_eq!(
        probes,
        wrappers().lines().count(),
        "every probe is in the assembly"
    );
    assert!(branches.is_empty(), "conditional branches: {branches:#?}");
}
