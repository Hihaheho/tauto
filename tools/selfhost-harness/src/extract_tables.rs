//! The tables of `totes/extract/src/tables`, made from the host: the names the
//! library takes, the helpers as the host writes them, what the host maps the
//! declarations of `std/` onto, and the runtime of lowered data.

/// Each table's file name and what it holds now.
pub fn tables() -> Vec<(&'static str, String)> {
    let b = tauto::bindings::library_bindings();
    let mut taken = std::collections::BTreeSet::new();
    for (t, _) in b.bindings() {
        taken.insert(t.to_string());
        taken.extend(t.split("::").map(str::to_string));
    }
    let names: Vec<_> = taken.into_iter().collect();
    let dir = std::env::temp_dir().join(format!("extract-tables-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("one.taut");
    std::fs::write(&path, "inductive U: Type {\n  Mk: U\n}\n").unwrap();
    let host = tauto::extract::extract_files(&[path]).unwrap();
    let helpers: String = host
        .lines()
        .skip(1)
        .take_while(|l| !l.starts_with("enum(shared) U"))
        .map(|l| format!("{l}\n"))
        .collect();
    // What the host adds once the library's `Text` is loaded: the helpers of texts.
    let with_text = dir.join("with-text.taut");
    std::fs::write(&with_text, "import std::text\ninductive U: Type {\n  Mk: U\n}\n").unwrap();
    let host_text = tauto::extract::extract_files(&[with_text]).unwrap();
    let all_text: Vec<&str> = host_text
        .lines()
        .skip(1)
        .take_while(|l| !l.starts_with("enum(shared) U"))
        .collect();
    let base = helpers.lines().count();
    let text_helpers: String = all_text.iter().skip(base).map(|l| format!("{l}\n")).collect();
    assert!(!text_helpers.is_empty(), "{host_text}");
    // The runtime of lowered data, as the host writes it after the variants.
    let lowered = dir.join("lowered.taut");
    std::fs::write(&lowered, "inductive U: Type {\n  Mk: U\n}\ninductive I: U -> Type {\n  Mk: I(U::Mk)\n}\nfn f(A: Type, i: I(U::Mk)): U { U::Mk }\n").unwrap();
    let host = tauto::extract::extract_files(&[lowered]).unwrap();
    let runtime: String = host
        .lines()
        .skip_while(|l| !l.starts_with("fn TautoErasedGetNat_1"))
        .take_while(|l| !l.starts_with("fn TautoErasedFn"))
        .map(|l| format!("{l}\n"))
        .collect();
    assert!(!runtime.is_empty(), "{host}");
    let table = |rows: &[(&str, &str)]| -> String { rows.iter().map(|(n, m)| format!("{n}\t{m}\n")).collect() };
    vec![
        ("library-names.txt", names.join("\n")),
        ("helpers.txt", helpers),
        ("text-helpers.txt", text_helpers),
        ("mapped-fns.txt", table(tauto::extract::MAPPED_FNS)),
        ("mapped-types.txt", table(tauto::extract::MAPPED_TYPES)),
        ("erased-runtime.txt", runtime),
    ]
}
