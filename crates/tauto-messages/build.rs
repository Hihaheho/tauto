//! Gathers the messages: each directory `locales/LANG` is one language, its
//! `.ftl` files read in name order. The tote `totes/fluent` is compiled into
//! `src/fluent.rs` ahead of time, since tauto-build itself writes messages.

use std::path::Path;

fn main() {
    println!("cargo:rerun-if-changed=locales");
    let mut langs: Vec<_> = std::fs::read_dir("locales")
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .collect();
    langs.sort();
    // English first: the language a missing message is taken from.
    langs.sort_by_key(|p| p.file_name().is_none_or(|n| n != "en"));
    let out = std::env::var_os("OUT_DIR").unwrap();
    let mut table = String::from("&[\n");
    for dir in langs {
        let lang = dir.file_name().unwrap().to_str().unwrap().to_string();
        println!("cargo:rerun-if-changed={}", dir.display());
        let mut files: Vec<_> = std::fs::read_dir(&dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|e| e == "ftl"))
            .collect();
        files.sort();
        let mut text = String::new();
        for f in files {
            println!("cargo:rerun-if-changed={}", f.display());
            text += &std::fs::read_to_string(&f).unwrap();
            text += "\n";
        }
        let target = Path::new(&out).join(format!("locale_{lang}.ftl"));
        std::fs::write(&target, text).unwrap();
        table += &format!(
            "    ({lang:?}, include_str!({:?})),\n",
            target.display().to_string()
        );
    }
    table += "]\n";
    std::fs::write(Path::new(&out).join("locales.rs"), table).unwrap();
}
