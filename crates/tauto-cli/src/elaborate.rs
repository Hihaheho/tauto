//! `tauto elaborate FILE [NAME] [--json]`: the term the kernel checks for
//! each body of the file, with what the elaborator filled in written out.
use std::path::Path;
use std::process::ExitCode;

use tauto::check::{describe, elaborate_file};
use tauto::report::{Json, term_json};

use crate::i18n;

const USAGE: &str = "tauto elaborate FILE [NAME] [--json]";

pub fn command(args: &[String]) -> ExitCode {
    let mut json = false;
    let mut positional = Vec::new();
    for a in args {
        match a.as_str() {
            "--json" => json = true,
            a if a.starts_with('-') => return usage(),
            a => positional.push(a),
        }
    }
    let (path, only) = match positional[..] {
        [path] => (path, None),
        [path, name] => (path, Some(name)),
        _ => return usage(),
    };
    let path = Path::new(path);
    let (entries, terms) = match elaborate_file(path) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::FAILURE;
        }
    };
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let names: Vec<&tauto::surface::Name> = entries
        .iter()
        .filter(|e| e.file == own)
        .map(|e| &e.entry.name)
        .filter(|n| only.is_none_or(|o| o == n.as_str()))
        .collect();
    // A body is elaborated once per declaration; the last one is the one kept.
    let shown: Vec<_> = names
        .iter()
        .filter_map(|n| terms.iter().rev().find(|(t, _)| t == *n))
        .collect();
    if let Some(name) = only
        && shown.is_empty()
    {
        eprintln!(
            "{}",
            i18n::t!(
                "elaborate-no-body",
                path = path.display().to_string(),
                name = name
            )
        );
        return ExitCode::FAILURE;
    }
    if json {
        let items = shown.iter().map(|(name, term)| {
            Json::Obj(vec![
                ("name", Json::Str(name.to_string())),
                ("term", Json::Str(describe(term))),
                ("tree", term_json(term)),
            ])
        });
        println!("{}", Json::Arr(items.collect()).render());
    } else {
        for (name, term) in shown {
            println!("{name} := {}", describe(term));
        }
    }
    ExitCode::SUCCESS
}

fn usage() -> ExitCode {
    eprintln!("{}", i18n::t!("elaborate-usage", usage = USAGE));
    ExitCode::from(2)
}
