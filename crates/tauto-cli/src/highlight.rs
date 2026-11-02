//! `tauto highlight [--tokens] [--timings] [--repeat N [--edit]] FILE`: the file coloured as an
//! editor colours it (`tauto_analyzer::editor::dsl_tokens`, the tokens `tauto lsp` answers
//! with).

use std::path::Path;
use std::process::ExitCode;
use std::time::Instant;

use crate::i18n;

pub fn command(args: &[String]) -> ExitCode {
    let (mut tokens, mut timings, mut edit, mut repeat, mut file) = (false, false, false, 1, None);
    let mut args = args.iter();
    while let Some(a) = args.next() {
        match a.as_str() {
            "--tokens" => tokens = true,
            "--timings" => timings = true,
            "--edit" => edit = true,
            "--repeat" => match args.next().and_then(|n| n.parse::<usize>().ok()) {
                Some(n) if n > 0 => repeat = n,
                _ => return usage(),
            },
            _ if a.starts_with('-') || file.is_some() => return usage(),
            _ => file = Some(a.as_str()),
        }
    }
    let Some(file) = file else {
        return usage();
    };
    if edit && repeat == 1 {
        return usage();
    }
    let path = Path::new(file);
    let mut text = match std::fs::read_to_string(path) {
        Ok(text) => text,
        Err(e) => {
            eprintln!(
                "{}",
                i18n::t!("highlight-error", error = format!("{file}: {e}"))
            );
            return ExitCode::from(2);
        }
    };
    // Read again, the file is read as `tauto lsp` reads it: what the reading before left is kept.
    tauto::program::keep_expansions(repeat > 1);
    let mut found = Vec::new();
    for run in 0..repeat {
        if edit && run > 0 {
            text.push('\n');
        }
        let start = Instant::now();
        let (result, phases) =
            tauto::phases::recorded(|| tauto_analyzer::editor::dsl_tokens(path, &text));
        let total = start.elapsed();
        found = match result {
            Ok((found, _)) => found,
            Err(e) => {
                eprintln!("{}", i18n::t!("highlight-error", error = e));
                return ExitCode::from(1);
            }
        };
        if timings {
            if repeat > 1 {
                eprintln!("#{}", run + 1);
            }
            for (name, d) in phases.iter().filter(|(_, d)| !d.is_zero()) {
                eprintln!("{name:>10} {:>10.3} ms", d.as_secs_f64() * 1e3);
            }
            eprintln!(
                "{:>10} {:>10.3} ms",
                i18n::t!("highlight-total"),
                total.as_secs_f64() * 1e3
            );
        }
    }
    if tokens {
        for t in &found {
            println!("{}", tauto_analyzer::editor::token_line(&text, t));
        }
    } else {
        print!("{}", coloured(&text, &found));
    }
    ExitCode::SUCCESS
}

fn usage() -> ExitCode {
    eprintln!("{}", i18n::t!("highlight-usage"));
    ExitCode::from(2)
}

/// The text with each token in the colour of its kind (ANSI escapes).
fn coloured(text: &str, tokens: &[tauto_analyzer::editor::DslToken]) -> String {
    let mut out = String::new();
    let mut at = 0;
    for t in tokens {
        if t.start < at {
            continue;
        }
        out.push_str(&text[at..t.start]);
        out.push_str(&format!(
            "\x1b[{}m{}\x1b[0m",
            ansi(t.kind),
            &text[t.start..t.end]
        ));
        at = t.end;
    }
    out.push_str(&text[at..]);
    out
}

/// The ANSI colour of a kind of token.
fn ansi(kind: &str) -> &'static str {
    match kind {
        "keyword" | "modifier" => "35",
        "number" | "enumMember" => "36",
        "string" | "regexp" => "32",
        "comment" => "90",
        "type" | "struct" | "enum" | "class" | "interface" | "typeParameter" => "33",
        "function" | "method" | "macro" | "decorator" => "34",
        "parameter" | "property" | "event" => "31",
        "namespace" => "1;33",
        "operator" => "37",
        _ => "39",
    }
}
