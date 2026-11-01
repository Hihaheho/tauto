//! Local documentation of source declarations and their kernel verdicts.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use tauto::check::{Verdict, describe};
use tauto::program::{self, Loaded};
use tauto::report::{Report, Status};
use tauto::surface::{FnDecl, Stmt, SurfaceTerm, TheoremDecl};

pub fn command(args: &[String]) -> ExitCode {
    if args == ["--help"] || args == ["-h"] {
        println!("{}", crate::i18n::t!("doc-help"));
        return ExitCode::SUCCESS;
    }
    let mut input = None;
    let mut output = None;
    let mut rest = args.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "-o" if output.is_none() => match rest.next() {
                Some(value) if !value.starts_with('-') => output = Some(PathBuf::from(value)),
                _ => return usage(),
            },
            value if !value.starts_with('-') && input.is_none() => {
                input = Some(PathBuf::from(value))
            }
            _ => return usage(),
        }
    }
    let Some(input) = input else { return usage() };
    let output = output.unwrap_or_else(|| PathBuf::from("target/tauto/doc"));
    match generate(&input, &output) {
        Ok(status) => {
            println!("{}", output.join("index.html").display());
            match status {
                Status::Ok => ExitCode::SUCCESS,
                Status::Failed => ExitCode::FAILURE,
                Status::Incomplete => ExitCode::from(3),
            }
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

fn usage() -> ExitCode {
    eprintln!("{}", crate::i18n::t!("doc-usage"));
    ExitCode::from(2)
}

fn generate(input: &Path, output: &Path) -> Result<Status, String> {
    // Even an empty directory or dangling symlink belongs to the caller.
    match fs::symlink_metadata(output) {
        Ok(_) => {
            return Err(crate::i18n::t!(
                "doc-output-exists",
                path = output.display().to_string()
            ));
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(format!("{}: {e}", output.display())),
    }
    let package = if input.is_dir() {
        Some(input)
    } else if input.file_name().is_some_and(|n| n == "Tauto.eure") {
        Some(input.parent().unwrap_or(Path::new(".")))
    } else {
        None
    };
    let roots = match package {
        Some(dir) => program::tote_inputs(dir)?
            .into_iter()
            .filter(|p| tauto::program::is_source_file(p))
            .collect(),
        None => vec![input.to_path_buf()],
    };
    if roots.is_empty() {
        return Err(crate::i18n::t!("doc-no-sources"));
    }
    let loaded = program::load_roots(&roots)?;
    // Mixed modules retain logical declarations without treating executable
    // functions as proofs; no top-level runtime expression is evaluated.
    let checked = tauto::check::check_tote_files(&roots, true)?;
    let sources = loaded
        .files
        .iter()
        .map(|f| (program::canonical_path(&f.path), f.text.clone()))
        .collect();
    let report = Report::from_parts(
        checked.entries,
        tauto::check::expansion_infos(&loaded),
        sources,
    );
    let base = program::canonical_path(
        package.unwrap_or_else(|| input.parent().unwrap_or(Path::new("."))),
    );
    let html = render(&loaded, &report, &base)?;
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    fs::create_dir_all(parent).map_err(|e| format!("{}: {e}", parent.display()))?;
    fs::create_dir(output).map_err(|e| format!("{}: {e}", output.display()))?;
    // The output name is constant: input paths and declaration names are
    // labels and numeric fragment anchors, never output filesystem paths.
    let path = output.join("index.html");
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    file.write_all(html.as_bytes())
        .map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(report.status())
}

fn escape(text: &str) -> String {
    let mut out = String::new();
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

struct Declaration {
    name: String,
    kind: &'static str,
    signature: String,
    start: u32,
    axiom: bool,
    obligation: bool,
}

fn generics(names: &[String], bounds: &[Option<String>]) -> String {
    if names.is_empty() {
        return String::new();
    }
    let items = names
        .iter()
        .enumerate()
        .map(|(i, n)| {
            tauto::surface::print::written_generic(
                n,
                bounds.get(i).and_then(Option::as_deref),
                false,
            )
        })
        .collect::<Vec<_>>();
    format!("<{}>", items.join(", "))
}

/// `(A: Type, B: Type)`: the parameters of a type declaration.
fn type_params(names: &[String], rows: &[bool]) -> String {
    if names.is_empty() {
        return String::new();
    }
    let items = names
        .iter()
        .enumerate()
        .map(|(i, n)| {
            if rows.get(i).copied().unwrap_or(false) {
                format!("!{n}")
            } else {
                format!("{n}: Type")
            }
        })
        .collect::<Vec<_>>();
    format!("({})", items.join(", "))
}

fn function(f: &FnDecl) -> String {
    let params = f
        .params
        .iter()
        .enumerate()
        .map(|(i, n)| {
            let borrow = match f.borrows.get(i).copied().flatten() {
                Some(true) => "&mut ",
                Some(false) => "&",
                None => "",
            };
            match f.param_types.get(i).and_then(Option::as_ref) {
                Some(ty) => format!("{borrow}{n}: {}", describe(ty)),
                None => format!("{borrow}{n}: (inferred)"),
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    let mut s = format!(
        "fn {}{}({params})",
        f.name,
        generics(&f.generics, &f.bounds)
    );
    if let Some(ty) = &f.result {
        write!(s, ": {}", describe(ty)).unwrap();
    }
    if let Some(effects) = &f.effects {
        write!(s, " ! {{{}}}", effects.join(", ")).unwrap();
    }
    if !f.where_.is_empty() {
        write!(
            s,
            " where {}",
            f.where_
                .iter()
                .map(|c| format!("{}({})", c.class, describe(&c.ty)))
                .collect::<Vec<_>>()
                .join(", ")
        )
        .unwrap();
    }
    s
}

fn theorem(t: &TheoremDecl, kind: &str) -> String {
    let params = |items: &[(String, tauto::surface::SurfaceTerm)]| {
        items
            .iter()
            .map(|(n, ty)| format!("{n}: {}", describe(ty)))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let implicit = t.implicit.min(t.params.len());
    let generic = if implicit == 0 {
        String::new()
    } else {
        format!("<{}>", params(&t.params[..implicit]))
    };
    format!(
        "{kind} {}{generic}({}): {}",
        t.name,
        params(&t.params[implicit..]),
        describe(&t.ty)
    )
}

fn declarations(stmts: &[Stmt], out: &mut Vec<Declaration>) {
    for stmt in stmts {
        let (name, kind, signature, start, axiom) = match stmt {
            Stmt::Fn(f) => (f.name.clone(), "fn", function(f), f.span.start, false),
            Stmt::Theorem(t) | Stmt::Def(t) => {
                let axiom = matches!(stmt, Stmt::Theorem(_)) && t.body.is_none();
                let kind = if axiom {
                    "axiom"
                } else if matches!(stmt, Stmt::Def(_)) {
                    "def"
                } else {
                    "theorem"
                };
                (t.name.clone(), kind, theorem(t, kind), t.span.start, axiom)
            }
            Stmt::Inductive(d) => {
                // Without parentheses when there are no parameters.
                let parens = |ps: &[(String, SurfaceTerm)]| {
                    if ps.is_empty() {
                        String::new()
                    } else {
                        format!(
                            "({})",
                            ps.iter()
                                .map(|(n, t)| format!("{n}: {}", describe(t)))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                };
                let mut s = format!(
                    "inductive {}{}: {}",
                    d.name,
                    parens(&d.params),
                    describe(&d.sort)
                );
                for c in &d.constructors {
                    let implicit = c.implicit.min(c.params.len());
                    let generic = if implicit == 0 {
                        String::new()
                    } else {
                        format!(
                            "<{}>",
                            c.params[..implicit]
                                .iter()
                                .map(|(n, t)| format!("{n}: {}", describe(t)))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    };
                    write!(
                        s,
                        "\n  {}{generic}{}: {}",
                        c.name,
                        parens(&c.params[implicit..]),
                        describe(&c.result)
                    )
                    .unwrap();
                }
                (d.name.clone(), "inductive", s, d.span.start, false)
            }
            Stmt::Struct(d) | Stmt::Enum(d) => {
                let kind = if matches!(stmt, Stmt::Struct(_)) {
                    "struct"
                } else {
                    "enum"
                };
                let mut s = format!(
                    "{}{} {}{}",
                    d.kind.as_ref().map_or(String::new(), |k| format!("{k} ")),
                    kind,
                    d.name,
                    type_params(&d.generics, &d.rows)
                );
                for c in &d.constructors {
                    write!(
                        s,
                        "\n  {}({})",
                        c.name,
                        c.fields
                            .iter()
                            .map(|(n, t)| match n {
                                Some(n) => format!("{n}: {}", describe(t)),
                                None => describe(t),
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                    .unwrap();
                }
                (d.name.clone(), kind, s, d.span.start, false)
            }
            Stmt::Class(c) => {
                let mut s = format!(
                    "class {}({}: {})",
                    c.name,
                    c.param,
                    c.bound.as_deref().unwrap_or("Type")
                );
                for f in &c.methods {
                    write!(s, "\n  {}", function(f)).unwrap();
                }
                for law in &c.laws {
                    write!(s, "\n  {}", theorem(&law.theorem, "law (obligation)")).unwrap();
                }
                (c.name.clone(), "class", s, c.span.start, false)
            }
            Stmt::Instance(i) => {
                let name = format!("{}({})", i.class, describe(&i.head));
                let mut s = format!("instance{} {name}", generics(&i.generics, &i.bounds));
                if !i.where_.is_empty() {
                    write!(
                        s,
                        " where {}",
                        i.where_
                            .iter()
                            .map(|c| format!("{}({})", c.class, describe(&c.ty)))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                    .unwrap();
                }
                for f in &i.methods {
                    write!(s, "\n  {}", function(f)).unwrap();
                }
                for law in &i.laws {
                    write!(s, "\n  {}", theorem(&law.theorem, "law")).unwrap();
                }
                (name, "instance", s, i.span.start, false)
            }
            Stmt::Effect(e) => {
                let mut s = format!(
                    "effect {}{}({}): {}",
                    e.name,
                    generics(&e.generics, &[]),
                    e.params
                        .iter()
                        .map(|t| t
                            .as_ref()
                            .map(describe)
                            .unwrap_or_else(|| "(inferred)".into()))
                        .collect::<Vec<_>>()
                        .join(", "),
                    e.result
                        .as_ref()
                        .map(describe)
                        .unwrap_or_else(|| "()".into())
                );
                if let Some(resume) = &e.resume {
                    if resume == "direct" {
                        s.push_str(" direct");
                    } else {
                        write!(s, " resume {resume}").unwrap();
                    }
                }
                (e.name.clone(), "effect", s, e.span.start, false)
            }
            Stmt::Extern { fns, .. } => {
                for f in fns {
                    out.push(Declaration {
                        name: f.name.clone(),
                        kind: "extern",
                        signature: format!("extern {}", function(f)),
                        start: f.span.start,
                        axiom: false,
                        obligation: false,
                    });
                }
                continue;
            }
            Stmt::Mutual { items, .. } | Stmt::Module { items, .. } => {
                declarations(items, out);
                continue;
            }
            Stmt::Attributed { stmt, .. } => {
                declarations(std::slice::from_ref(stmt.as_ref()), out);
                continue;
            }
            _ => continue,
        };
        out.push(Declaration {
            name,
            kind,
            signature,
            start,
            axiom,
            obligation: matches!(stmt, Stmt::Class(_)),
        });
    }
}

fn source_place(loaded: &Loaded, start: u32) -> Option<(&Path, usize, usize)> {
    let mut offset = start;
    while let Some((written, _)) = loaded.spans.origin(offset) {
        offset = written;
    }
    // Lowering can assign synthetic spans without a written origin. Do not
    // clamp those spans to the final line and present a fictitious source link.
    loaded.files.iter().find(|f| {
        offset >= f.base && u64::from(offset) <= u64::from(f.base) + f.text.len() as u64
    })?;
    loaded.locate(start)
}

fn render(loaded: &Loaded, report: &Report, base: &Path) -> Result<String, String> {
    let mut out = String::from(
        "<!doctype html>\n<html lang=\"en\"><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width\"><title>Tauto documentation</title>\n<style>body{max-width:80em;margin:2em auto;padding:0 1em;font-family:system-ui}pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#eee;padding:1em}section{border-top:1px solid #aaa;padding:1em 0}a{color:#1458a0}.source-line{display:block}h2{overflow-wrap:anywhere}</style>\n<h1>Tauto documentation</h1>\n",
    );
    write!(out, "<p>Proof check: <strong>{}</strong>. Checked declarations may depend on the axioms listed below. Runtime signatures and extern implementations are not type-checked or proof-checked. Class laws are obligations, not proofs.</p>\n", report.status().name()).unwrap();
    let files: BTreeMap<_, _> = report
        .files()
        .enumerate()
        .map(|(id, (p, text))| (p.to_path_buf(), (id, text)))
        .collect();
    let mut decls = Vec::new();
    // Runtime lowering erases class and instance declarations and rewrites
    // signatures. Read the written API through the same surface parser, then
    // retain declarations made by syntax and macros that have no written API.
    for file in &loaded.files {
        let written = tauto::surface::parse_program_as_written_at(&file.text, file.base)?;
        declarations(&written.stmts, &mut decls);
    }
    let written: std::collections::BTreeSet<_> = decls
        .iter()
        .map(|d| {
            (
                d.name.clone(),
                source_place(loaded, d.start).map(|(p, _, _)| program::canonical_path(p)),
            )
        })
        .collect();
    let mut generated = Vec::new();
    for stmts in &loaded.per_file {
        declarations(stmts, &mut generated);
    }
    for d in generated {
        let key = (
            d.name.clone(),
            source_place(loaded, d.start).map(|(p, _, _)| program::canonical_path(p)),
        );
        if !written.contains(&key) {
            decls.push(d);
        }
    }
    decls.sort_by(|a, b| (&a.name, a.start).cmp(&(&b.name, b.start)));
    for (id, d) in decls.iter().enumerate() {
        let place = source_place(loaded, d.start);
        let file = place.map(|(p, _, _)| program::canonical_path(p));
        let entries = report
            .entries
            .iter()
            .filter(|e| e.entry.name == d.name && file.as_ref().is_some_and(|f| *f == e.file))
            .collect::<Vec<_>>();
        let verdict = entries
            .iter()
            .find(|e| matches!(e.entry.verdict, Verdict::Failed(_)))
            .or_else(|| {
                entries
                    .iter()
                    .find(|e| matches!(e.entry.verdict, Verdict::Incomplete { .. }))
            })
            .or_else(|| entries.first());
        let state = match verdict.map(|e| &e.entry.verdict) {
            Some(Verdict::Checked { .. }) if d.axiom => "axiom (assumption, not a proof)",
            Some(Verdict::Checked { .. }) => "checked",
            Some(Verdict::Incomplete { .. }) => "incomplete (not accepted)",
            Some(Verdict::Failed(_)) => "failed (not accepted)",
            Some(Verdict::Skipped(_)) => "skipped (not proof-checked)",
            None => "not proof-checked",
        };
        write!(
            out,
            "<section id=\"decl-{id}\"><h2>{} <code>{}</code></h2><p>{}</p><pre>{}</pre>\n",
            d.kind,
            escape(&d.name),
            state,
            escape(&d.signature)
        )
        .unwrap();
        if d.obligation {
            out.push_str("<p>Law fields are obligations for instances; this declaration does not supply their proofs.</p>\n");
        }
        if let Some(entry) = verdict {
            match &entry.entry.verdict {
                Verdict::Checked { axioms } => {
                    write!(
                        out,
                        "<p>Axiom dependencies: {}</p>\n",
                        if axioms.is_empty() {
                            "none".into()
                        } else {
                            escape(&axioms.join(", "))
                        }
                    )
                    .unwrap();
                }
                Verdict::Failed(d) => {
                    write!(
                        out,
                        "<p>Diagnostic: {}</p>\n",
                        escape(&d.message.to_string())
                    )
                    .unwrap();
                }
                Verdict::Skipped(reason) => {
                    write!(out, "<p>{}</p>\n", escape(reason)).unwrap();
                }
                Verdict::Incomplete { holes, uses } => {
                    write!(
                        out,
                        "<p>Holes: {}. Incomplete dependencies: {}</p>\n",
                        escape(
                            &holes
                                .iter()
                                .map(|h| h.name.clone())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                        escape(&uses.join(", "))
                    )
                    .unwrap();
                }
            }
        }
        if let Some((p, line, _)) = place {
            if let Some((source, _)) = files.get(&program::canonical_path(p)) {
                write!(
                    out,
                    "<p><a href=\"#source-{source}-L{line}\">{}:{line}</a></p>\n",
                    escape(&p.strip_prefix(base).unwrap_or(p).display().to_string())
                )
                .unwrap();
            }
        }
        out.push_str("</section>\n");
    }
    out.push_str("<h2>Check report</h2><pre>");
    out.push_str(&escape(&report.text()));
    out.push_str("</pre>\n<h2>Source snapshots</h2>\n");
    for (path, (id, text)) in files {
        write!(
            out,
            "<section id=\"source-{id}\"><h3>{}</h3><pre>",
            escape(
                &path
                    .strip_prefix(base)
                    .unwrap_or(&path)
                    .display()
                    .to_string()
            )
        )
        .unwrap();
        for (line, text) in text.split('\n').enumerate() {
            write!(
                out,
                "<span class=\"source-line\" id=\"source-{id}-L{}\">{}</span>",
                line + 1,
                escape(text)
            )
            .unwrap();
        }
        out.push_str("</pre></section>\n");
    }
    out.push_str("</html>\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    #[test]
    fn escapes_html_text_and_attribute_delimiters() {
        assert_eq!(
            super::escape("<&>\"' 日本語"),
            "&lt;&amp;&gt;&quot;&#39; 日本語"
        );
    }
}
