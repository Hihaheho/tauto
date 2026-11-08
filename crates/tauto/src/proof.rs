//! Presentations of judgments recorded by the core kernel.
use crate::check::{
    Derivation, FileEntry, InferenceRule as Rule, Kernel, Verdict, declare_prelude,
};
use crate::surface::print::print_term as show;
use crate::surface::{Name, Stmt, SurfaceTerm, TheoremDecl};
use std::{fmt::Write, path::Path};
mod json;
mod natural;
mod notation;
use tauto_message::{Message, msg};

#[derive(Clone, Copy, Debug, Default)]
pub enum Format {
    Block,
    Node,
    Tree,
    TreeHtml,
    Json,
    #[default]
    Natural,
}
impl Format {
    pub fn parse(name: &str) -> Option<Self> {
        Some(match name {
            "block" => Self::Block,
            "node" => Self::Node,
            "tree" => Self::Tree,
            "tree-html" => Self::TreeHtml,
            "json" => Self::Json,
            "natural" => Self::Natural,
            _ => return None,
        })
    }
}

pub struct View {
    pub text: String,
    pub failed: bool,
    pub incomplete: bool,
}

/// Each displayed inference comes from a core check, without the proof cache.
pub fn render_file(path: &Path, only: Option<&str>, format: Format) -> Result<View, Message> {
    render_file_with(path, only, format, Options::default())
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Options {
    pub full: bool,
}

pub fn render_file_with(
    path: &Path,
    only: Option<&str>,
    format: Format,
    options: Options,
) -> Result<View, Message> {
    let loaded = crate::program::load_with_text_in(path, None)?;
    render_loaded(&loaded, path, only, format, options)
}

/// Presents a loaded editor snapshot using the same checks and notation as the CLI.
pub fn render_loaded(
    loaded: &crate::program::Loaded,
    path: &Path,
    only: Option<&str>,
    format: Format,
    options: Options,
) -> Result<View, Message> {
    if !loaded.program.errors.is_empty() {
        return Err(Message::text(
            loaded
                .program
                .errors
                .iter()
                .map(|(message, _)| message.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        ));
    }
    let own = crate::program::canonical_path(path);
    let index = loaded
        .files
        .iter()
        .position(|f| crate::program::canonical_path(&f.path) == own)
        .ok_or_else(|| msg!("proof-no-theorem").to_string())?;
    let mut declarations = Vec::new();
    theorems(&loaded.kernel_files[index], &mut declarations);
    declarations.retain(|d| only.is_none_or(|name| name == d.name.as_str()));
    if declarations.is_empty() {
        return Err(msg!("proof-no-theorem"));
    }
    let mut kernel = Kernel::new();
    declare_prelude(&mut kernel)?;
    kernel.record_derivations(
        &declarations
            .iter()
            .map(|d| d.name.clone())
            .collect::<Vec<_>>(),
    );
    kernel.record_elaborated();
    let entries = crate::read::declare_loaded(&mut kernel, loaded)?;
    if matches!(format, Format::Json) {
        return json::render(
            &declarations,
            &entries,
            kernel.derivations(),
            &own,
            !loaded.program.errors.is_empty(),
        );
    }
    let library = kernel.library();
    let mut inspector = kernel.proof_inspector();
    let html = matches!(format, Format::Block | Format::Node | Format::TreeHtml);
    let mut out = String::new();
    if html {
        out.push_str(HTML_HEAD);
        write!(
            out,
            "<title>{}</title></head><body><main>",
            esc(&msg!("proof-title").to_string())
        )
        .unwrap();
    }
    for (group, d) in declarations.iter().enumerate() {
        let matching: Vec<_> = entries
            .iter()
            .filter(|e| e.file == own && e.entry.name == d.name)
            .collect();
        let [entry] = matching.as_slice() else {
            return Err(msg!("proof-ambiguous", name = d.name.to_string()));
        };
        let status = verdict(entry);
        let notation = notation::Notation::new(loaded, &kernel, d);
        if html {
            write!(out, "<section><h1>{}</h1>", esc(&d.name)).unwrap();
            if let Some(status) = &status {
                write!(out, "<p class=status>{}</p>", esc(status)).unwrap();
            }
            write!(
                out,
                "<p class=statement>⊢ {}</p>",
                esc(&notation.show(&d.ty, &d.params, false))
            )
            .unwrap();
        } else {
            if let Some(status) = &status {
                writeln!(out, "{} [{}]", d.name, status).unwrap();
            } else {
                writeln!(out, "{}", d.name).unwrap();
            }
            if !matches!(format, Format::Natural) {
                writeln!(out, "⊢ {}", notation.show(&d.ty, &d.params, false)).unwrap();
            }
        }
        let recorded = kernel
            .derivations()
            .iter()
            .rev()
            .find(|(n, _)| n == &d.name)
            .map(|(_, tree)| tree);
        if let Some(mut root) = recorded {
            // Declaration parameters are the hypotheses of the displayed proof.
            for _ in 0..if options.full { 0 } else { d.params.len() } {
                if root.rule == Rule::Introduction && root.premises.len() == 1 {
                    root = &root.premises[0];
                }
            }
            let mut scopes = Scopes {
                notation,
                ..Scopes::default()
            };
            scopes.collect(root);
            if html {
                write!(
                    out,
                    "<h2>{}</h2><p class=note>{}</p>",
                    esc(&judgment(root, &scopes)),
                    esc(&msg!("proof-derivation-note").to_string())
                )
                .unwrap();
                scopes.html(&mut out);
                match format {
                    Format::Block => blocks(root, &scopes, &mut out),
                    Format::Node => graph(root, &scopes, group, &mut out),
                    Format::TreeHtml => {
                        out.push_str("<div class=tree-scroll>");
                        html_tree(root, &scopes, &mut out);
                        out.push_str("</div>");
                    }
                    _ => unreachable!(),
                }
            } else {
                match format {
                    Format::Tree => {
                        scopes.text(&mut out);
                        for line in inference_tree(root, &scopes).lines {
                            writeln!(out, "{line}").unwrap();
                        }
                    }
                    Format::Natural => {
                        if options.full {
                            natural::render_full(root, &scopes, &mut out);
                        } else {
                            natural::render(
                                root,
                                &library,
                                &mut inspector,
                                &scopes.notation,
                                &mut out,
                            );
                        }
                    }
                    _ => unreachable!(),
                }
                out.push('\n');
            }
        } else {
            let note = msg!("proof-no-derivation").to_string();
            if html {
                write!(out, "<p class=unavailable>{}</p>", esc(&note)).unwrap();
            } else {
                writeln!(out, "{note}").unwrap();
            }
        }
        if html {
            out.push_str("</section>");
        }
    }
    if html {
        out.push_str("</main></body></html>\n");
    }
    Ok(View {
        text: out,
        failed: entries
            .iter()
            .any(|e| matches!(e.entry.verdict, Verdict::Failed(_)))
            || !loaded.program.errors.is_empty(),
        incomplete: entries
            .iter()
            .any(|e| matches!(e.entry.verdict, Verdict::Incomplete { .. })),
    })
}

fn theorems<'a>(stmts: &'a [Stmt], out: &mut Vec<&'a TheoremDecl>) {
    for stmt in stmts {
        match stmt {
            Stmt::Theorem(d) if d.body.is_some() => out.push(d),
            Stmt::Mutual { items, .. } => theorems(items, out),
            _ => {}
        }
    }
}
fn verdict(entry: &FileEntry) -> Option<String> {
    Some(match &entry.entry.verdict {
        Verdict::Checked { axioms } if axioms.is_empty() => return None,
        Verdict::Checked { axioms } => msg!(
            "proof-axioms",
            names = axioms
                .iter()
                .map(Name::as_str)
                .collect::<Vec<_>>()
                .join(", ")
        )
        .to_string(),
        Verdict::Incomplete { holes, uses } => {
            let mut details = holes
                .iter()
                .map(|h| {
                    let context = h
                        .context
                        .iter()
                        .map(|(n, t)| format!("{n}: {}", show(t)))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("?{}: {} [{}]", h.name, show(&h.goal), context)
                })
                .collect::<Vec<_>>();
            details.extend(uses.iter().map(ToString::to_string));
            msg!("proof-incomplete", details = details.join("; ")).to_string()
        }
        Verdict::Failed(d) => msg!("proof-failed", details = d.to_string()).to_string(),
        Verdict::Skipped(reason) => msg!("proof-skipped", details = reason.clone()).to_string(),
    })
}

/// Bound variables may be renamed when core writes a type. Free references
/// still compare by their declaration or local identity.
fn same_term(a: &SurfaceTerm, b: &SurfaceTerm) -> bool {
    use crate::surface::TermKind;
    fn go(a: &SurfaceTerm, b: &SurfaceTerm, bound: &[(Name, Name)]) -> bool {
        match (&*a.kind, &*b.kind) {
            (TermKind::Var(a), TermKind::Var(b)) => {
                match bound.iter().rev().find(|(left, _)| left == a) {
                    Some((_, right)) => right == b,
                    None => a == b && !bound.iter().any(|(_, right)| right == b),
                }
            }
            (
                TermKind::App {
                    function: af,
                    arguments: aa,
                },
                TermKind::App {
                    function: bf,
                    arguments: ba,
                },
            ) => {
                aa.len() == ba.len()
                    && go(af, bf, bound)
                    && aa.iter().zip(ba).all(|(a, b)| go(a, b, bound))
            }
            (
                TermKind::Pi {
                    params: ap,
                    result: ar,
                    effects: ae,
                },
                TermKind::Pi {
                    params: bp,
                    result: br,
                    effects: be,
                },
            ) => {
                if ap.len() != bp.len() || ae != be {
                    return false;
                }
                let mut inner = bound.to_vec();
                for ((an, at), (bn, bt)) in ap.iter().zip(bp) {
                    if !go(at, bt, &inner) {
                        return false;
                    }
                    if let (Some(an), Some(bn)) = (an, bn) {
                        inner.push((an.clone(), bn.clone()));
                    }
                }
                go(ar, br, &inner)
            }
            (
                TermKind::Lam {
                    params: ap,
                    body: ab,
                    types: at,
                },
                TermKind::Lam {
                    params: bp,
                    body: bb,
                    types: bt,
                },
            ) => {
                if ap.len() != bp.len() || at.len() != bt.len() {
                    return false;
                }
                let mut inner = bound.to_vec();
                for (i, (a, b)) in ap.iter().zip(bp).enumerate() {
                    match (
                        at.get(i).and_then(Option::as_ref),
                        bt.get(i).and_then(Option::as_ref),
                    ) {
                        (Some(a), Some(b)) if !go(a, b, &inner) => return false,
                        (Some(_), None) | (None, Some(_)) => return false,
                        _ => {}
                    }
                    inner.push((a.clone(), b.clone()));
                }
                go(ab, bb, &inner)
            }
            _ => crate::surface::same_term_structure(a, b),
        }
    }
    go(a, b, &[])
}

#[derive(Default)]
struct Scopes {
    contexts: Vec<Vec<(Name, SurfaceTerm)>>,
    displayed: Vec<Vec<(String, String)>>,
    notation: notation::Notation,
}
impl Scopes {
    fn key(d: &Derivation) -> Vec<(Name, SurfaceTerm)> {
        d.context.clone()
    }
    fn same(a: &[(Name, SurfaceTerm)], b: &[(Name, SurfaceTerm)]) -> bool {
        a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|((an, at), (bn, bt))| an == bn && same_term(at, bt))
    }
    fn collect(&mut self, d: &Derivation) {
        let k = Self::key(d);
        if !self.contexts.iter().any(|c| Self::same(c, &k)) {
            self.contexts.push(k);
            self.displayed.push(
                d.context
                    .iter()
                    .enumerate()
                    .map(|(i, (n, t))| {
                        (n.to_string(), self.notation.show(t, &d.context[..i], false))
                    })
                    .collect(),
            );
        }
        for p in &d.premises {
            self.collect(p);
        }
    }
    fn id(&self, d: &Derivation) -> usize {
        self.contexts
            .iter()
            .position(|c| Self::same(c, &Self::key(d)))
            .expect("recorded context")
    }
    fn text(&self, out: &mut String) {
        for (i, ctx) in self.displayed.iter().enumerate() {
            writeln!(out, "Γ{i} = {}", bindings(ctx)).unwrap();
        }
        out.push('\n');
    }
    fn html(&self, out: &mut String) {
        out.push_str("<details open class=contexts><summary>");
        out.push_str(&esc(&msg!("proof-contexts").to_string()));
        out.push_str("</summary>");
        for (i, ctx) in self.displayed.iter().enumerate() {
            write!(out, "<p><b>Γ{i}</b> = {}</p>", esc(&bindings(ctx))).unwrap();
        }
        out.push_str("</details>");
    }
}
fn bindings(ctx: &[(String, String)]) -> String {
    if ctx.is_empty() {
        return "∅".into();
    }
    ctx.iter()
        .map(|(n, t)| format!("{n}: {t}"))
        .collect::<Vec<_>>()
        .join(", ")
}
fn judgment(d: &Derivation, s: &Scopes) -> String {
    format!(
        "Γ{} ⊢ {} : {}",
        s.id(d),
        s.notation.show(&d.term, &d.context, false),
        s.notation.show(&d.ty, &d.context, false)
    )
}
fn rule_id(r: Rule) -> &'static str {
    match r {
        Rule::Assumption => "assumption",
        Rule::Constant => "constant",
        Rule::UnverifiedReference => "unverified",
        Rule::Literal => "literal",
        Rule::Sort => "sort",
        Rule::Formation => "formation",
        Rule::Introduction => "introduction",
        Rule::Application => "application",
        Rule::Conversion => "conversion",
        Rule::Reduction => "reduction",
        Rule::Hole => "hole",
    }
}
fn rule_name(d: &Derivation) -> String {
    let id = format!("proof-rule-{}", rule_id(d.rule));
    let mut name = tauto_message::Message::new(id).to_string();
    if !d.introduced.is_empty() {
        write!(
            name,
            " [{}]",
            bindings(
                &d.introduced
                    .iter()
                    .map(|(n, t)| (n.to_string(), show(t)))
                    .collect::<Vec<_>>()
            )
        )
        .unwrap();
    }
    name
}

struct Diagram {
    lines: Vec<String>,
    width: usize,
}
fn width(s: &str) -> usize {
    s.chars()
        .map(|c| {
            if c >= '\u{2e80}' && c != '\u{fe0f}' {
                2
            } else {
                1
            }
        })
        .sum()
}
fn pad(s: &str, n: usize) -> String {
    format!("{s}{}", " ".repeat(n.saturating_sub(width(s))))
}
fn center(s: &str, n: usize) -> String {
    let left = n.saturating_sub(width(s)) / 2;
    format!("{}{}", " ".repeat(left), pad(s, n - left))
}
fn inference_tree(d: &Derivation, s: &Scopes) -> Diagram {
    let children: Vec<_> = d.premises.iter().map(|p| inference_tree(p, s)).collect();
    let conclusion = judgment(d, s).replace('\n', " ");
    let label = if d.is_complete() {
        rule_name(d)
    } else {
        msg!("proof-open-rule", rule = rule_name(d)).to_string()
    };
    let total =
        children.iter().map(|c| c.width).sum::<usize>() + children.len().saturating_sub(1) * 4;
    let w = total.max(width(&conclusion)).max(label.len() + 4);
    let mut lines = Vec::new();
    let h = children.iter().map(|c| c.lines.len()).max().unwrap_or(0);
    for row in 0..h {
        let parts: Vec<_> = children
            .iter()
            .map(|c| {
                let offset = h - c.lines.len();
                if row < offset {
                    " ".repeat(c.width)
                } else {
                    pad(&c.lines[row - offset], c.width)
                }
            })
            .collect();
        lines.push(center(&parts.join("    "), w));
    }
    lines.push(format!("{} [{}]", "─".repeat(w), label));
    lines.push(center(&conclusion, w));
    // The rule label extends the inference line; reserve its complete width for a parent.
    let width = lines.iter().map(|l| width(l)).max().unwrap_or(w);
    Diagram { lines, width }
}

fn html_tree(d: &Derivation, s: &Scopes, out: &mut String) {
    write!(
        out,
        "<div class=proof-tree data-rule={} data-established={}><div class=premises>",
        rule_id(d.rule),
        d.is_complete()
    )
    .unwrap();
    for p in &d.premises {
        html_tree(p, s, out);
    }
    let label = if d.is_complete() {
        rule_name(d)
    } else {
        msg!("proof-open-rule", rule = rule_name(d)).to_string()
    };
    write!(out,"</div><div class=tree-line><span class=tree-rule>{}</span><div class=tree-judgment>{}</div></div></div>",esc(&label),esc(&judgment(d,s))).unwrap();
}

fn color(d: &Derivation) -> String {
    let hash = show(&d.ty)
        .bytes()
        .fold(0u32, |h, b| h.wrapping_mul(31).wrapping_add(u32::from(b)));
    format!("hsl({} 65% 65%)", hash % 360)
}
fn blocks(d: &Derivation, s: &Scopes, out: &mut String) {
    write!(out,"<details open data-established={} class=\"block {}\" style=\"--type:{}\"><summary><b>{}</b><span class=claim>{}</span></summary>",d.is_complete(),rule_id(d.rule),color(d),esc(&rule_name(d)),esc(&judgment(d,s))).unwrap();
    if !d.introduced.is_empty() {
        write!(
            out,
            "<p class=discharge>{}</p>",
            esc(&msg!(
                "proof-discharge",
                names = d
                    .introduced
                    .iter()
                    .map(|(n, _)| n.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
            .to_string())
        )
        .unwrap();
    }
    for (i, p) in d.premises.iter().enumerate() {
        write!(
            out,
            "<div class=slot style=\"--type:{}\"><div class=slot-label>{} {}: {}</div>",
            color(p),
            esc(&msg!("proof-premise").to_string()),
            i + 1,
            esc(&judgment(p, s))
        )
        .unwrap();
        blocks(p, s, out);
        out.push_str("</div>");
    }
    out.push_str("</details>");
}

struct Placed<'a> {
    d: &'a Derivation,
    depth: usize,
    parent: Option<(usize, usize)>,
    y: usize,
    height: usize,
}
fn place<'a>(
    d: &'a Derivation,
    depth: usize,
    parent: Option<(usize, usize)>,
    nodes: &mut Vec<Placed<'a>>,
    next_y: &mut usize,
) {
    let i = nodes.len();
    let height = 150 + d.premises.len() * 42;
    nodes.push(Placed {
        d,
        depth,
        parent,
        y: *next_y,
        height,
    });
    *next_y += height + 32;
    for (slot, p) in d.premises.iter().enumerate() {
        place(p, depth + 1, Some((i, slot)), nodes, next_y);
    }
}
fn graph(d: &Derivation, s: &Scopes, group: usize, out: &mut String) {
    let mut nodes = Vec::new();
    let mut y = 20;
    place(d, 0, None, &mut nodes, &mut y);
    let max_depth = nodes.iter().map(|n| n.depth).max().unwrap_or(0);
    let w = (max_depth + 1) * 480 + 40;
    write!(out,"<div class=graph-scroll><div class=graph style=\"width:{w}px;height:{y}px\"><svg aria-hidden=true width={w} height={y}>").unwrap();
    for (i, n) in nodes.iter().enumerate() {
        if let Some((p, slot)) = n.parent {
            let x = (max_depth - n.depth) * 480 + 420;
            let y = n.y + 61;
            let px = (max_depth - nodes[p].depth) * 480 + 20;
            let py = nodes[p].y + 141 + slot * 42;
            write!(out,"<path data-from=\"g{group}n{i}\" data-to=\"g{group}n{p}\" data-slot={slot} style=\"stroke:{}\" d=\"M {x} {y} C {} {y}, {} {py}, {px} {py}\"/>",color(n.d),x+30,px-30).unwrap();
        }
    }
    out.push_str("</svg>");
    for (i, n) in nodes.iter().enumerate() {
        write!(out,"<article id=\"g{group}n{i}\" data-established={} class=\"node {}\" style=\"--type:{};left:{}px;top:{}px;height:{}px\"><header>#{i} {}</header><div class=output><span>{}</span><i class=port-out></i></div><code class=term>{}</code>",n.d.is_complete(),rule_id(n.d.rule),color(n.d),(max_depth-n.depth)*480+20,n.y,n.height,esc(&rule_name(n.d)),esc(&format!("Γ{} ⊢ {}",s.id(n.d),s.notation.show(&n.d.ty, &n.d.context, false))),esc(&s.notation.show(&n.d.term, &n.d.context, false))).unwrap();
        for (slot, p) in n.d.premises.iter().enumerate() {
            let child = nodes
                .iter()
                .position(|n| n.parent == Some((i, slot)))
                .unwrap();
            write!(out,"<a class=input href=\"#g{group}n{child}\" style=\"--type:{}\"><i class=port-in></i><span>{}: Γ{} ⊢ {}</span></a>",color(p),slot+1,s.id(p),esc(&s.notation.show(&p.ty, &p.context, false))).unwrap();
        }
        out.push_str("</article>");
    }
    out.push_str("</div></div>");
}
fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#39;")
}
const HTML_HEAD: &str = r##"<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; base-uri 'none'; form-action 'none'"><style>
:root{color-scheme:dark;font:15px/1.6 system-ui,sans-serif;background:#10151e;color:#e7edf6}body{margin:0;padding:24px}main{max-width:1200px;margin:auto}section{margin-bottom:48px}h1{font-size:1.5rem}h2{font:1.1rem ui-monospace,monospace;overflow-wrap:anywhere}.status,.contexts,.note{overflow-wrap:anywhere}.note{color:#9eafc5;font-size:.85rem}.contexts{background:#192333;padding:8px 16px;border-radius:8px;margin:12px 0}.contexts p{font:13px ui-monospace,monospace}.block{border:2px solid var(--type);border-left-width:8px;border-radius:5px 14px 14px 5px;background:#1b2a40;padding:8px 12px;margin:6px 0;overflow-wrap:anywhere}.block summary{cursor:pointer}.claim{display:block;font:14px/1.6 ui-monospace,monospace;color:var(--type);margin-top:4px}.slot{border:2px solid var(--type);background:#0e1725;border-radius:10px;margin:12px 0 0 16px;padding:8px}.slot-label{font:12px/1.5 ui-monospace,monospace;color:var(--type)}.discharge{font-size:.85rem;color:#dcb7ff}.hole,[data-established=false]{border-style:dashed}.unavailable{color:#ffd082}.graph-scroll{overflow:auto;direction:rtl;border:1px solid #34445c;border-radius:12px}.graph{direction:ltr;position:relative;background:radial-gradient(#34445c 1px,transparent 1px);background-size:20px 20px}.graph svg{position:absolute;inset:0}.graph path{fill:none;stroke-width:2.5}.node{position:absolute;box-sizing:border-box;width:400px;border:2px solid var(--type);border-radius:10px;background:#19263a}.node header{box-sizing:border-box;padding:7px 16px;background:#24354d;font-size:12px;height:36px;overflow:auto}.output{box-sizing:border-box;position:relative;padding:8px 16px;color:var(--type);font:13px/1.4 ui-monospace,monospace;height:48px;overflow-wrap:anywhere}.output span{display:block;max-height:34px;overflow:auto}.term{box-sizing:border-box;display:block;height:36px;overflow:auto;padding:3px 16px;font-size:12px}.input{box-sizing:border-box;height:42px;position:relative;display:block;border-top:1px solid #34445c;color:var(--type);text-decoration:none;padding:7px 16px;font:12px/1.5 ui-monospace,monospace}.input span{display:block;max-height:28px;overflow:auto}.port-in,.port-out{position:absolute;width:10px;height:10px;border:2px solid var(--type);border-radius:50%;background:#10151e;top:12px}.port-in{left:-8px}.port-out{top:16px;right:-8px;background:var(--type)}a:focus-visible,summary:focus-visible{outline:3px solid #fff;outline-offset:3px}@media print{body{background:white;color:black}.graph-scroll{overflow:visible}}
.tree-scroll{overflow:auto;padding:24px 8px;border:1px solid #34445c;border-radius:12px}.proof-tree{display:inline-flex;flex-direction:column;align-items:stretch;vertical-align:bottom;min-width:max-content;padding:0 12px}.premises{display:flex;align-items:flex-end;justify-content:center;gap:24px;padding:0 10px 24px}.premises:empty{padding-bottom:0}.tree-line{border-top:2px solid #a5b4ca;position:relative;text-align:center;padding:10px 8px 0}.tree-rule{position:absolute;right:0;top:-12px;background:#10151e;padding:0 6px;color:#b7cee9;font:12px/20px system-ui,sans-serif}.tree-judgment{font:14px/1.7 ui-monospace,monospace;white-space:nowrap}.proof-tree[data-established=false]>.tree-line{border-top-style:dashed;color:#ffd082}
</style>"##;
