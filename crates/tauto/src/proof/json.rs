//! Machine-readable complete kernel derivations, independent of presentation rules.
use super::{View, rule_id, show};
use crate::check::{Derivation, FileEntry, Verdict};
use crate::report::{Json, term_json};
use crate::surface::Name;
use crate::surface::{SurfaceTerm, TheoremDecl};
use std::path::Path;
use tauto_message::Message;

fn string(s: impl Into<String>) -> Json {
    Json::Str(s.into())
}
fn strings(xs: &[Name]) -> Json {
    Json::Arr(xs.iter().map(|s| string(s.to_string())).collect())
}
fn context(xs: &[(Name, SurfaceTerm)]) -> Json {
    Json::Arr(
        xs.iter()
            .map(|(n, t)| {
                Json::Obj(vec![
                    ("name", string(n.to_string())),
                    ("type", string(show(t))),
                    ("type_tree", term_json(t)),
                ])
            })
            .collect(),
    )
}
fn node(d: &Derivation, next: &mut usize) -> Json {
    let id = *next;
    *next += 1;
    Json::Obj(vec![
        ("id", Json::Num(id)),
        ("rule", string(rule_id(d.rule))),
        ("complete", Json::Bool(d.is_complete())),
        ("context", context(&d.context)),
        ("term", string(show(&d.term))),
        ("term_tree", term_json(&d.term)),
        ("type", string(show(&d.ty))),
        ("type_tree", term_json(&d.ty)),
        ("introduced", context(&d.introduced)),
        (
            "premises",
            Json::Arr(d.premises.iter().map(|p| node(p, next)).collect()),
        ),
    ])
}
fn status(v: &Verdict) -> &'static str {
    match v {
        Verdict::Checked { .. } => "checked",
        Verdict::Incomplete { .. } => "incomplete",
        Verdict::Failed(_) => "failed",
        Verdict::Skipped(_) => "skipped",
    }
}
pub(super) fn render(
    declarations: &[&TheoremDecl],
    entries: &[FileEntry],
    trees: &[(Name, Derivation)],
    own: &Path,
    load_failed: bool,
) -> Result<View, Message> {
    let mut proofs = Vec::new();
    for d in declarations {
        let matching: Vec<_> = entries
            .iter()
            .filter(|e| e.file == own && e.entry.name == d.name)
            .collect();
        let [entry] = matching.as_slice() else {
            return Err(tauto_message::msg!(
                "proof-ambiguous",
                name = d.name.to_string()
            ));
        };
        let verdict = &entry.entry.verdict;
        let (axioms, uses, holes, error) = match verdict {
            Verdict::Checked { axioms } => (
                strings(axioms),
                Json::Arr(vec![]),
                Json::Arr(vec![]),
                Json::Null,
            ),
            Verdict::Incomplete { holes, uses } => (
                Json::Arr(vec![]),
                strings(uses),
                Json::Arr(
                    holes
                        .iter()
                        .map(|h| {
                            Json::Obj(vec![
                                ("name", string(h.name.clone())),
                                ("goal", string(show(&h.goal))),
                                ("goal_tree", term_json(&h.goal)),
                                ("context", context(&h.context)),
                            ])
                        })
                        .collect(),
                ),
                Json::Null,
            ),
            Verdict::Failed(e) => (
                Json::Arr(vec![]),
                Json::Arr(vec![]),
                Json::Arr(vec![]),
                string(e.to_string()),
            ),
            Verdict::Skipped(e) => (
                Json::Arr(vec![]),
                Json::Arr(vec![]),
                Json::Arr(vec![]),
                string(e.to_string()),
            ),
        };
        let tree = trees
            .iter()
            .rev()
            .find(|(name, _)| name == &d.name)
            .map_or(Json::Null, |(_, d)| node(d, &mut 0));
        proofs.push(Json::Obj(vec![
            ("name", string(d.name.to_string())),
            ("status", string(status(verdict))),
            ("parameters", context(&d.params)),
            ("implicit", Json::Num(d.implicit)),
            ("goal", string(show(&d.ty))),
            ("goal_tree", term_json(&d.ty)),
            ("axioms", axioms),
            ("uses", uses),
            ("holes", holes),
            ("error", error),
            ("derivation", tree),
        ]));
    }
    let failed = load_failed
        || entries
            .iter()
            .any(|e| matches!(e.entry.verdict, Verdict::Failed(_)));
    let incomplete = entries
        .iter()
        .any(|e| matches!(e.entry.verdict, Verdict::Incomplete { .. }));
    let text = Json::Obj(vec![
        ("version", Json::Num(1)),
        (
            "status",
            string(if failed {
                "failed"
            } else if incomplete {
                "incomplete"
            } else {
                "ok"
            }),
        ),
        ("proofs", Json::Arr(proofs)),
    ])
    .render()
        + "\n";
    Ok(View {
        text,
        failed,
        incomplete,
    })
}
