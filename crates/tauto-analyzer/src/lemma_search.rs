//! Read-only, explicitly scoped suggestions. Shape matching discovers candidates;
//! checking their written terms is a separate operation, never a proof rule.

use std::{collections::BTreeSet, path::Path};

use tauto::{
    check::Verdict,
    report::{Hole, Json, Report, try_fill},
};

use crate::assist::{Suggestion, suggest};

/// Restrict candidate names before applying the result limit. An empty selection
/// searches the local hypotheses and the entry file's loaded import closure.
/// These names restrict discovery, not the dependencies of the resulting proof.
pub fn select(
    report: &Report,
    hole: &Hole,
    using: &[String],
    limit: usize,
) -> Result<Vec<Suggestion>, String> {
    let names: BTreeSet<&str> = using.iter().map(String::as_str).collect();
    for name in &names {
        if !hole.goal.context.iter().any(|(n, _)| n.as_str() == *name)
            && !report.library.iter().any(|entry| entry.name == *name)
        {
            return Err(
                tauto_message::msg!("analyzer-candidate-not-in-scope", name = *name).to_string(),
            );
        }
    }
    let mut candidates = suggest(report, hole, usize::MAX);
    candidates.retain(|s| names.is_empty() || names.contains(s.name.as_str()));
    candidates.truncate(limit);
    Ok(candidates)
}

/// The verdict on the containing declaration, not just a shape match or an
/// accepted partial edit. A checked result still reports any axiom dependencies.
pub struct Validation {
    pub status: &'static str,
    pub axioms: Option<Vec<String>>,
    pub remaining_holes: Vec<String>,
    pub file_status: Option<&'static str>,
    pub diagnostic: Option<String>,
}

impl Validation {
    pub fn unchecked() -> Self {
        Self {
            status: "unchecked",
            axioms: None,
            remaining_holes: Vec::new(),
            file_status: None,
            diagnostic: None,
        }
    }

    pub fn json(&self) -> Json {
        let mut fields = vec![
            ("status", Json::Str(self.status.into())),
            (
                "remaining_holes",
                Json::Arr(
                    self.remaining_holes
                        .iter()
                        .cloned()
                        .map(Json::Str)
                        .collect(),
                ),
            ),
        ];
        if let Some(axioms) = &self.axioms {
            fields.push((
                "axioms",
                Json::Arr(axioms.iter().cloned().map(Json::Str).collect()),
            ));
        }
        if let Some(status) = self.file_status {
            fields.push(("file_status", Json::Str(status.into())));
        }
        if let Some(diagnostic) = &self.diagnostic {
            fields.push(("diagnostic", Json::Str(diagnostic.clone())));
        }
        Json::Obj(fields)
    }
}

/// Check the explicit candidate with the ordinary checker, without changing the
/// source. Incomplete declarations are never labelled checked, even if the
/// proposed edit is accepted by `try_fill`.
pub fn verify(path: &Path, hole: &str, expression: &str) -> Validation {
    let mut result = Validation::unchecked();
    let attempt = match try_fill(path, hole, expression) {
        Ok(attempt) => attempt,
        Err(error) => {
            result.status = "rejected";
            result.diagnostic = Some(error);
            return result;
        }
    };
    result.file_status = Some(attempt.report.status().name());
    result.remaining_holes = attempt
        .report
        .holes()
        .iter()
        .filter(|h| h.file == attempt.hole.file && h.declaration == attempt.hole.declaration)
        .map(|h| h.goal.name.clone())
        .collect();
    result.remaining_holes.sort();
    result.remaining_holes.dedup();
    let entry = attempt.report.entries.iter().find(|entry| {
        entry.file == attempt.hole.file && entry.entry.name == attempt.hole.declaration
    });
    if !attempt.accepted {
        result.status = "rejected";
        result.diagnostic = Some(attempt.report.text());
        return result;
    }
    match entry.map(|entry| &entry.entry.verdict) {
        Some(Verdict::Checked { axioms }) => {
            result.status = "checked";
            let mut axioms = axioms.clone();
            axioms.sort();
            axioms.dedup();
            result.axioms = Some(axioms);
        }
        Some(Verdict::Incomplete { .. }) => result.status = "incomplete",
        _ => {
            result.status = "rejected";
            result.diagnostic = Some(attempt.report.text());
        }
    }
    result
}

/// Keep the written term and discovery name beside, not hidden behind, its verdict.
pub fn candidate_json(suggestion: &Suggestion, validation: &Validation) -> Json {
    let Json::Obj(mut fields) = suggestion.json() else {
        unreachable!("a suggestion is an object")
    };
    fields.push(("validation", validation.json()));
    Json::Obj(fields)
}
