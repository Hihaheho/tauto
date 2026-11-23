//! Runs repository cases with statement values produced by the Tauto macro tote.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use selfhost_harness::{differential, materialize, root, run_tote_native};
use tauto::surface::{Name, Program};
use tauto_macro::macros::runner::{CallError, CallStats, Host, MacroRunner};
use tauto_nibcheck::types::TypeReport;
use tauto_surface::macros::Node;
use tauto_test_suite::{Filter, Outcome};

fn decode_text(hex: &str) -> String {
    if hex == "-" {
        return String::new();
    }
    assert_eq!(hex.len() % 2, 0);
    let bytes = (0..hex.len())
        .step_by(2)
        .map(|start| u8::from_str_radix(&hex[start..start + 2], 16).unwrap())
        .collect();
    String::from_utf8(bytes).unwrap()
}

fn decode_node<'a>(lines: &mut impl Iterator<Item = &'a str>) -> Node {
    let line = lines.next().expect("truncated statement value");
    let words: Vec<_> = line.split_ascii_whitespace().collect();
    match words.as_slice() {
        ["ctor", name, count] => {
            let fields = (0..count.parse().unwrap())
                .map(|_| {
                    let label = lines.next().expect("missing constructor field");
                    let label = (label != "-").then(|| decode_text(label));
                    (label, decode_node(lines))
                })
                .collect();
            Node::Ctor(decode_text(name).into(), fields)
        }
        ["text", text] => Node::Text(decode_text(text)),
        ["int", number] => Node::Int(number.parse().unwrap()),
        ["true"] => Node::Bool(true),
        ["false"] => Node::Bool(false),
        ["list", count] => Node::List(
            (0..count.parse().unwrap())
                .map(|_| decode_node(lines))
                .collect(),
        ),
        ["product", count] => Node::product(
            (0..count.parse().unwrap())
                .map(|_| decode_node(lines))
                .collect(),
        ),
        ["none"] => Node::none(),
        ["some"] => Node::some(decode_node(lines)),
        _ => panic!("invalid statement value: {line:?}"),
    }
}

#[derive(Debug, Default)]
struct StatementRunner {
    value: Mutex<Option<Node>>,
    calls: AtomicUsize,
}

impl MacroRunner for StatementRunner {
    fn call(
        &self,
        program: &Program,
        report: &TypeReport,
        name: &Name,
        args: &[Node],
        host: &mut Host,
    ) -> Result<(Node, CallStats), CallError> {
        if name.as_str().rsplit("::").next() == Some("make") {
            self.calls.fetch_add(1, Ordering::Relaxed);
            let value = self
                .value
                .lock()
                .unwrap()
                .clone()
                .expect("missing self-hosted result");
            Ok((
                value,
                CallStats {
                    steps: 0,
                    allocations: 0,
                },
            ))
        } else {
            tauto_macro_vm::VmRunner.call(program, report, name, args, host)
        }
    }
}

#[test]
fn sealed_effects_from_selfhosted_statement_values() {
    let mut cases = BTreeMap::<String, Vec<(String, String)>>::new();
    for (path, source) in differential("macro-sealed-expansion") {
        let (case, file) = path.rsplit_once('/').unwrap();
        cases
            .entry(case.to_owned())
            .or_default()
            .push((file.to_owned(), source));
    }
    assert_eq!(cases.len(), 4);
    let runner = Arc::new(StatementRunner::default());
    tauto::macros::expand::set_runner(runner.clone());
    let cases_root = root().join("cases");
    for (case, mut files) in cases {
        files.sort_by_key(|(file, _)| match file.as_str() {
            "macro.nib" => 0,
            "lib.nib" => 1,
            "main.nib" => 2,
            _ => panic!("{case}: unexpected source {file}"),
        });
        let scratch = materialize("sealed-statement-values", &files);
        let mut args = vec!["--statement-values".to_owned()];
        args.extend(scratch.paths.iter().cloned());
        let out = run_tote_native("macros", &args, 200_000_000_000);
        assert_eq!(out.error, None, "{case}: {}", out.stderr);
        assert_eq!(out.exit, Some(0), "{case}: {}", out.stderr);
        let mut lines = out.stdout.lines();
        let value = decode_node(&mut lines);
        assert_eq!(lines.next(), None, "{case}");
        *runner.value.lock().unwrap() = Some(value);
        let prior_calls = runner.calls.load(Ordering::Relaxed);
        let (file, name) = case.split_once('#').unwrap();
        let report = tauto_test_suite::run_path(
            &root().join(file),
            &cases_root,
            Some(Filter::Contains(name)),
        )
        .unwrap();
        assert!(report.error.is_none(), "{case}: {:?}", report.error);
        assert_eq!(report.results.len(), 1, "{case}");
        match &report.results[0].1 {
            Outcome::Passed => {}
            Outcome::Failed(error) => panic!("{case}: {error}"),
            _ => panic!("{case}: case did not run to completion"),
        }
        assert!(
            runner.calls.load(Ordering::Relaxed) > prior_calls,
            "{case}: macro result unused"
        );
    }
}
