use tauto_nir::{Callee, CompilePhase, ExprKind, Tick, compile_loaded_with_observer};

#[test]
fn extracted_text_markers_do_not_certify_totality() {
    let extracted = r#"// tauto:extracted
pub fn proved(n: i64): i64 ! {Div} { if n == 0 { 0 } else { proved(n - 1) } }
// tauto:extracted-end
"#.to_string();
    assert!(extracted.starts_with(tauto::extract::EXTRACTED_BEGIN));
    assert!(extracted.ends_with(tauto::extract::EXTRACTED_END));
    let loaded = tauto::program::load_texts(vec![
        ("extracted.taut".into(), extracted),
        (
            "runtime.taut".into(),
            r#"pub fn looping(n: i64): i64 ! {Div} { looping(n) }
perform show("a", proved(1))
perform show("b", looping(1))
"#
            .into(),
        ),
    ])
    .unwrap();
    for javascript in [false, true] {
        let mut phases = Vec::new();
        let package =
            compile_loaded_with_observer(&loaded, false, javascript, |phase| phases.push(phase))
                .unwrap();
        assert_eq!(phases, [CompilePhase::Check, CompilePhase::Lower]);
        let mut proved = 0;
        let mut looping = 0;
        for function in &package.fns {
            function.body.walk(&mut |expr| {
                if let ExprKind::Call(call) = &expr.kind
                    && let Callee::Inst(inst) = call.callee
                {
                    match package.fns[inst].source.as_str() {
                        "proved" => {
                            assert_eq!(call.tick, Tick::Host);
                            proved += 1;
                        }
                        "looping" => {
                            assert_eq!(call.tick, Tick::Host);
                            looping += 1;
                        }
                        _ => {}
                    }
                }
            });
        }
        assert!(proved > 0 && looping > 0);
    }
}
