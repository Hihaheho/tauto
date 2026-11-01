use tauto_nir::{CompilePhase, compile_javascript_with_observer, compile_with_observer};

#[test]
fn observers_see_only_reached_phase_boundaries() {
    use CompilePhase::*;
    for javascript in [false, true] {
        for (source, expected, success) in [
            (
                r#"fn bad(
"#,
                vec![ParseExpand],
                false,
            ),
            (
                r#"let x: Bool := 42
"#,
                vec![ParseExpand, Check],
                false,
            ),
            (
                r#"perform show("x", 42)
"#,
                vec![ParseExpand, Check, Lower],
                true,
            ),
        ] {
            let mut phases = Vec::new();
            let observer = |phase| phases.push(phase);
            let result = if javascript {
                compile_javascript_with_observer(source, observer)
            } else {
                compile_with_observer(source, false, observer)
            };
            assert_eq!(result.is_ok(), success, "{result:?}");
            assert_eq!(phases, expected);
        }
    }
}
