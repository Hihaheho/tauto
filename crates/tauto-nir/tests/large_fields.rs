use tauto_nir::{Indirect, compile_with};

/// The indirection of each field of `data`'s constructor `ctor`.
fn indirect(source: &str, data: &str, ctor: &str) -> Vec<Indirect> {
    let package = compile_with(source, true).unwrap();
    let d = package
        .datas
        .iter()
        .find(|d| d.name.as_str() == data)
        .unwrap();
    let c = d
        .ctors
        .iter()
        .find(|c| c.name.rsplit("::").next() == Some(ctor))
        .unwrap();
    c.fields.iter().map(|f| f.indirect).collect()
}

const SOURCE: &str = r#"
struct Big { a: Text, b: Text, c: Text, d: Text }
struct Small { a: Text, b: Text }
enum Step { Next(Big, Small), Done }
fn step(s: Step): Step ! {} { s }
"#;

#[test]
fn a_large_field_of_a_shared_data_goes_behind_an_rc() {
    assert_eq!(
        indirect(SOURCE, "Step", "Next"),
        vec![Indirect::Shared, Indirect::None]
    );
}

#[test]
fn the_fields_of_a_large_struct_stay_inline() {
    assert_eq!(indirect(SOURCE, "Big", "Mk"), vec![Indirect::None; 4]);
}
