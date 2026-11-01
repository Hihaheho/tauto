//! List declared route capabilities without executing or claiming a test pass.
fn main() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cases");
    let filter = std::env::args().nth(1).unwrap_or_default();
    let cases =
        tauto_test_suite::capabilities(&root).unwrap_or_else(|e| panic!("case capabilities: {e}"));
    let mut selected = 0;
    println!("case\tassertions\troute\tcapability (not execution status)");
    for case in cases.into_iter().filter(|c| c.name.contains(&filter)) {
        selected += 1;
        for (route, capability) in case.routes {
            println!(
                "{}\t{}\t{route}\t{capability}",
                case.name,
                case.assertions.join(",")
            );
        }
    }
    assert!(selected > 0, "filter selected no case capabilities");
}
