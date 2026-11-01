//! The workspace answers for files that are only in memory, as in a browser.

use tauto_analyzer_wasm::{attempt, goals_json, set_text_str, suggest_json};

const PATH: &str = "/tauto-analyzer-wasm-test/Swap.taut";

#[test]
fn a_proof_is_made_in_memory_a_step_at_a_time() {
    set_text_str(
        PATH,
        "theorem swap<P: Prop, Q: Prop>(h: And(P, Q)): And(Q, P) {\n  ?top\n}\n",
    );
    let goals = goals_json(PATH).unwrap().render();
    assert!(goals.contains("\"goal\":\"And(Q, P)\""), "{goals}");
    let suggested = suggest_json(PATH, "top", 20).unwrap().render();
    assert!(suggested.contains("AndIntro"), "{suggested}");
    let a = attempt(PATH, "top", "AndIntro(?l, ?r)", true)
        .unwrap()
        .render();
    assert!(a.contains("\"accepted\":true"), "{a}");
    attempt(PATH, "l", "and_right(h)", true).unwrap();
    let done = attempt(PATH, "r", "and_left(h)", true).unwrap().render();
    assert!(done.contains("\"status\":\"ok\""), "{done}");
    let wrong = attempt(PATH, "nothing", "h", false);
    assert!(wrong.is_err());
}
