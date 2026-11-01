//! How long a first check, an unchanged check and an edit of the last
//! declaration take, compared with an in-process batch check of the same file:
//! `cargo run --release -p tauto-analyzer --example edit_latency -- std/MapLaws.taut`

use std::path::PathBuf;
use std::time::Instant;

use tauto_analyzer::Workspace;

fn main() {
    let path: PathBuf = std::env::args().nth(1).expect("a .taut file").into();
    let text = std::fs::read_to_string(&path).unwrap();
    let mut ws = Workspace::new();
    let timed = |what: &str, f: &mut dyn FnMut()| {
        let t = Instant::now();
        f();
        println!("{what:<28} {:>9.1?}", t.elapsed());
    };
    timed("tauto check (batch)", &mut || {
        tauto::report::check_report(&path, None).unwrap();
    });
    timed("first check", &mut || {
        ws.report(&path).unwrap();
    });
    timed("unchanged", &mut || {
        ws.report(&path).unwrap();
    });
    let at = text.rfind("\n}").unwrap();
    let mut n = 0;
    for _ in 0..3 {
        n += 1;
        let edited = format!("{}\n  // edit {n}{}", &text[..at], &text[at..]);
        ws.set_text(&path, edited);
        timed("edit the last declaration", &mut || {
            ws.report(&path).unwrap();
        });
    }
    println!("{:?}", ws.stats(&path));
}
