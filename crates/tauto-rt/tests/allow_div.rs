//! `--allow-div`: `Div` outside any `budget` runs past the host's step limit.

use tauto_rt::permissions::{self, Permissions};
use tauto_rt::{DEFAULT_STEP_LIMIT, Loc, host_tick};

const AT: Loc = Loc {
    file: "src/main.taut",
    line: 1,
    col: 1,
};

#[test]
fn allow_div_lifts_the_host_limit() {
    let args = vec!["--allow-div".to_string()];
    let (granted, rest) = Permissions::from_args(&args).unwrap();
    assert!(rest.is_empty());
    permissions::set(granted);
    for _ in 0..=DEFAULT_STEP_LIMIT {
        host_tick(AT);
    }
}
