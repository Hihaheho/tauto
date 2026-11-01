//! The language of the command's messages: `--lang`, `$TAUTO_LANG`, the
//! user config and the locale, in that order.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

struct Home(PathBuf);

impl Home {
    fn new(name: &str) -> Home {
        let d = std::env::temp_dir().join(format!("tauto-lang-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(d.join("tauto")).unwrap();
        Home(d)
    }
}

impl Drop for Home {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn tauto(config: &Path, env: &[(&str, &str)], args: &[&str]) -> Output {
    let mut c = Command::new(env!("CARGO_BIN_EXE_tauto"));
    c.current_dir(config)
        .env("XDG_CONFIG_HOME", config)
        .env_remove("TAUTO_LANG")
        .env_remove("LC_ALL")
        .env_remove("LC_MESSAGES")
        .env_remove("LANG");
    c.envs(env.iter().copied()).args(args).output().unwrap()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

const EN: &str = "no command nope:";
const JA: &str = "コマンド nope はありません";

#[test]
fn english_without_a_setting() {
    let h = Home::new("none");
    assert!(stderr(&tauto(&h.0, &[], &["nope"])).starts_with(EN));
    assert!(stderr(&tauto(&h.0, &[("LANG", "C")], &["nope"])).starts_with(EN));
}

#[test]
fn the_locale_chooses_the_language() {
    let h = Home::new("locale");
    let out = tauto(&h.0, &[("LANG", "ja_JP.UTF-8")], &["nope"]);
    assert!(stderr(&out).starts_with(JA), "{}", stderr(&out));
    // A language without messages is English.
    assert!(stderr(&tauto(&h.0, &[("LANG", "fr_FR.UTF-8")], &["nope"])).starts_with(EN));
}

#[test]
fn the_config_comes_before_the_locale() {
    let h = Home::new("config");
    std::fs::write(h.0.join("tauto/config.eure"), "lang = \"ja\"\n").unwrap();
    let out = tauto(&h.0, &[("LANG", "en_US.UTF-8")], &["nope"]);
    assert!(stderr(&out).starts_with(JA), "{}", stderr(&out));
}

#[test]
fn the_variable_and_the_option_come_first() {
    let h = Home::new("option");
    std::fs::write(h.0.join("tauto/config.eure"), "lang = \"ja\"\n").unwrap();
    assert!(stderr(&tauto(&h.0, &[("TAUTO_LANG", "en")], &["nope"])).starts_with(EN));
    let out = tauto(&h.0, &[("TAUTO_LANG", "en")], &["--lang", "ja", "nope"]);
    assert!(stderr(&out).starts_with(JA), "{}", stderr(&out));
}

#[test]
fn an_unknown_language_is_refused() {
    let h = Home::new("unknown");
    let out = tauto(&h.0, &[], &["--lang", "xx", "nope"]);
    assert!(!out.status.success());
    assert!(stderr(&out).starts_with("unknown language xx (known: en, ja)"));
}
