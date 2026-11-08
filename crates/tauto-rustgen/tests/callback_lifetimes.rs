//! Locally handled suspension does not give synchronous borrows a future lifetime.
use std::process::Command;
use std::sync::Mutex;
use tauto_rustgen::{Bindings, Options, Sources, workspace};

static BUILD_LOCK: Mutex<()> = Mutex::new(());

fn execute_mode(source: &str, tag: &str, expected: &str, sync: bool) {
    let _build = BUILD_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let evaluated = tauto::eval::run(source)
        .unwrap()
        .outputs
        .into_iter()
        .map(|(name, value)| format!("{name} = {value}\n"))
        .collect::<String>();
    assert_eq!(evaluated, expected, "evaluator: {tag}");
    let mut package = tauto_nir::compile(source).unwrap();
    package.sync |= sync;
    let ws = workspace(
        "callback-lifetimes",
        &package,
        &Sources {
            file: "main.taut",
            text: source,
        },
        &Bindings::default(),
        &Options::default(),
    );
    build_and_run(ws, tag, expected);
}

fn build_and_run(ws: tauto_rustgen::Workspace, tag: &str, expected: &str) {
    let root = std::env::temp_dir().join(format!("tauto-callback-abi-{}", std::process::id()));
    let generated = root.join(tag);
    let binary = ws
        .build(
            "callback-lifetimes",
            &generated,
            &root.join("target"),
            false,
        )
        .unwrap_or_else(|error| panic!("{tag}: {error}"));
    let output = Command::new(binary).output().unwrap();
    assert!(
        output.status.success(),
        "{tag}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected, "{tag}");
    assert!(output.stderr.is_empty(), "{tag}: unexpected stderr");
    std::fs::remove_dir_all(generated).unwrap();
}

#[test]
fn shared_and_affine_callbacks_compile_with_sync_runtime_aliases() {
    tauto_messages::install();
    execute_mode(
        r#"effect ask(): i64
fn apply<!e>(callback: () -> i64 ! e): i64 ! e { callback() }
let result := handle { apply(() => perform ask()) } with {
  ask(), k => k(42)
  return value => value
}
perform show("value", result)
"#,
        "shared-sync",
        "value = 42\n",
        true,
    );
    execute_mode(
        r#"effect ask(): i64
fn apply_once(callback: affine () -> Text ! {ask}): Text ! {ask} { callback() }
let text := "kept"
let buffer := Buf::of(&text)
let result := handle {
  apply_once(() => {
    let ignored := perform ask()
    Text::of(buffer)
  })
} with {
  ask(), k => k(42)
  return value => value
}
perform show("value", result)
"#,
        "affine-sync",
        "value = \"kept\"\n",
        true,
    );
}

#[test]
fn standalone_callback_spellings_resolve_without_hidden_declarations() {
    tauto_messages::install();
    use tauto_nir::{FnTy, Kind, Package, Tier, Ty};
    let _build = BUILD_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let package = Package::default();
    let bindings = Bindings::default();
    let shared = Ty::Fn(Box::new(FnTy {
        params: Vec::new(),
        ret: Ty::Unit,
        kind: Kind::Shared,
        tier: Tier::O,
    }));
    let nested = Ty::Fn(Box::new(FnTy {
        params: vec![shared.clone()],
        ret: Ty::Option(Box::new(shared.clone())),
        kind: Kind::Affine,
        tier: Tier::O,
    }));
    let plain = tauto_rustgen::type_name(&package, &bindings, &shared);
    let named = tauto_rustgen::type_name_with_lifetime(&package, &bindings, &nested, "'scope");
    let mut ws = workspace(
        "callback-lifetimes",
        &package,
        &Sources { file: "", text: "" },
        &bindings,
        &Options::default(),
    );
    let lib = &mut ws
        .files
        .iter_mut()
        .find(|(name, _)| name == "src/lib.rs")
        .unwrap()
        .1;
    assert!(!lib.contains("__TautoO"));
    assert!(!plain.contains("__TautoO") && !named.contains("__TautoO"));
    lib.push_str(&format!(
        r#"
pub fn standalone<'a>(callback: {plain}) -> {plain} {{ callback }}
pub fn nested<'scope>(callback: {named}) -> {named} {{ callback }}
pub fn public_helper_probe<'a, 'scope>() {{
    let callback: {plain} = Rc::new(|_ev| tauto_rt::o::pin(async move {{}}));
    drop(standalone(callback));
    let wrapper: {named} = Box::new(|_ev, inner| tauto_rt::o::pin(async move {{ Some(inner) }}));
    drop(nested(wrapper));
}}
"#
    ));
    ws.files
        .iter_mut()
        .find(|(name, _)| name == "src/main.rs")
        .unwrap()
        .1 = "fn main() { callback_lifetimes::public_helper_probe(); }\n".into();
    build_and_run(ws, "standalone-types", "");
}
