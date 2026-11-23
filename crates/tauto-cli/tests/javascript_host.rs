use std::{
    fs,
    path::Path,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};
static NEXT: AtomicU64 = AtomicU64::new(0);
fn write(root: &Path, p: &str, s: &str) {
    let p = root.join(p);
    fs::create_dir_all(p.parent().unwrap()).unwrap();
    fs::write(p, s).unwrap();
}
fn dir() -> std::path::PathBuf {
    let p = std::env::temp_dir().join(format!(
        "tauto-js-host-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&p).unwrap();
    p
}
fn cli(root: &Path, target: &str) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_tauto"))
        // The messages below are the English ones, whatever the language here.
        .env("TAUTO_LANG", "en")
        .args(["build", "--backend", "javascript", "--target", target, "-o"])
        .arg(root.join("out"))
        .arg(root)
        .output()
        .unwrap()
}
fn run(root: &Path) -> std::process::Output {
    Command::new("node")
        .arg(root.join("out/main.mjs"))
        .output()
        .unwrap()
}
fn success(out: &std::process::Output) {
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
#[test]
fn manifest_fetch_effect_and_rejection() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "http-demo" }
javascript { extern { get = "host/http.mjs#get" } sources = ["host"] }
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
extern { fn get(url: Text): Text ! {wait} }
effect http_get(url: Text): Text resume 1
let text := handle { perform http_get("data:text/plain,hello") } with { http_get(url), k => k(get(url)) }
show(&text)"#,
    );
    write(
        &d,
        "host/http.mjs",
        "export async function get(url) { const r=await fetch(url);if(!r.ok)throw new Error('HTTP '+r.status);return r.text(); }",
    );
    for target in ["node", "browser"] {
        success(&cli(&d, target));
        let out = run(&d);
        success(&out);
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            "\"hello\"\n"
        );
    }
    write(
        &d,
        "host/http.mjs",
        "export async function get(){throw new Error('host rejected');}",
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("host rejected"));
    fs::remove_dir_all(d).unwrap();
}
#[test]
fn bindings_are_checked_for_target_and_direct_handlers() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "host-demo" }
javascript { node { wait = "host.mjs#wait" } }"#,
    );
    write(&d, "host.mjs", "export async function wait(){return 1n;}");
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
extern { fn wait(): i64 ! {wait} }
show(&wait())"#,
    );
    let out = cli(&d, "browser");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("unavailable"));
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
extern { fn wait(): i64 ! {wait} }
effect ask(): i64 direct
let n := handle { perform ask() } with { ask(), k => k(wait()) }
show(&n)"#,
    );
    let out = cli(&d, "node");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("performs wait, which is not direct"));
    fs::remove_dir_all(d).unwrap();
}
#[test]
fn rust_externs_are_compiled_to_wasm() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "wasm-demo" }
rust { bridge = "bridge" types { Counter = "wasm_demo_bridge::Counter" } }
"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"wasm-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        r#"pub struct Counter(i64);
pub fn make(n:i64)->Counter{Counter(n)}
pub fn bump(n:&mut Counter)->i64{n.0+=1;n.0}
pub fn consume(n:Counter)->i64{n.0}
pub fn twice(n:i64)->i64{n*2}
pub fn hello(s:&str)->String{format!("hello {s}")}
pub fn append(v:&mut Vec<i64>){v.push(42);}
pub fn maybe(n:i64)->Option<i64>{Some(n+1)}
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::prelude::collections

struct(affine) Counter {}
extern {
 fn make(n: i64): Counter
 fn bump(n: &mut Counter): i64
 fn consume(n: Counter): i64
 fn twice(n: i64): i64
 fn hello(s: &Text): Text
 fn append(v: &mut Vec(i64)): Unit
 fn maybe(n: i64): Option(i64)
}
show(&twice(9007199254740993))
show(&hello("世界"))
var values := Vec::new()
append(&mut values)
show(&values)
show(&maybe(9))
var c := make(40)
show(&bump(&mut c))
show(&consume(c))
"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "18014398509481986\n\"hello 世界\"\nVec[42]\nSome(10)\n41\n41\n"
    );
    assert!(d.join("out/externs.wasm").exists());
    fs::remove_dir_all(d).unwrap();
}
#[test]
fn async_host_callback_can_suspend_through_a_nib_handler() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "callback-demo" }
javascript { extern { apply = "host.mjs#apply" } }"#,
    );
    write(
        &d,
        "host.mjs",
        "export async function apply(f){return (await f(2n))+(await f(3n));}",
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
effect ask(n: i64): i64 resume 1
extern { fn apply(f: &((n: i64) -> i64)): i64 ! {wait} }
let r := handle { apply((n) => perform ask(n)) + 1 } with { ask(n), k => k(n * 10) }
show(&r)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "51\n");
    fs::remove_dir_all(d).unwrap();
}
#[test]
fn callback_abort_leaves_the_host_frame() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "callback-demo" }
javascript { extern { apply = "host.mjs#apply" } }"#,
    );
    write(
        &d,
        "host.mjs",
        "export async function apply(f){return (await f(2n))+100n;}",
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
effect ask(n: i64): i64 resume <=1
extern { fn apply(f: &((n: i64) -> i64)): i64 ! {wait} }
let r := handle { apply((n) => perform ask(n)) + 1 } with { ask(n), k => 7 }
show(&r)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "7\n");
    fs::remove_dir_all(d).unwrap();
}
#[test]
fn wasm_resources_are_released_at_scope_exit_and_abort() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "lifetime-demo" }
rust { bridge = "bridge" types { Probe = "lifetime_demo_bridge::Probe" } }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"lifetime-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        r#"use std::sync::atomic::{AtomicI64,Ordering};static DROPS:AtomicI64=AtomicI64::new(0);
pub struct Probe(i64);impl Drop for Probe{fn drop(&mut self){DROPS.fetch_add(self.0,Ordering::SeqCst);}}
pub fn make(n:i64)->Probe{Probe(n)}pub fn dropped()->i64{DROPS.load(Ordering::SeqCst)}"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"struct(affine) Probe {}
extern { fn make(n: i64): Probe
 fn dropped(): i64 }
effect stop(): Never resume 0
fn scope(): Unit { let a := make(10); let b := make(20); #() }
fn leave(): Unit ! {stop} { let a := make(4); let b := make(8); perform stop() }
scope()
show(&dropped())
handle { leave() } with { stop() => #() }
show(&dropped())
let p := Some(make(9))
match p { Some(value) => #(), None => #() }
show(&dropped())
"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "30\n42\n51\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn host_boundaries_reject_reusable_callbacks_and_expired_borrows() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "boundary-demo" }
javascript { extern { apply = "host.mjs#apply" } }"#,
    );
    write(
        &d,
        "host.mjs",
        "export async function apply(f){return await f(0n);}",
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
effect choose(): i64 resume ω
extern { fn apply(f: &((n: i64) -> i64)): i64 ! {wait} }
let n := handle { apply((n) => perform choose()) } with { choose(), k => k(1) + k(2) }
show(&n)"#,
    );
    let out = cli(&d, "node");
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("may resume more than once"),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "boundary-demo" }
javascript { extern { remember = "host.mjs#remember" inspect = "host.mjs#inspect" } }"#,
    );
    write(
        &d,
        "host.mjs",
        "let saved;export function remember(v){saved=v;return null;}export function inspect(){return saved.get();}",
    );
    write(
        &d,
        "src/main.taut",
        r#"extern { fn remember(n: &i64): Unit
fn inspect(): i64 }
let n := 3
remember(&n)
show(&inspect())"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("outlived its call"));
    fs::remove_dir_all(d).unwrap();
}
#[test]
fn wasm_shared_temporaries_survive_multiple_resumptions() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "shared-demo" }
rust { bridge = "bridge" types { Probe = "shared_demo_bridge::Probe" } }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"shared-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        "#[derive(Clone)] pub struct Probe(i64); pub fn make(n:i64)->Probe{Probe(n)}pub fn inspect(p:Probe,n:i64)->i64{p.0+n}",
    );
    write(
        &d,
        "src/main.taut",
        r#"struct(shared) Probe {}
extern { fn make(n: i64): Probe
fn inspect(p: Probe, n: i64): i64 }
effect choose(): i64 resume ω
let result := handle { inspect(make(10), perform choose()) } with { choose(), k => k(1) + k(2) }
show(&result)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "23\n");
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn generic_rust_externs_are_specialized_through_nib_functions() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "generic-demo" }
rust { bridge = "bridge" }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"generic-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        "pub fn identity<T>(x:T)->T{x}\npub fn reverse<T>(mut xs:Vec<T>)->Vec<T>{xs.reverse();xs}",
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::prelude::collections

extern {
 fn identity<A>(x: A): A
 fn reverse<A>(xs: Vec(A)): Vec(A)
}
fn indirect<A>(x: A): A { identity(x) }
show(&indirect(42))
show(&indirect("hello"))
var xs := Vec::new()
Vec::push(&mut xs, 1)
Vec::push(&mut xs, 2)
show(&reverse(xs))"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "42\n\"hello\"\nVec[2, 1]\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_callbacks_reenter_and_return_functions() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "function-demo" }
rust { bridge = "bridge" }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"function-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        r#"pub fn twice(f:&mut dyn FnMut(i64)->i64)->i64{f(2)+f(3)}
pub fn add(n:i64)->impl Fn(i64)->i64{move |x|x+n}
pub fn number(n:i64)->i64{n*10}
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"extern {
 fn twice(f: &((n: i64) -> i64)): i64
 fn add(n: i64): (i64) -> i64
 fn number(n: i64): i64
}
effect adjust(n: i64): i64 direct
let result := handle { twice((n) => number(n) + perform adjust(n)) } with { adjust(n), k => k(n) }
show(&result)
let f := add(40)
show(&f(2))
show(&twice(&f))"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "55\n42\n85\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_borrowed_returns_preserve_mutation_and_owner_lifetime() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "view-demo" }
rust { bridge = "bridge" types { Counter = "view_demo_bridge::Counter" } }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"view-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        r#"pub struct Counter(i64);
pub fn make(n:i64)->Counter{Counter(n)}
pub fn count(c:&Counter)->&i64{&c.0}
pub fn count_mut(c:&mut Counter)->&mut i64{&mut c.0}
pub fn consume(c:Counter)->i64{c.0}
pub fn first(v:&mut Vec<i64>)->Option<&mut i64>{v.first_mut()}
pub fn numbers(v:&mut Vec<i64>)->&mut Vec<i64>{v}
pub fn slice(v:&Vec<i64>)->&[i64]{v.as_slice()}
pub fn bump(n:&mut i64){*n+=1}
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::prelude::collections

struct(affine) Counter {}
extern {
 fn make(n: i64): Counter
 fn count(c: &Counter): &i64
 fn count_mut(c: &mut Counter): &mut i64
 fn consume(c: Counter): i64
 fn first(v: &mut Vec(i64)): Option(&mut i64)
 fn numbers(v: &mut Vec(i64)): &mut Vec(i64)
 fn slice(v: &Vec(i64)): &Slice(i64)
 fn bump(n: &mut i64): Unit
}
var c := make(40)
{ let n := count(&c); show(&n) }
{ let n := count_mut(&mut c); *n := n + 1; bump(&mut n) }
show(&consume(c))
var values := Vec::new()
Vec::push(&mut values, 10)
match first(&mut values) { Some(n) => bump(&mut n), None => #() }
{ let list := numbers(&mut values)
  Vec::push(&mut list, 20)
  handle { Vec::swap(&mut list, 0, 1) } with { out_of_bounds() => #() }
  match Vec::get_mut(&mut list, 0) { Some(n) => bump(&mut n), None => #() }
  show(&Vec::pop(&mut list))
}
{ let s := slice(&values); show(&Slice::len(&s)) }
show(&values)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "40\n42\nSome(11)\n1\nVec[21]\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_callback_waits_for_fetch_and_reenters_after_suspension() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "async-wasm" }
rust { bridge = "bridge" }
javascript { extern { get = "host.mjs#get" } }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"async-wasm-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        r#"pub fn twice(f:&mut dyn FnMut(i64)->i64)->i64{f(2)+f(3)}
pub fn number(n:i64)->i64{n*10}"#,
    );
    write(
        &d,
        "host.mjs",
        "export async function get(){const r=await fetch('data:text/plain,7');return BigInt(await r.text());}",
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
extern {
 fn twice(f: &((n: i64) -> i64)): i64
 fn number(n: i64): i64
 fn get(): i64 ! {wait}
}
effect ask(n: i64): i64 resume 1
let result := handle { twice((n) => perform ask(n)) } with {
 ask(n), k => k(number(n) + get())
}
show(&result)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "64\n");
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_callback_borrows_rust_stack_and_updates_it() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "borrow-callback" }
rust { bridge = "bridge" }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"borrow-callback-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        "pub fn edit(f:&mut dyn FnMut(&mut i64))->i64{let mut n=40;f(&mut n);n}",
    );
    write(
        &d,
        "src/main.taut",
        r#"extern { fn edit(f: &((n: &mut i64) -> Unit)): i64 }
fn change(value: &mut i64): Unit { *value := value + 2 }
let n := edit(&change)
show(&n)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "42\n");
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_opaque_iterator_view_keeps_its_vector_alive() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "iterator-demo" }
rust { bridge = "bridge" types { Cursor = "iterator_demo_bridge::Cursor<'_>" } }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"iterator-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        r#"pub struct Cursor<'a>(std::slice::Iter<'a,i64>);
pub fn cursor(v:&Vec<i64>)->Cursor<'_>{Cursor(v.iter())}
pub fn next<'a>(v:&mut Cursor<'a>)->Option<&'a i64>{v.0.next()}"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::prelude::collections

extern {
 type(borrow) Cursor
 fn cursor(v: &Vec(i64)): Cursor
 fn next(c: &mut Cursor): Option(&i64)
}
var values := Vec::new()
Vec::push(&mut values, 10)
Vec::push(&mut values, 20)
{ var it := cursor(&values)
  match next(&mut it) { Some(n) => show(&n), None => #() }
  match next(&mut it) { Some(n) => show(&n), None => #() }
}
show(&values)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "10\n20\nVec[10, 20]\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn abandoning_rust_callbacks_are_rejected_before_wasm_build() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "native-callback-policy" }
rust { bridge = "bridge" }"#,
    );
    for (declaration, body) in [
        (r#"effect stop(): Never resume 0"#, r#"perform stop(); 1"#),
        (r#"effect maybe(): i64 resume <=1"#, r#"perform maybe()"#),
    ] {
        let effect = if declaration.contains("stop") {
            "stop"
        } else {
            "maybe"
        };
        let arm = if effect == "stop" {
            r#"stop() => 42"#
        } else {
            // A tail `k(2)` would make `maybe` direct; this arm may not resume.
            r#"maybe(), k => if true { k(2) } else { 0 }"#
        };
        write(
            &d,
            "src/main.taut",
            &format!(
                r#"{}
extern {{ fn apply(f: &((i64) -> i64)): i64 }}
fn callback(n:i64): i64 ! {{ {} }} {{ {} }}
let result := handle {{ apply(&callback) }} with {{ {} }}
show(&result)"#,
                declaration, effect, body, arm
            ),
        );
        let out = cli(&d, "node");
        assert!(!out.status.success());
        assert!(
            String::from_utf8_lossy(&out.stderr).contains("may abandon"),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn owned_nib_callback_can_be_stored_in_rust_and_called_later() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "stored-callback" }
rust { bridge = "bridge" types { Saved = "stored_callback_bridge::Saved" } }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"stored-callback-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        r#"pub struct Saved(Box<dyn Fn(i64)->i64>);
pub fn save(f:impl Fn(i64)->i64+'static)->Saved{Saved(Box::new(f))}
pub fn use_saved(s:&Saved,n:i64)->i64{(s.0)(n)}"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"struct(affine) Saved {}
extern {
 fn save(f: (i64) -> i64): Saved
 fn use_saved(s: &Saved, n: i64): i64
}
let offset := 40
let saved := save((n) => offset + n)
show(&use_saved(&saved, 2))
show(&use_saved(&saved, 3))"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "42\n43\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn generic_borrowed_record_fields_and_nib_reborrows_keep_aliasing() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "field-demo" }
rust { bridge = "bridge" }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"field-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        "pub fn view<T>(x:&mut T)->&mut T{x}",
    );
    write(
        &d,
        "src/main.taut",
        r#"struct(copy) Point { x: i64, y: i64 }
extern { fn view<A>(value: &mut A): &mut A }
fn through<A>(value: &mut A): &mut A { view(&mut value) }
fn forward(point: &mut Point): &mut Point { &mut point }
fn bump(n: &mut i64): Unit { *n := n + 1 }
fn set(n: &mut i64, value:i64): Unit { *n := value }
var point := Point { x: 10, y: 20 }
{ let borrowed := through(&mut point)
  set(&mut borrowed.x, 40)
  bump(&mut borrowed.x)
  { let again := forward(&mut borrowed); set(&mut again.y, 50) }
  show(&borrowed.x)
}
show(&point)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "41\nPoint { x: 41, y: 50 }\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn concurrent_async_callbacks_preserve_wasm_stack_order() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "concurrent-wasm" }
rust { bridge = "bridge" }
javascript { extern { parallel = "host.mjs#parallel" wait = "host.mjs#wait" } }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"concurrent-wasm-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        "pub fn twice(f:&mut dyn FnMut(i64)->i64)->i64{f(1)+f(2)}",
    );
    write(
        &d,
        "host.mjs",
        "export async function parallel(f){const xs=await Promise.all([f(1n),f(2n)]);return xs[0]+xs[1];}export async function wait(n){await new Promise(r=>setTimeout(r,1));return n*10n;}",
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
extern {
 fn twice(f: &((i64) -> i64)): i64
 fn parallel(f: &((i64) -> i64)): i64 ! {wait}
 fn wait(n: i64): i64 ! {wait}
}
fn task(n: i64): i64 { twice((value) => n + wait(value)) }
show(&parallel(&task))"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "66\n");
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn opaque_clone_and_mutation_agree_with_the_rust_backend() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "clone-demo" }
rust { bridge = "bridge" types { State = "clone_demo_bridge::State" } }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"clone-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        r#"use std::sync::atomic::{AtomicI64,Ordering};
static COPIES:AtomicI64=AtomicI64::new(0);
pub struct State(i64);
impl Clone for State{fn clone(&self)->Self{COPIES.fetch_add(1,Ordering::SeqCst);Self(self.0)}}
pub fn make(n:i64)->State{State(n)}
pub fn read(s:&State)->i64{s.0}
pub fn update(s:&mut State,n:i64){s.0=n;}
pub fn copies()->i64{COPIES.load(Ordering::SeqCst)}"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"struct(shared) State {}
extern {
 fn make(n: i64): State
 fn read(s: &State): i64
 fn update(s: &mut State, n: i64): Unit
 fn copies(): i64
}
var original := make(1)
let copied := original
update(&mut original, 2)
show(&read(&copied))
show(&read(&original))
show(&copies())"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "1\n2\n1\n"
    );
    let rust = Command::new(env!("CARGO_BIN_EXE_tauto"))
        .args(["run", "--backend", "rust", "-o"])
        .arg(d.join("native"))
        .arg(&d)
        .output()
        .unwrap();
    success(&rust);
    assert_eq!(out.stdout, rust.stdout);
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn host_types_keep_the_host_object_and_release_it_once_nobody_holds_it() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "host-types" }
javascript {
  extern { make = "host/h.mjs#make" label = "host/h.mjs#label" consume = "host/h.mjs#consume" }
  types { Node = "host/h.mjs#release" }
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"extern {
  type(affine) Node
  fn make(name: Text): Node
  fn label(n: &Node): Text
  fn consume(n: Node): Text
}
let a := make("a")
show(&label(&a))
show(&consume(a))
{ let b := make("b") }
let s := make("s")
let t := s
show(&label(&t))
"#,
    );
    write(
        &d,
        "host/h.mjs",
        "const made=new Set();\nexport function make(name){const n={name};made.add(n);return n;}\nexport function label(n){if(!made.has(n))throw new Error('not the host object');return n.name;}\nexport function consume(n){return 'took '+n.name;}\nexport function release(n){if(!made.delete(n))throw new Error('released twice');console.log('release '+n.name);}\n",
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "\"a\"\n\"took a\"\nrelease b\n\"s\"\nrelease s\nrelease a\n"
    );
    write(
        &d,
        "src/main.taut",
        r#"extern {
  type(affine) Node
  fn make(name: Text): Node
}
let n := Node {}
"#,
    );
    let out = cli(&d, "node");
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr)
            .contains("Node is an extern type; only extern functions make its values")
    );
}

/// A type of the same name in another file does not take the key from the
/// extern type: `javascript.types { Node }` binds the extern `Node`.
#[test]
fn a_host_type_key_binds_the_extern_type_when_another_type_has_the_name() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "host-types-collide" }
javascript {
  extern { make = "host/h.mjs#make" label = "host/h.mjs#label" }
  types { Node = "host/h.mjs#release" }
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "src/main.taut",
        "import std::builtin::os\nimport \"native.taut\"\nimport \"other.taut\"\nperform main(() => {\n  let a := make(\"a\")\n  perform stdout(label(&a))\n  perform stdout(\"\\n\")\n  if weight() == 7 { perform stdout(\"seven\\n\") } else { () }\n})\n",
    );
    write(
        &d,
        "src/native.taut",
        "extern {\n  pub type(affine) Node\n  pub fn make(name: Text): Node\n  pub fn label(n: &Node): Text\n}\n",
    );
    write(
        &d,
        "src/other.taut",
        "pub(open) struct Node { w: i64 }\npub fn weight(): i64 { Node { w: 7 }.w }\n",
    );
    write(
        &d,
        "host/h.mjs",
        "export function make(name){return {name};}\nexport function label(n){return n.name;}\nexport function release(n){console.log('release '+n.name);}\n",
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "a\nseven\nrelease a\n"
    );
}

#[test]
fn instances_export_named_functions_without_running_the_program() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "exports" }
exports = ["add", "greet", "fetch_len", "count"]
javascript {
  extern { get = "host/h.mjs#get" }
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
extern { fn get(url: Text): Text ! {wait} }
enum Shape { Circle(i64), Square(i64) }
fn add(a: i64, b: i64): i64 { a + b }
fn greet(s: Shape): Text { match s { Circle(r) => "circle", Square(n) => "square" } }
fn fetch_len(u: Text): i64 { if get(u) == "x" { 1 } else { 2 } }
fn count(n: i64): i64 {
  show(&n)
  n
}
show(&1)
"#,
    );
    write(
        &d,
        "host/h.mjs",
        "export async function get(u){return u;}\n",
    );
    success(&cli(&d, "node"));
    write(
        &d,
        "out/use.mjs",
        r#"import { instantiate } from './program.mjs';
import * as h from './host/host/h.mjs';
const i = instantiate({get: h.get}, {show: t => console.log('shown ' + t)});
console.log(i.add(2n, 3n));
console.log(i.greet({owner:"Shape",tag:"Square",names:[null],fields:[4n],struct:false}));
const pending = i.fetch_len("x");
console.log(pending instanceof Promise, await pending);
console.log(i.count(7n));
i.dispose();
try { i.add(1n, 1n); } catch (e) { console.log(e.message); }
"#,
    );
    let out = Command::new("node")
        .arg(d.join("out/use.mjs"))
        .output()
        .unwrap();
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "5n\nsquare\ntrue 1n\nshown n = 7\n7n\nthe instance was disposed\n"
    );
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "exports" }
exports = ["ask_twice"]
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"effect ask(): i64
fn ask_twice(): i64 { perform ask() + perform ask() }
"#,
    );
    let out = cli(&d, "node");
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("javascript export ask_twice performs ask")
    );
}

#[test]
fn an_export_starts_a_task_that_outlives_the_call() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "tasks" }
exports = ["start", "once"]
javascript {
  extern { next = "host/h.mjs#next" report = "host/h.mjs#report" }
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
extern {
  fn next(): i64 ! {wait}
  fn report(v: i64): Unit
}
fn listen(n: i64): Unit ! {div, wait} {
  let v := next()
  report(v)
  if v < n { listen(n) } else { #() }
}
fn start(n: i64): Unit ! {div, wait, ∀ T. spawn(() -> T ! {})} {
  Task::detach(perform spawn(() => listen(n)))
}
fn once(): Unit ! {wait} { report(next()) }
"#,
    );
    write(
        &d,
        "host/h.mjs",
        "let waiting=[];export function next(){return new Promise(r=>waiting.push(r));}\nexport function report(v){console.log('got '+v);}\nexport function fire(v){const w=waiting;waiting=[];for(const r of w)r(v);return w.length;}\n",
    );
    success(&cli(&d, "node"));
    write(
        &d,
        "out/use.mjs",
        r#"import { instantiate } from './program.mjs';
import * as h from './host/host/h.mjs';
const flush = () => new Promise(r => setTimeout(r, 5));
const i = instantiate({next: h.next, report: h.report});
await i.start(3n);
console.log('returned');
for (const v of [1n, 2n]) { await flush(); console.log('fired', h.fire(v)); }
await flush();
i.dispose();
console.log('disposed', h.fire(9n));
await flush();
console.log('waiting after dispose', h.fire(9n));
"#,
    );
    let out = Command::new("node")
        .arg(d.join("out/use.mjs"))
        .output()
        .unwrap();
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "returned\nfired 1\ngot 1\nfired 1\ngot 2\ndisposed 1\nwaiting after dispose 0\n"
    );
    // `report` has no `wait` in its row, so its binding may not answer with
    // a Promise.
    write(
        &d,
        "out/promise.mjs",
        r#"import { instantiate } from './program.mjs';
const i = instantiate({next: async () => 1n, report: async () => null});
try { await i.once(); } catch (e) { console.log(e.message); }
"#,
    );
    let out = Command::new("node")
        .arg(d.join("out/promise.mjs"))
        .output()
        .unwrap();
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "extern report returned a Promise but its row has no wait\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn kept_callbacks_live_as_long_as_their_host_owner() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "callbacks" }
exports = ["setup", "teardown"]
javascript {
  extern { emitter = "host/h.mjs#emitter" listen = "host/h.mjs#listen" stash = "host/h.mjs#stash" take = "host/h.mjs#take" }
  types { Emitter = "host/h.mjs#close" }
  retain = ["listen"]
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"extern {
  type(affine) Emitter
  fn emitter(): Emitter
  fn listen(e: &Emitter, f: (n: i64) -> i64): Unit
  fn stash(e: Emitter): Unit
  fn take(): Emitter
}
fn setup(base: i64): Unit {
  let e := emitter()
  let offset := base * 10
  listen(&e, (n) => {
    show(&n)
    n + offset
  })
  stash(e)
}
fn teardown(): Unit { let e := take() }
"#,
    );
    write(
        &d,
        "host/h.mjs",
        "let saved;\nexport function emitter(){return {listeners:[]};}\nexport function listen(e,f){e.listeners.push(f);}\nexport function stash(e){saved=e;}\nexport function take(){return saved;}\nexport function close(){console.log('close');}\nexport function fire(n){return saved.listeners.map(f=>f(n));}\n",
    );
    success(&cli(&d, "node"));
    write(
        &d,
        "out/use.mjs",
        r#"import { instantiate } from './program.mjs';
import * as h from './host/host/h.mjs';
const i = instantiate(h, {release: {Emitter: h.close}});
i.setup(4n);
console.log(h.fire(1n));
i.teardown();
console.log(h.fire(2n));
"#,
    );
    let out = Command::new("node")
        .arg(d.join("out/use.mjs"))
        .output()
        .unwrap();
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "1\n[ 41n ]\nclose\n[ undefined ]\n"
    );
    write(
        &d,
        "src/main.taut",
        r#"effect ask(): i64
extern {
  type(affine) Emitter
  fn emitter(): Emitter
  fn listen(e: &Emitter, f: (n: i64) -> i64 ! {ask}): Unit
  fn stash(e: Emitter): Unit
  fn take(): Emitter
}
fn setup(base: i64): Unit { #() }
fn teardown(): Unit { #() }
"#,
    );
    let out = cli(&d, "node");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("keeps its callbacks"));
}

#[test]
fn a_running_kept_callback_holds_its_owner_until_it_finishes() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "callbacks" }
exports = ["setup", "teardown"]
javascript {
  extern { emitter = "host/h.mjs#emitter" listen = "host/h.mjs#listen" stash = "host/h.mjs#stash" take = "host/h.mjs#take" wait = "host/h.mjs#wait" }
  types { Emitter = "host/h.mjs#close" }
  retain = ["listen"]
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"import std::builtin::par
extern {
  type(affine) Emitter
  fn emitter(): Emitter
  fn listen(e: &Emitter, f: (n: i64) -> i64): ()
  fn stash(e: Emitter): ()
  fn take(): Emitter
  fn wait(n: i64): i64 ! {wait}
}
fn setup(): () {
  let e := emitter()
  listen(&e, (n) => {
    let m := wait(n)
    show(&m)
    m
  })
  stash(e)
}
fn teardown(): () { let e := take() }
"#,
    );
    write(
        &d,
        "host/h.mjs",
        r#"let saved,gate;
export function emitter(){return {listeners:[]};}
export function listen(e,f){e.listeners.push(f);}
export function stash(e){saved=e;}
export function take(){return saved;}
export function close(){console.log('close');}
export function wait(n){return new Promise(r=>{gate=()=>r(n);});}
export function open(){gate();}
export function fire(n){return saved.listeners.map(f=>f(n));}
"#,
    );
    success(&cli(&d, "node"));
    write(
        &d,
        "out/use.mjs",
        r#"import { instantiate } from './program.mjs';
import * as h from './host/host/h.mjs';
const i = instantiate(h, {release: {Emitter: h.close}});
await i.setup();
const [running] = h.fire(1n);
await i.teardown();
console.log('released');
console.log(h.fire(2n));
h.open();
console.log(await running);
"#,
    );
    let out = Command::new("node")
        .arg(d.join("out/use.mjs"))
        .output()
        .unwrap();
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "released\n[ undefined ]\n1\nclose\n1n\n"
    );
}

#[test]
fn exports_pass_host_values_and_functions() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "exports" }
exports = ["name_of", "rename", "make", "twice", "adder"]
javascript {
  extern { label = "host/h.mjs#label" fresh = "host/h.mjs#fresh" }
  types { Node = "host/h.mjs#close" }
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"extern {
  type(affine) Node
  fn label(n: &Node): Text
  fn fresh(name: Text): Node
}
fn name_of(n: &Node): Text { label(&n) }
fn rename(n: Node): Text { label(&n) }
fn make(name: Text): Node { fresh(name) }
fn twice(f: &((n: i64) -> i64), x: i64): i64 { f(f(x)) }
fn adder(k: i64): (n: i64) -> i64 { (n) => n + k }
"#,
    );
    write(
        &d,
        "host/h.mjs",
        r#"export function label(n){return n.name;}
export function fresh(name){return {name};}
export function close(n){console.log('close '+n.name);}
"#,
    );
    success(&cli(&d, "node"));
    write(
        &d,
        "out/use.mjs",
        r#"import { instantiate } from './program.mjs';
import * as h from './host/host/h.mjs';
const i = instantiate(h, {release: {Node: h.close}});
const a = {name:'a'};
console.log(await i.name_of(a));
console.log(await i.name_of(a));
console.log(await i.rename({name:'b'}));
const m = await i.make('m');
console.log(m.name, await i.name_of(m));
console.log(await i.twice(n => n * 3n, 2n));
console.log(await i.twice(async n => n + 1n, 2n));
const add = i.adder(10n);
console.log(add(5n));
i.dispose();
console.log(add(5n));
"#,
    );
    let out = Command::new("node")
        .arg(d.join("out/use.mjs"))
        .output()
        .unwrap();
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "a\na\nclose b\nb\nm m\n18n\n4n\n15n\nclose m\nclose a\nundefined\n"
    );
    for (source, message) in [
        (
            "fn keep(f: (n: i64) -> i64): i64 { f(1) }\n",
            "a function taken by value",
        ),
        (
            "effect ask(): i64\nfn keep(): (n: i64) -> i64 ! {ask} { (n) => n + perform ask() }\n",
            "a function result that performs an effect but show",
        ),
    ] {
        write(
            &d,
            "Tauto.eure",
            r#"package { name = "exports" }
exports = ["keep"]
"#,
        );
        write(&d, "src/main.taut", source);
        let out = cli(&d, "node");
        assert!(!out.status.success());
        assert!(
            String::from_utf8_lossy(&out.stderr).contains(message),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

#[test]
fn an_aborting_effect_releases_host_values() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "abort" }
javascript { extern { make = "host/h.mjs#make" } types { Node = "host/h.mjs#release" } sources = ["host"] }
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"effect stop(): i64 resume 0
extern {
  type(affine) Node
  fn make(name: Text): Node
}
let r := handle {
  let a := make("aborted")
  perform stop()
} with { stop() => 0 }
show(&r)
"#,
    );
    write(
        &d,
        "host/h.mjs",
        "export function make(name){return {name};}\nexport function release(n){console.log('release '+n.name);}\n",
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "release aborted\n0\n"
    );
}

#[test]
fn generic_function_values_keep_checked_arguments_through_wasm_specialization() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "generic-alias-demo" }
rust { bridge = "bridge" }"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"generic-alias-demo-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(
        &d,
        "bridge/src/lib.rs",
        "pub fn native_identity<T>(value: T) -> T { value }",
    );
    let source = r#"extern { fn native_identity<A>(value: A): A }
fn choose<B: Shared, A: Shared>(first: B, second: A, pick: Bool): (B | A) {
  if pick { native_identity(first) } else { native_identity(second) }
}
show(&choose("known", 7, true))
show(&choose("known", 7, false))
let alias := choose
show(&alias("other", 8, false))
fn outer<C: Shared>(captured: C): Unit {
  fn captured_choose<B: Shared, A: Shared>(known: B, witness: A, input: B | A, first: Bool): (B | A) {
    show(&captured)
    if first { known } else { input }
  }
  let alias := captured_choose
  let number: i64 := 7
  let input := if true { number } else { "unseen" }
  show(&captured_choose("known", number, input, false))
  show(&alias("known", number, input, true))
}
outer("kept")
show(&native_identity(11))"#;
    let package = tauto::nir::compile_javascript(source).unwrap();
    assert!(package.externs.iter().any(
        |external| external.name.as_str() == "native_identity" && !external.generics.is_empty()
    ));
    let mut checked_function_value = false;
    for function in &package.fns {
        function.body.walk(&mut |expression| {
            if let tauto_nir::ExprKind::FnValue { inst, targs } = &expression.kind
                && package.fns[*inst].source.as_str() == "choose"
            {
                assert_eq!(
                    package.fns[*inst]
                        .generics
                        .iter()
                        .map(|(name, _)| name.as_str())
                        .collect::<Vec<_>>(),
                    ["B", "A"]
                );
                assert_eq!(
                    targs,
                    &[
                        tauto_nir::Ty::Text,
                        tauto_nir::Ty::Int(tauto_nir::Width::W64)
                    ]
                );
                checked_function_value = true;
            }
        });
    }
    assert!(checked_function_value);
    write(&d, "src/main.taut", source);
    success(&cli(&d, "node"));
    assert!(d.join("out/externs.wasm").is_file());
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "\"known\"\n7\n8\n\"kept\"\n7\n\"kept\"\n\"known\"\n11\n"
    );
    assert!(out.stderr.is_empty());
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn chunks_load_on_their_first_call() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "chunks" }
javascript { chunks { settings = ["settings"] } }
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"fn square(n: i64): i64 { n * n }
fn doubled_square(n: i64): i64 { square(n) * 2 }
fn settings(n: i64): i64 { doubled_square(n) + 1 }
show(&square(3))
show(&settings(2))
show(&settings(3))
"#,
    );
    success(&cli(&d, "node"));
    let chunk = fs::read_to_string(d.join("out/chunk-settings.mjs")).unwrap();
    assert!(chunk.starts_with("import {"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "9\n9\n19\n"
    );
    // The chunk is read only when its entry is called: without it, the
    // program runs until that call and then fails.
    fs::remove_file(d.join("out/chunk-settings.mjs")).unwrap();
    let out = run(&d);
    assert!(!out.status.success());
    assert_eq!(String::from_utf8_lossy(&out.stdout), "9\n");
    assert!(String::from_utf8_lossy(&out.stderr).contains("chunk-settings.mjs"));
    // A rebuild without chunks removes the module.
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "chunks" }
"#,
    );
    success(&cli(&d, "node"));
    assert!(!d.join("out/chunk-settings.mjs").exists());
    success(&run(&d));
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "chunks" }
javascript { chunks { settings = ["missing"] } }
"#,
    );
    let out = cli(&d, "node");
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("javascript chunk settings names missing")
    );
}

#[test]
fn javascript_host_types_stay_out_of_the_wasm_build() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "mixed-types" }
javascript {
  extern { make = "host/h.mjs#make" label = "host/h.mjs#label" }
  types { Node = "host/h.mjs#release" }
  sources = ["host"]
}
rust { bridge = "bridge" }
"#,
    );
    write(
        &d,
        "bridge/Cargo.toml",
        "[package]\nname=\"mixed-types-bridge\"\nversion=\"0.1.0\"\nedition=\"2024\"\n",
    );
    write(&d, "bridge/src/lib.rs", "pub fn double(n:i64)->i64{n*2}\n");
    write(
        &d,
        "src/main.taut",
        r#"extern {
  type(affine) Node
  fn make(name: Text): Node
  fn label(n: &Node): Text
  fn double(n: i64): i64
}
let a := make("a")
show(&label(&a))
show(&double(21))
"#,
    );
    write(
        &d,
        "host/h.mjs",
        "export function make(name){return {name};}\nexport function label(n){return n.name;}\nexport function release(n){console.log('release '+n.name);}\n",
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "\"a\"\n42\nrelease a\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn a_value_the_host_got_back_can_be_passed_in_again() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "passback" }
exports = ["make", "size"]
"#,
    );
    write(
        &d,
        "src/main.taut",
        r#"struct Bag { items: List(i64), name: Text }
fn make(n: i64): Option(Bag) { Some(Bag { items: Cons(n, Cons(n + 1, Nil)), name: "bag" }) }
fn total(l: List(i64)): i64 { match l { Nil => 0, Cons(x, rest) => x + total(rest) } }
fn size(b: Option(Bag)): i64 {
  show(&0)
  match b { None => 0, Some(x) => total(x.items) }
}
"#,
    );
    success(&cli(&d, "node"));
    write(
        &d,
        "out/use.mjs",
        r#"import { instantiate } from './program.mjs';
const i = instantiate({}, {show: t => {}});
const s = i.make(4n);
console.log(i.size(s), i.size(s));
"#,
    );
    let out = Command::new("node")
        .arg(d.join("out/use.mjs"))
        .output()
        .unwrap();
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "9n 9n\n");
}
