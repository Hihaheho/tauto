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
        r#"package { name = "http-demo" sources = ["main.taut"] }
javascript { extern { get = "host/http.mjs#get" } async = ["get"] sources = ["host"] }
"#,
    );
    write(
        &d,
        "main.taut",
        r#"extern { fn get(url: Text): Text }
effect http_get(url: Text): Text resume 1
let text := handle { perform http_get("data:text/plain,hello") } with { http_get(url), k => k(get(url)) }
perform show("response", text)"#,
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
            "response = \"hello\"\n"
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
        r#"package { name = "host-demo" sources = ["main.taut"] }
javascript { node { wait = "host.mjs#wait" } async = ["wait"] }"#,
    );
    write(&d, "host.mjs", "export async function wait(){return 1n;}");
    write(
        &d,
        "main.taut",
        r#"extern { fn wait(): i64 }
perform show("n", wait())"#,
    );
    let out = cli(&d, "browser");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("unavailable"));
    write(
        &d,
        "main.taut",
        r#"extern { fn wait(): i64 }
effect ask(): i64 direct
let n := handle { perform ask() } with { ask(), k => k(wait()) }
perform show("n", n)"#,
    );
    let out = cli(&d, "node");
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("direct handler"));
    fs::remove_dir_all(d).unwrap();
}
#[test]
fn rust_externs_are_compiled_to_wasm() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "wasm-demo" sources = ["main.taut"] }
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
        "main.taut",
        r#"affine struct Counter {}
extern {
 fn make(n: i64): Counter
 fn bump(&mut n: Counter): i64
 fn consume(n: Counter): i64
 fn twice(n: i64): i64
 fn hello(&s: Text): Text
 fn append(&mut v: Vec(i64)): Unit
 fn maybe(n: i64): Option(i64)
}
perform show("wide", twice(9007199254740993))
perform show("text", hello("世界"))
var values := Vec::new()
append(&mut values)
perform show("values", values)
perform show("option", maybe(9))
var c := make(40)
perform show("bump", bump(&mut c))
perform show("consume", consume(c))
"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "wide = 18014398509481986\ntext = \"hello 世界\"\nvalues = Vec[42]\noption = Some(10)\nbump = 41\nconsume = 41\n"
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
        r#"package { name = "callback-demo" sources = ["main.taut"] }
javascript { extern { apply = "host.mjs#apply" } async = ["apply"] }"#,
    );
    write(
        &d,
        "host.mjs",
        "export async function apply(f){return (await f(2n))+(await f(3n));}",
    );
    write(
        &d,
        "main.taut",
        r#"effect ask(n: i64): i64 resume 1
extern { fn apply(&f: (n: i64) -> i64): i64 }
let r := handle { apply(&(n) => perform ask(n)) + 1 } with { ask(n), k => k(n * 10) }
perform show("r", r)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "r = 51\n");
    fs::remove_dir_all(d).unwrap();
}
#[test]
fn callback_abort_leaves_the_host_frame() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "callback-demo" sources = ["main.taut"] }
javascript { extern { apply = "host.mjs#apply" } async = ["apply"] }"#,
    );
    write(
        &d,
        "host.mjs",
        "export async function apply(f){return (await f(2n))+100n;}",
    );
    write(
        &d,
        "main.taut",
        r#"effect ask(n: i64): i64 resume <=1
extern { fn apply(&f: (n: i64) -> i64): i64 }
let r := handle { apply(&(n) => perform ask(n)) + 1 } with { ask(n), k => 7 }
perform show("r", r)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "r = 7\n");
    fs::remove_dir_all(d).unwrap();
}
#[test]
fn wasm_resources_are_released_at_scope_exit_and_abort() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "lifetime-demo" sources = ["main.taut"] }
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
        "main.taut",
        r#"affine struct Probe {}
extern { fn make(n: i64): Probe
 fn dropped(): i64 }
effect stop(): Never resume 0
fn scope(): Unit { let a := make(10); let b := make(20); #() }
fn leave(): Unit ! {stop} { let a := make(4); let b := make(8); perform stop() }
scope()
perform show("normal", dropped())
handle { leave() } with { stop() => #() }
perform show("abort", dropped())
let p := Some(make(9))
match p { Some(value) => #(), None => #() }
perform show("match", dropped())
"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "normal = 30\nabort = 42\nmatch = 51\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn host_boundaries_reject_reusable_callbacks_and_expired_borrows() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "boundary-demo" sources = ["main.taut"] }
javascript { extern { apply = "host.mjs#apply" } async = ["apply"] }"#,
    );
    write(
        &d,
        "host.mjs",
        "export async function apply(f){return await f(0n);}",
    );
    write(
        &d,
        "main.taut",
        r#"effect choose(): i64 resume ω
extern { fn apply(&f: (n: i64) -> i64): i64 }
let n := handle { apply(&(n) => perform choose()) } with { choose(), k => k(1) + k(2) }
perform show("n", n)"#,
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
        r#"package { name = "boundary-demo" sources = ["main.taut"] }
javascript { extern { remember = "host.mjs#remember" inspect = "host.mjs#inspect" } }"#,
    );
    write(
        &d,
        "host.mjs",
        "let saved;export function remember(v){saved=v;return null;}export function inspect(){return saved.get();}",
    );
    write(
        &d,
        "main.taut",
        r#"extern { fn remember(&n: i64): Unit
fn inspect(): i64 }
let n := 3
remember(&n)
perform show("n", inspect())"#,
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
        r#"package { name = "shared-demo" sources = ["main.taut"] }
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
        "main.taut",
        r#"shared struct Probe {}
extern { fn make(n: i64): Probe
fn inspect(p: Probe, n: i64): i64 }
effect choose(): i64 resume ω
let result := handle { inspect(make(10), perform choose()) } with { choose(), k => k(1) + k(2) }
perform show("result", result)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "result = 23\n");
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn generic_rust_externs_are_specialized_through_nib_functions() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "generic-demo" sources = ["main.taut"] }
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
        "main.taut",
        r#"extern {
 fn identity<A>(x: A): A
 fn reverse<A>(xs: Vec(A)): Vec(A)
}
fn indirect<A>(x: A): A { identity(x) }
perform show("number", indirect(42))
perform show("text", indirect("hello"))
var xs := Vec::new()
Vec::push(&mut xs, 1)
Vec::push(&mut xs, 2)
perform show("reverse", reverse(xs))"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "number = 42\ntext = \"hello\"\nreverse = Vec[2, 1]\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_callbacks_reenter_and_return_functions() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "function-demo" sources = ["main.taut"] }
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
        "main.taut",
        r#"extern {
 fn twice(&f: (n: i64) -> i64): i64
 fn add(n: i64): (i64) -> i64
 fn number(n: i64): i64
}
effect adjust(n: i64): i64 direct
let result := handle { twice(&(n) => number(n) + perform adjust(n)) } with { adjust(n), k => k(n) }
perform show("callback", result)
let f := add(40)
perform show("returned", f(2))
perform show("again", twice(&f))"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "callback = 55\nreturned = 42\nagain = 85\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_borrowed_returns_preserve_mutation_and_owner_lifetime() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "view-demo" sources = ["main.taut"] }
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
        "main.taut",
        r#"affine struct Counter {}
extern {
 fn make(n: i64): Counter
 fn count(&c: Counter): &i64
 fn count_mut(&mut c: Counter): &mut i64
 fn consume(c: Counter): i64
 fn first(&mut v: Vec(i64)): Option(&mut i64)
 fn numbers(&mut v: Vec(i64)): &mut Vec(i64)
 fn slice(&v: Vec(i64)): &Slice(i64)
 fn bump(&mut n: i64): Unit
}
var c := make(40)
{ let &n := count(&c); perform show("read", n) }
{ let &mut n := count_mut(&mut c); n := n + 1; bump(&mut n) }
perform show("owner", consume(c))
var values := Vec::new()
Vec::push(&mut values, 10)
match first(&mut values) { Some(n) => bump(&mut n), None => #() }
{ let &mut list := numbers(&mut values)
  Vec::push(&mut list, 20)
  handle { Vec::swap(&mut list, 0, 1) } with { out_of_bounds() => #() }
  match Vec::get_mut(&mut list, 0) { Some(n) => bump(&mut n), None => #() }
  perform show("popped", Vec::pop(&mut list))
}
{ let &s := slice(&values); perform show("length", Slice::len(&s)) }
perform show("updated", values)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "read = 40\nowner = 42\npopped = Some(11)\nlength = 1\nupdated = Vec[21]\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_callback_waits_for_fetch_and_reenters_after_suspension() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "async-wasm" sources = ["main.taut"] }
rust { bridge = "bridge" }
javascript { extern { get = "host.mjs#get" } async = ["get"] }"#,
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
        "main.taut",
        r#"extern {
 fn twice(&f: (n: i64) -> i64): i64
 fn number(n: i64): i64
 fn get(): i64
}
effect ask(n: i64): i64 resume 1
let result := handle { twice(&(n) => perform ask(n)) } with {
 ask(n), k => k(number(n) + get())
}
perform show("async", result)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "async = 64\n");
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_callback_borrows_rust_stack_and_updates_it() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "borrow-callback" sources = ["main.taut"] }
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
        "main.taut",
        r#"extern { fn edit(&f: (&mut n: i64) -> Unit): i64 }
fn change(&mut value: i64): Unit { value := value + 2 }
let n := edit(&change)
perform show("edited", n)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "edited = 42\n");
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn wasm_opaque_iterator_view_keeps_its_vector_alive() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "iterator-demo" sources = ["main.taut"] }
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
        "main.taut",
        r#"view struct Cursor {}
extern {
 fn cursor(&v: Vec(i64)): Cursor
 fn next(&mut c: Cursor): Option(&i64)
}
var values := Vec::new()
Vec::push(&mut values, 10)
Vec::push(&mut values, 20)
{ var &it := cursor(&values)
  match next(&mut it) { Some(n) => perform show("first", n), None => #() }
  match next(&mut it) { Some(n) => perform show("second", n), None => #() }
}
perform show("owner", values)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "first = 10\nsecond = 20\nowner = Vec[10, 20]\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn abandoning_rust_callbacks_are_rejected_before_wasm_build() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "native-callback-policy" sources = ["main.taut"] }
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
            r#"maybe(), k => k(2)"#
        };
        write(
            &d,
            "main.taut",
            &format!(
                r#"{}
extern {{ fn apply(&f: (i64) -> i64): i64 }}
fn callback(n:i64): i64 ! {{ {} }} {{ {} }}
let result := handle {{ apply(&callback) }} with {{ {} }}
perform show("result",result)"#,
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
        r#"package { name = "stored-callback" sources = ["main.taut"] }
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
        "main.taut",
        r#"affine struct Saved {}
extern {
 fn save(f: (i64) -> i64): Saved
 fn use_saved(&s: Saved, n: i64): i64
}
let offset := 40
let saved := save((n) => offset + n)
perform show("stored", use_saved(&saved, 2))
perform show("again", use_saved(&saved, 3))"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "stored = 42\nagain = 43\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn generic_borrowed_record_fields_and_nib_reborrows_keep_aliasing() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "field-demo" sources = ["main.taut"] }
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
        "pub fn is_view<T>(x:&mut T)->&mut T{x}",
    );
    write(
        &d,
        "main.taut",
        r#"copy struct Point { x: i64, y: i64 }
extern { fn r#view<A>(&mut value: A): &mut A }
fn through<A>(&mut value: A): &mut A { r#view(&mut value) }
fn forward(&mut point: Point): &mut Point { &mut point }
fn bump(&mut n: i64): Unit { n := n + 1 }
fn set(&mut n: i64, value:i64): Unit { n := value }
var point := Point { x: 10, y: 20 }
{ let &mut borrowed := through(&mut point)
  set(&mut borrowed.x, 40)
  bump(&mut borrowed.x)
  { let &mut again := forward(&mut borrowed); set(&mut again.y, 50) }
  perform show("field", borrowed.x)
}
perform show("owner", point)"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "field = 41\nowner = Point { x: 41, y: 50 }\n"
    );
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn concurrent_async_callbacks_preserve_wasm_stack_order() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "concurrent-wasm" sources = ["main.taut"] }
rust { bridge = "bridge" }
javascript { extern { parallel = "host.mjs#parallel" wait = "host.mjs#wait" } async = ["parallel", "wait"] }"#,
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
        "main.taut",
        r#"extern {
 fn twice(&f: (i64) -> i64): i64
 fn parallel(&f: (i64) -> i64): i64
 fn wait(n: i64): i64
}
fn task(n: i64): i64 { twice(&(value) => n + wait(value)) }
perform show("concurrent", parallel(&task))"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "concurrent = 66\n");
    fs::remove_dir_all(d).unwrap();
}

#[test]
fn opaque_clone_and_mutation_agree_with_the_rust_backend() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "clone-demo" sources = ["main.taut"] }
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
        "main.taut",
        r#"shared struct State {}
extern {
 fn make(n: i64): State
 fn read(&s: State): i64
 fn update(&mut s: State, n: i64): Unit
 fn copies(): i64
}
var original := make(1)
let copied := original
update(&mut original, 2)
perform show("copy", read(&copied))
perform show("original", read(&original))
perform show("clones", copies())"#,
    );
    success(&cli(&d, "node"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "copy = 1\noriginal = 2\nclones = 1\n"
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
        r#"package { name = "host-types" sources = ["main.taut"] }
javascript {
  extern { make = "host/h.mjs#make" label = "host/h.mjs#label" consume = "host/h.mjs#consume" }
  types { Node = "host/h.mjs#release" }
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "main.taut",
        r#"extern {
  affine type Node
  fn make(name: Text): Node
  fn label(&n: Node): Text
  fn consume(n: Node): Text
}
let a := make("a")
perform show("label", label(&a))
perform show("consume", consume(a))
{ let b := make("b") }
let s := make("s")
let t := s
perform show("moved", label(&t))
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
        "label = \"a\"\nconsume = \"took a\"\nrelease b\nmoved = \"s\"\nrelease s\nrelease a\n"
    );
    write(
        &d,
        "main.taut",
        r#"extern {
  affine type Node
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

#[test]
fn instances_export_named_functions_without_running_the_program() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "exports" sources = ["main.taut"] }
javascript {
  exports = ["add", "greet", "fetch_len", "count"]
  extern { get = "host/h.mjs#get" }
  async = ["get"]
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "main.taut",
        r#"extern { fn get(url: Text): Text }
enum Shape { Circle(i64), Square(i64) }
fn add(a: i64, b: i64): i64 { a + b }
fn greet(s: Shape): Text { match s { Circle(r) => "circle", Square(n) => "square" } }
fn fetch_len(u: Text): i64 { if get(u) == "x" { 1 } else { 2 } }
fn count(n: i64): i64 {
  perform show("n", n)
  n
}
perform show("top", 1)
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
        r#"package { name = "exports" sources = ["main.taut"] }
javascript { exports = ["ask_twice"] }
"#,
    );
    write(
        &d,
        "main.taut",
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
fn kept_callbacks_live_as_long_as_their_host_owner() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "callbacks" sources = ["main.taut"] }
javascript {
  exports = ["setup", "teardown"]
  extern { emitter = "host/h.mjs#emitter" listen = "host/h.mjs#listen" stash = "host/h.mjs#stash" take = "host/h.mjs#take" }
  types { Emitter = "host/h.mjs#close" }
  retain = ["listen"]
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "main.taut",
        r#"extern {
  affine type Emitter
  fn emitter(): Emitter
  fn listen(&e: Emitter, f: (n: i64) -> i64): Unit
  fn stash(e: Emitter): Unit
  fn take(): Emitter
}
fn setup(base: i64): Unit {
  let e := emitter()
  let offset := base * 10
  listen(&e, (n) => {
    perform show("event", n)
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
        "event = 1\n[ 41n ]\nclose\n[ undefined ]\n"
    );
    write(
        &d,
        "main.taut",
        r#"effect ask(): i64
extern {
  affine type Emitter
  fn emitter(): Emitter
  fn listen(&e: Emitter, f: (n: i64) -> i64 ! {ask}): Unit
  fn stash(e: Emitter): Unit
  fn take(): Emitter
}
fn setup(base: i64): Unit { }
fn teardown(): Unit { }
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
        r#"package { name = "callbacks" sources = ["main.taut"] }
javascript {
  exports = ["setup", "teardown"]
  extern { emitter = "host/h.mjs#emitter" listen = "host/h.mjs#listen" stash = "host/h.mjs#stash" take = "host/h.mjs#take" wait = "host/h.mjs#wait" }
  types { Emitter = "host/h.mjs#close" }
  retain = ["listen"]
  async = ["wait"]
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "main.taut",
        r#"extern {
  affine type Emitter
  fn emitter(): Emitter
  fn listen(&e: Emitter, f: (n: i64) -> i64): ()
  fn stash(e: Emitter): ()
  fn take(): Emitter
  fn wait(n: i64): i64
}
fn setup(): () {
  let e := emitter()
  listen(&e, (n) => {
    let m := wait(n)
    perform show("done", m)
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
        "released\n[ undefined ]\ndone = 1\nclose\n1n\n"
    );
}

#[test]
fn exports_pass_host_values_and_functions() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "exports" sources = ["main.taut"] }
javascript {
  exports = ["name_of", "rename", "make", "twice", "adder"]
  extern { label = "host/h.mjs#label" fresh = "host/h.mjs#fresh" }
  types { Node = "host/h.mjs#close" }
  sources = ["host"]
}
"#,
    );
    write(
        &d,
        "main.taut",
        r#"extern {
  affine type Node
  fn label(&n: Node): Text
  fn fresh(name: Text): Node
}
fn name_of(&n: Node): Text { label(&n) }
fn rename(n: Node): Text { label(&n) }
fn make(name: Text): Node { fresh(name) }
fn twice(&f: (n: i64) -> i64, x: i64): i64 { f(f(x)) }
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
            r#"package { name = "exports" sources = ["main.taut"] }
javascript { exports = ["keep"] }
"#,
        );
        write(&d, "main.taut", source);
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
        r#"package { name = "abort" sources = ["main.taut"] }
javascript { extern { make = "host/h.mjs#make" } types { Node = "host/h.mjs#release" } sources = ["host"] }
"#,
    );
    write(
        &d,
        "main.taut",
        r#"effect stop(): i64 resume 0
extern {
  affine type Node
  fn make(name: Text): Node
}
let r := handle {
  let a := make("aborted")
  perform stop()
} with { stop() => 0 }
perform show("after", r)
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
        "release aborted\nafter = 0\n"
    );
}

#[test]
fn generic_function_values_keep_checked_arguments_through_wasm_specialization() {
    let d = dir();
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "generic-alias-demo" sources = ["main.taut"] }
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
perform show("left", choose("known", 7, true))
perform show("right", choose("known", 7, false))
let alias := choose
perform show("alias", alias("other", 8, false))
fn outer<C: Shared>(captured: C): Unit {
  fn captured_choose<B: Shared, A: Shared>(known: B, witness: A, input: B | A, first: Bool): (B | A) {
    perform show("captured", captured)
    if first { known } else { input }
  }
  let alias := captured_choose
  let number: i64 := 7
  let input := if true { number } else { "unseen" }
  perform show("direct", captured_choose("known", number, input, false))
  perform show("alias", alias("known", number, input, true))
}
outer("kept")
perform show("native", native_identity(11))"#;
    let package = tauto_nir::compile_javascript(source).unwrap();
    assert!(
        package
            .externs
            .iter()
            .any(|external| external.name == "native_identity" && !external.generics.is_empty())
    );
    let mut checked_function_value = false;
    for function in &package.fns {
        function.body.walk(&mut |expression| {
            if let tauto_nir::ExprKind::FnValue { inst, targs } = &expression.kind
                && package.fns[*inst].source == "choose"
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
    write(&d, "main.taut", source);
    success(&cli(&d, "node"));
    assert!(d.join("out/externs.wasm").is_file());
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "left = \"known\"\nright = 7\nalias = 8\ncaptured = \"kept\"\ndirect = 7\ncaptured = \"kept\"\nalias = \"known\"\nnative = 11\n"
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
        r#"package { name = "chunks" sources = ["main.taut"] }
javascript { chunks { settings = ["settings"] } }
"#,
    );
    write(
        &d,
        "main.taut",
        r#"fn square(n: i64): i64 { n * n }
fn doubled_square(n: i64): i64 { square(n) * 2 }
fn settings(n: i64): i64 { doubled_square(n) + 1 }
perform show("main", square(3))
perform show("chunk", settings(2))
perform show("again", settings(3))
"#,
    );
    success(&cli(&d, "node"));
    let chunk = fs::read_to_string(d.join("out/chunk-settings.mjs")).unwrap();
    assert!(chunk.starts_with("import {"));
    let out = run(&d);
    success(&out);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "main = 9\nchunk = 9\nagain = 19\n"
    );
    // The chunk is read only when its entry is called: without it, the
    // program runs until that call and then fails.
    fs::remove_file(d.join("out/chunk-settings.mjs")).unwrap();
    let out = run(&d);
    assert!(!out.status.success());
    assert_eq!(String::from_utf8_lossy(&out.stdout), "main = 9\n");
    assert!(String::from_utf8_lossy(&out.stderr).contains("chunk-settings.mjs"));
    // A rebuild without chunks removes the module.
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "chunks" sources = ["main.taut"] }
"#,
    );
    success(&cli(&d, "node"));
    assert!(!d.join("out/chunk-settings.mjs").exists());
    success(&run(&d));
    write(
        &d,
        "Tauto.eure",
        r#"package { name = "chunks" sources = ["main.taut"] }
javascript { chunks { settings = ["missing"] } }
"#,
    );
    let out = cli(&d, "node");
    assert!(!out.status.success());
    assert!(
        String::from_utf8_lossy(&out.stderr).contains("javascript chunk settings names missing")
    );
}
