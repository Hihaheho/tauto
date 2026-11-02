//! Stack depth and ownership contracts of generated JavaScript.
use std::{
    fs,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(0);

fn execute(module: &str) -> String {
    let dir = std::env::temp_dir().join(format!(
        "tauto-js-lifetimes-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("test.mjs");
    fs::write(&file, module).unwrap();
    let output = Command::new("node")
        .arg(&file)
        .output()
        .expect("node is required for JavaScript backend tests");
    fs::remove_dir_all(&dir).unwrap();
    assert!(
        output.status.success(),
        "stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

fn generated(source: &str, host: &str) -> String {
    let package = tauto_nir::compile(source).unwrap();
    let module = tauto_jsgen::generate(&package).unwrap();
    execute(&format!("{module}\n{host}"))
}

fn generated_case(name: &str, host: &str) -> String {
    let source = case_inputs::source(name);
    // The tail-call programs keep the checked extraction evidence (a tote that
    // imports the program) instead of treating proof source as an ordinary
    // runtime function, which would charge divergent-call fuel.
    let package = if name.starts_with("backend-tail-self-call/") {
        compile_extracted(source)
    } else {
        tauto_nir::compile_javascript(source).unwrap()
    };
    let module = tauto_jsgen::generate(&package).unwrap();
    execute(&format!("{module}\n{host}"))
}

/// The program, importing `std/Base.taut`, loaded through a tote as a build reads it.
fn compile_extracted(source: &str) -> tauto_nir::Package {
    let dir = std::env::temp_dir().join(format!(
        "tauto-js-extracted-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(dir.join("src")).unwrap();
    let base = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../std/Base.taut")
        .canonicalize()
        .unwrap();
    let import_base = format!("import {:?}\n", base.to_string_lossy());
    let entry = dir.join("program.taut");
    fs::write(&entry, format!("{source}\n{import_base}")).unwrap();
    let entry = entry.canonicalize().unwrap();
    let wrapper = dir.join("imports.taut");
    fs::write(
        &wrapper,
        format!("{import_base}import {:?}\n", entry.to_string_lossy()),
    )
    .unwrap();
    fs::write(
        dir.join("src/main.taut"),
        format!("import {:?}\n", wrapper.to_string_lossy()),
    )
    .unwrap();
    fs::write(
        dir.join("Tauto.eure"),
        "package { name = \"case\"\nversion = \"0.1.0\" }",
    )
    .unwrap();
    let loaded = tauto::program::load_tote_for_build(&dir).unwrap();
    let package = tauto_nir::compile_loaded_with_observer(&loaded, false, true, |_| {}).unwrap();
    fs::remove_dir_all(&dir).unwrap();
    package
}

fn runtime(test: &str) {
    execute(&format!(
        "{}\n{}\n{}\n{}\nimport assert from 'node:assert/strict';\n{test}",
        include_str!("../../tauto-jsgen/src/runtime.js"),
        include_str!("../../tauto-jsgen/src/cps.js"),
        include_str!("../../tauto-jsgen/src/resources.js"),
        include_str!("../../tauto-jsgen/src/builtins.js"),
    ));
}

#[test]
fn generated_captures_keep_their_lexical_activation() {
    for (case, expected) in [
        ("borrowed-recursive-capture", "plain = 1\nwith_helper = 1\n"),
        (
            "resumed-boundary-capture",
            "resumed_plain = 1\nresumed_with_helper = 1\n",
        ),
        ("resumed-operation-arm-capture", "arm = 1\n"),
        ("resumed-return-arm-capture", "return = 1\n"),
    ] {
        assert_eq!(
            generated_case(&format!("backend-capture-bindings/{case}"), "await run();"),
            expected,
            "{case}",
        );
    }
}

#[test]
fn generated_closure_ownership_matches_checked_binding_kinds() {
    for (name, expected) in [
        (
            "copy-captures-remain-readable",
            "first = 17\noriginal = 17\nsecond = 17\n",
        ),
        (
            "shared-capture-last-use-remains-repeatable",
            "first = \"kept\"\nsecond = \"kept\"\n",
        ),
        ("nested-affine-capture", "nested = 23\n"),
        ("linear-capture-is-consumed", "linear = 31\n"),
        (
            "borrowed-capture-is-not-consumed",
            "before = 14\nafter = 18\noriginal = 9\n",
        ),
    ] {
        assert_eq!(
            generated_case(&format!("backend-closure-ownership/{name}"), "await run();"),
            expected,
            "{name}",
        );
    }
}

#[test]
fn generated_owned_callee_and_capture_release_when_host_throws() {
    for name in ["lambda-argument-exception", "lambda-body-exception"] {
        generated(
            case_inputs::fixture_static("backend-closure-ownership-fixtures.eure", name),
            r#"let drops=0,retains=0;
const failure=new Error('host failed');
try{
    await run(()=>{throw new Error('unexpected output');},{
        make(){return {resource:true,retain(){retains++;},release(){drops++;}};},
        fail(){throw failure;}
    });
    throw new Error('host exception was lost');
}catch(error){if(error!==failure)throw error;}
if(drops!==1||retains!==0)throw new Error('incorrect exception ownership: '+drops+'/'+retains);"#,
        );
    }
}

#[test]
fn owned_closures_transfer_captures_and_abandoned_callees() {
    runtime(
        r#"let drops=0,retains=0;
const resource=n=>{let owners=1;return {resource:true,retain(){retains++;owners++;},release(){assert(owners>0);if(--owners===0)drops+=n;}};};
const closure=(id,params=[])=>closureValue(readLocal(id,false,false,true),params,[id],false,[],false,params.map(()=>true),[id],true);
const check=n=>(c,k)=>{assert.equal(drops,n);return k(c,null);};
await drive(sequence([
    defineLocal(1,false,pure(resource(20))),
    sequence([defineLocal(2,false,closure(1)),pure(null)]),check(20),
    defineLocal(3,false,pure(resource(160))),
    sequence([defineLocal(4,false,closure(3)),defineLocal(5,false,pure(resource(320))),
        defineLocal(6,false,callFunction(readLocal(4,false,false,true),[],false)),pure(null)]),check(500),
    defineLocal(7,false,pure(resource(10240))),
    sequence([defineLocal(9,false,closure(7,[8])),
        handleValue(callFunction(readLocal(9,false,false,true),[performValue('stop','zero',[])],false),
            [{op:'stop',pats:[],k:null,guard:pure(true),body:pure(null)}],null),check(10740)])
]),()=>{},{});
assert.equal(drops,10740);assert.equal(retains,0);
for(const inBody of [false,true]){
    let count=0;const value={release(){count++;}};
    const fail=()=>{throw new Error('failed');};
    const body=inBody?fail:readLocal(1,false,false,true);
    const make=closureValue(body,[3],[1],false,[],false,[true],[1],true);
    await assert.rejects(drive(sequence([defineLocal(1,false,pure(value)),defineLocal(2,false,make),
        callFunction(readLocal(2,false,false,true),[inBody?pure(0n):fail],false)]),()=>{},{}),/failed/);
    assert.equal(count,1);
}
let movedDrops=0,copyDrops=0;
await assert.rejects(drive(sequence([
    defineLocal(1,false,pure({release(){movedDrops++;}})),
    defineLocal(2,false,pure({copy(){throw new Error('copy failed');},release(){copyDrops++;}})),
    closureValue(pure(null),[],[1,2],false,[],false,[],[1],true)
]),()=>{},{}),/copy failed/);
assert.equal(movedDrops,1);assert.equal(copyDrops,1);
"#,
    );
}

#[test]
fn reusable_and_borrowed_closures_preserve_their_capture_owners() {
    runtime(
        r#"let drops=0,owners=1,retains=0;
const resource={retain(){retains++;owners++;},release(){assert(owners>0);if(--owners===0)drops++;}};
await drive(sequence([
    defineLocal(1,false,pure(resource)),
    defineLocal(2,false,closureValue(readLocal(1,false,true),[],[1],false,[],false,[],[],false)),
    callFunction(readLocal(2,false,true),[],false),callFunction(readLocal(2,false,true),[],false),
    (c,k)=>{assert.equal(owners,2);assert.equal(drops,0);return k(c,null);},
    defineLocal(3,true,pure(0n)),
    defineLocal(4,false,closureValue((c,k)=>{c.env[3].value++;return k(c,c.env[3].value);},[],[3],true)),
    callFunction(readLocal(4,false,true),[],false),callFunction(readLocal(4,false,true),[],false),
    (c,k)=>{assert.equal(c.env[3].value,2n);assert.equal(drops,0);return k(c,null);}
]),()=>{},{});
assert.equal(owners,0);assert.equal(drops,1);assert.equal(retains,5);
"#,
    );
}

#[test]
fn many_shot_resumptions_preserve_reusable_closure_capture_owners() {
    runtime(
        r#"let owners=1,drops=0,calls=0;
const resource={retain(){owners++;},release(){assert(owners>0);if(--owners===0)drops++;}};
const body=sequence([
    defineLocal(1,false,pure(resource)),
    defineLocal(2,false,closureValue(readLocal(1,false,true),[],[1],false,[],false)),
    performValue('pause','many',[]),
    callFunction(readLocal(2,false,true),[],false)
]);
const arm={op:'pause',pats:[],k:3,guard:pure(true),body:(c,k)=>{
    const resume=c.env[3].value;
    return resume(c,[null],(after,first)=>{
        assert.equal(first,resource);dropValue(first);calls++;
        return resume(after,[null],(done,second)=>{
            assert.equal(second,resource);dropValue(second);calls++;
            assert.equal(drops,0);return k(done,null);
        });
    });
}};
await drive(handleValue(body,[arm],null),()=>{},{});
assert.equal(calls,2);assert.equal(owners,0);assert.equal(drops,1);
"#,
    );
}

#[test]
fn retained_owned_callback_transfers_once_without_disabling_host_retains() {
    runtime(
        r#"for(const invoke of [false,true]){
    let saved,drops=0,retains=0;
    const resource={retain(){retains++;},release(){drops++;}};
    await drive(sequence([
        defineLocal(1,false,pure(resource)),
        defineLocal(2,false,closureValue(readLocal(1,false,false,true),[],[1],false,[],false,[],[1],true)),
        (c,k)=>{saved=copyValue(c.env[2].value);return k(c,null);}
    ]),()=>{},{});
    assert.equal(drops,0);assert.equal(retains,0);
    if(invoke){
        saved.retain();
        const result=await drive(callFunction(pure(saved),[],false),()=>{},{});
        assert.equal(result,resource);assert.equal(drops,0);
        dropValue(result);assert.equal(drops,1);
        await assert.rejects(drive((c,k)=>saved(c,[],k),()=>{},{}),/called more than once/);
        assert.equal(drops,1);
    }
    saved.release();assert.equal(drops,1);
}
"#,
    );
}

#[test]
fn lexical_scope_aliases_preserve_binding_identity_without_ownership() {
    runtime(
        r#"const root=openScope(null);let drops=0;
const outer=own(root,{id:1,value:{release(){drops++;}},shared:false});
const caller=openScope(root),shadow=own(caller,{id:1,value:20n,shared:false});
const scope=openAliasScope(caller,{1:outer,7:outer});
let restored=restoreEnv({1:outer,7:outer},scope);
assert.equal(restored[1],outer);assert.equal(restored[7],outer);
const parameter=own(scope,{id:1,value:30n,shared:false});
restored=restoreEnv({1:outer,7:outer},scope);
assert.equal(restored[1],parameter);assert.equal(restored[7],outer);
outer.value.marker=45n;
assert.equal(restored[7].value.marker,45n);
closeScope(scope);assert.equal(drops,0);assert.equal(outer.owners,1);
// Unannotated runtime scopes keep their ordinary nearest-slot lookup.
assert.equal(restoreEnv({1:outer},caller)[1],shadow);
const foreign={value:45n,shared:false},foreignScope=openAliasScope(caller,{8:foreign});
assert.equal(restoreEnv({8:foreign},foreignScope)[8],foreign);
closeScope(foreignScope);assert.equal(foreign.value,45n);
closeScope(caller);closeScope(root);assert.equal(drops,1);
assert.equal(root.open.size,0);
"#,
    );
}

#[test]
fn continuation_aliases_follow_physical_copies_and_preserve_outside_slots() {
    runtime(
        r#"const root=openScope(null);let owners=1,drops=0,outsideDrops=0,sharedDrops=0;
const resource={retain(){owners++;},release(){if(--owners===0)drops++;}};
const outside=own(root,{id:1,value:{release(){outsideDrops++;}},shared:false});
const outer=openScope(root),local=own(outer,{id:2,value:resource,shared:false});
const shared=own(outer,{id:3,value:{release(){sharedDrops++;}},shared:true});
const inner=openAliasScope(outer,{7:local,8:outside,9:shared});
const env={2:local,7:local,8:outside,9:shared};
const snapshot=captureContext({scope:inner,env},root,true,{10:outside});
assert.equal(owners,1);
const first=resumeContext(snapshot,root,true);
const second=resumeContext(snapshot,first.scope,true);
assert.equal(owners,3);
assert.notEqual(first.env[2],local);assert.notEqual(second.env[2],first.env[2]);
for(const resumed of [first,second]){
    const restored=restoreEnv({...env,10:outside},resumed.scope);
    assert.equal(restored[2],resumed.env[2]);assert.equal(restored[7],resumed.env[2]);
    assert.equal(restored[8],outside);assert.equal(restored[9],shared);
    assert.equal(restored[10],outside);
}
// A callback from the first resumption is not rebound to its nearer sibling.
const callback=openAliasScope(second.scope,{7:first.env[2]});
assert.equal(restoreEnv({7:first.env[2]},callback)[7],first.env[2]);
const nested=captureContext({scope:callback,env:{7:first.env[2]}},second.scope,false);
const transferred=resumeContext(nested,second.scope,false);
// A single-shot resumption moves its frames instead of copying them.
assert.equal(transferred.scope,callback);
assert.equal(restoreEnv({7:first.env[2]},transferred.scope)[7],first.env[2]);
assert.equal(owners,3);assert.equal(shared.owners,1);
for(const scope of [...root.open].reverse())closeScope(scope);
assert.equal(owners,0);assert.equal(drops,1);assert.equal(outsideDrops,1);
assert.equal(sharedDrops,1);assert.equal(root.open.size,0);
"#,
    );
}

#[test]
fn continuation_boundary_aliases_do_not_modify_original_or_empty_snapshots() {
    runtime(
        r#"for(const clone of [false,true]){
    const root=openScope(null),source=openScope(root),caller=openScope(root);
    const lexical=own(root,{id:1,value:11n,shared:false});
    const dynamic=own(caller,{id:1,value:22n,shared:false});
    const snapshot=captureContext({scope:source,env:{1:lexical}},root,clone,{1:lexical});
    // A clone leaves the original alone; a single-shot snapshot moves it.
    assert.equal(scopeAliases.has(source),!clone);
    const resumed=resumeContext(snapshot,caller,clone);
    assert.equal(restoreEnv({1:lexical},resumed.scope)[1],lexical);
    const empty=captureContext({scope:root,env:{1:lexical}},root,clone,{1:lexical});
    assert.equal(empty.frames.length,0);
    const emptyResume=resumeContext(empty,caller,clone);
    assert.equal(emptyResume.scope,caller);
    assert.equal(restoreEnv({1:lexical},emptyResume.scope)[1],dynamic);
    for(const scope of [...root.open].reverse())closeScope(scope);
    assert.equal(root.open.size,0);
}
"#,
    );
}

#[test]
fn handler_alias_scopes_close_on_rejection_completion_and_abandonment() {
    runtime(
        r#"for(const quant of ['direct','one','many','zero']){
    let registry,rejectedDrops=0,armDrops=0,rootDrops=0;
    const rejected={op:'ask',pats:[],k:2,guard:(c,k)=>{
        own(c.scope,{id:90,value:{release(){rejectedDrops++;}},shared:false});
        return k(c,false);
    },body:()=>{throw new Error('rejected arm ran');}};
    const accepted={op:'ask',pats:[],k:2,guard:pure(true),body:(c,k)=>{
        assert.equal(rejectedDrops,1);
        own(c.scope,{id:91,value:{release(){armDrops++;}},shared:false});
        if(quant==='one'||quant==='many')return c.env[2].value(c,[7n],k);
        return k(c,7n);
    }};
    const start=(c,k)=>{
        registry=c.scope.open;
        const slot=own(c.scope,{id:1,value:{release(){rootDrops++;}},shared:false});
        return handleValue(performValue('ask',quant,[]),[rejected,accepted],null)({...c,env:{1:slot}},k);
    };
    assert.equal(await drive(start,()=>{},{}),7n);
    assert.equal(rejectedDrops,1);assert.equal(armDrops,1);assert.equal(rootDrops,1);
    assert.equal(registry.size,0);
}
"#,
    );
}

#[test]
fn handler_alias_scopes_close_when_guards_bodies_or_return_arms_throw() {
    runtime(
        r#"for(const phase of ['guard','body','return']){
    let registry,localDrops=0,rootDrops=0;
    const failure=new Error(phase);
    const fail=(c,k)=>{
        own(c.scope,{id:90,value:{release(){localDrops++;}},shared:false});
        throw failure;
    };
    const arm={op:'ask',pats:[],k:2,
        guard:phase==='guard'?fail:pure(true),
        body:phase==='body'?fail:pure(7n)};
    const ret=phase==='return'?[['bind',3,false,false],pure(true),fail]:null;
    const start=(c,k)=>{
        registry=c.scope.open;
        const slot=own(c.scope,{id:1,value:{release(){rootDrops++;}},shared:false});
        const body=phase==='return'?pure(7n):performValue('ask','one',[]);
        return handleValue(body,[arm],ret)({...c,env:{1:slot}},k);
    };
    await assert.rejects(drive(start,()=>{},{}),error=>error===failure);
    assert.equal(localDrops,1,phase);assert.equal(rootDrops,1,phase);
    assert.equal(registry.size,0,phase);
}
"#,
    );
}

#[test]
fn generated_deep_borrowed_list_traversal() {
    assert_eq!(
        generated(
            &r#"fn length(&items: List(i64)): i64 ! {Div} {
    match items { Nil => 0, Cons(head, tail) => 1 + length(&tail) }
}
var items: List(i64) := Nil
var index := 0
while index < 20000 { items := Cons(index, items); index := index + 1 }
perform show("length", length(&items))"#
                .to_string(),
            "await run();",
        ),
        "length = 20000\n"
    );
}

#[test]
fn generated_immutable_borrows_use_cached_projections() {
    assert_eq!(
        generated(
            &r#"fn length(&items: List(i64)): i64 ! {Div} {
    match items { Nil => 0, Cons(head, tail) => 1 + length(&tail) }
}
var items: List(i64) := Nil
var index := 0
while index < 20000 { items := Cons(index, items); index := index + 1 }
let stable_items := items
perform show("length", length(&stable_items))"#
                .to_string(),
            r#"let cached=0;
const project=fieldRef;
fieldRef=(...args)=>{const ref=project(...args);if(stableReferences.get(ref)?.valid())cached++;return ref;};
await run();
if(cached<20000)throw new Error('immutable borrowed traversal did not use its proven stable root');"#,
        ),
        "length = 20000\n"
    );
}

#[test]
fn generated_pure_tail_self_calls_bound_live_scopes() {
    assert_eq!(
        generated_case(
            "backend-tail-self-call/pure-tail-count",
            // The count is written in direct form, which loops; under a budget
            // its continuation form restarts the frame instead.
            r#"let maximum=0,restarts=0,directs=0;
const register=registerScope,enter=enterFunction,run_direct=direct;
registerScope=scope=>{const result=register(scope);maximum=Math.max(maximum,result.open.size);return result;};
enterFunction=(...args)=>{if(args[9]===true)restarts++;return enter(...args);};
direct=(...args)=>{directs++;return run_direct(...args);};
await run();
if((restarts<60000&&directs===0)||maximum>100)throw new Error('pure tail calls retained their previous frames: '+JSON.stringify({restarts,directs,maximum}));"#,
        ),
        "count = 60000\n"
    );
}

#[test]
fn generated_walks_over_options_generics_and_text_run_in_direct_form() {
    assert_eq!(
        generated_case(
            "backend-direct-data/direct-generic-option-text-walk",
            r#"let entered=0;const enter=enterFunction;
enterFunction=(...args)=>{entered++;return enter(...args);};
await run();
if(entered>20)throw new Error('the walk ran in continuation form: '+entered+' frames');"#,
        ),
        "bytes = 2000\n"
    );
}

#[test]
fn generated_word_bits_run_in_direct_form() {
    assert_eq!(
        generated_case(
            "backend-direct-data/direct-word-bits",
            r#"let entered=0;const enter=enterFunction;
enterFunction=(...args)=>{entered++;return enter(...args);};
await run();
if(entered>20)throw new Error('the bits ran in continuation form: '+entered+' frames');"#,
        ),
        "mix = 18446744072294971391\n"
    );
}

#[test]
fn generated_vectors_change_in_place_in_direct_form() {
    assert_eq!(
        generated_case(
            "backend-direct-vectors/direct-vectors-in-place",
            r#"let entered=0;const enter=enterFunction;
enterFunction=(...args)=>{entered++;return enter(...args);};
await run();
if(entered>1)throw new Error('the vectors ran in continuation form: '+entered+' frames');"#,
        ),
        "sum = 258\nn = 9007199254740995\nold = 3\nnew = 2\nwords = \"tea and tea\"\npopped = 9\ntrimmed = 1\nfirst = 14\ncleared = 0\nbytes = 253\nrows = 9\n"
    );
}

#[test]
fn generated_restart_in_continuation_form_undoes_direct_changes() {
    assert_eq!(
        generated_case(
            "backend-direct-vectors/direct-changes-undone-on-restart",
            r#"let undone=0;const back=undo;
undo=log=>{if(log.length)undone++;return back(log);};
await run();
if(undone<2)throw new Error('the direct form did not start again with changes to undo: '+undone);"#,
        ),
        "depth = 30000\nlen = 30001\nfirst = 30005\ncount = 30000\nc = 30003\nchurn = 30000\nw = 1\nw0 = 1\n"
    );
}

#[test]
fn generated_integers_past_the_safe_range_run_in_direct_form() {
    assert_eq!(
        generated_case(
            "backend-direct-data/direct-integer-range",
            r#"let entered=0;const enter=enterFunction;
enterFunction=(...args)=>{entered++;return enter(...args);};
await run();
if(entered>5)throw new Error('the integers ran in continuation form: '+entered+' frames');"#,
        ),
        "grow40 = 18236498188585393201\nshrink = 23\nsigned = -3001\nsigned2 = -2999\ni64min = -9223372036854775808\nnegsafe = -9007199254740991\nnat = 1000000000000000000000000000000\nclassify = 20\nclassify0 = 10\nsame = true\nopt = 9223372036854775809\nshifts = 2147483649\n"
    );
}

#[test]
fn generated_non_tail_recursion_keeps_its_return_work() {
    assert_eq!(
        generated_case(
            "backend-tail-self-call/pure-non-tail-count",
            r#"let restarts=0;const enter=enterFunction;
enterFunction=(...args)=>{if(args[9]===true)restarts++;return enter(...args);};
await run();if(restarts!==0)throw new Error('non-tail recursive result was discarded');"#,
        ),
        "count = 32\n"
    );
}

#[test]
fn tail_self_restart_preserves_ownership_order_and_unknown_fallback() {
    runtime(
        r#"async function test(value,optimized,n){
    let maximum=0;const order=[];
    const body=(c,k)=>{
        maximum=Math.max(maximum,c.scope.open.size);
        const n=c.env[1].value;
        if(n===0n)return readLocal(2,false,false,true)(c,k);
        return tailSelfCall(pure(f),[
            mapValue(pure(n-1n),v=>{if(n<4n)order.push('n'+n);return v;}),
            mapValue(readLocal(2,false,false,true),v=>{if(n<4n)order.push('v'+n);return v;})
        ])(c,k);
    };
    const f=(c,args,k)=>enterFunction(body,[1,2],{},c,args,k,false,false,[true,true],optimized);
    let input;
    const result=await drive((c,k)=>{input=typeof value==='function'?value():value;return f(c,[n,input],k);},()=>{},{},{steps:0});
    assert.equal(result,input);assert.deepEqual(order,['n3','v3','n2','v2','n1','v1']);
    return maximum;
}
assert(await test(()=>some(4n),true,30000n)<20);
assert(await test(()=>some(4n),false,40n)>80);
let drops=0;
const foreign={fields:[4n],names:['value'],release(){drops++;}};
assert(await test(foreign,true,40n)>80);assert.equal(drops,0);
dropValue(foreign);assert.equal(drops,1);
// Charged calls keep their exact exhaustion behavior on the ordinary path.
const recur=(c,args,k)=>callFunction(pure(recur),[],true)(c,k);
await assert.rejects(drive((c,k)=>recur(c,[],k),()=>{},{},{steps:3}),/step limit ran out/);
"#,
    );
}

#[test]
fn aggregate_copy_is_stack_safe_without_sharing_mutable_copies() {
    runtime(
        r#"// A proven graph is shared by its copies, frozen, and stays proven.
const original=list(Array(20000).fill(7n)),copied=copyValue(original);
assert.equal(copied,original);assert(stableAggregate(copied));forgetStableData();assert(stableAggregate(copied));
assert(Object.isFrozen(copied.fields[1].fields[1]));assert.throws(()=>{copied.fields[0]=8n;});
// A write copies only the path to the change.
let root=copied;const slot=reference(()=>root,x=>{root=x;});
projectionRef(slot,{parent:{parent:null,key:1},key:0}).set(9n);
assert.equal(root.fields[1].fields[0],9n);assert.equal(original.fields[1].fields[0],7n);
assert.notEqual(root,original);assert.equal(root.fields[1].fields[1],original.fields[1].fields[1]);
// A host gets graphs it may change, one copy per occurrence.
const given=thaw(pair(original,original));assert.notEqual(given.fields[0],given.fields[1]);
let a=original,b=given.fields[0];
for(let i=0;i<20000;i++){assert.notEqual(a,b);assert(!Object.isFrozen(b));a=a.fields[1];b=b.fields[1];}
given.fields[0].fields[0]=8n;assert.equal(original.fields[0],7n);
// Mutable graphs are still copied per occurrence.
const open={owner:'Box',tag:'Box',names:[null],fields:[{owner:'Box',tag:'Box',names:[null],fields:[1n]}]};
const aliases=copyValue(pair(open,open));assert.notEqual(aliases.fields[0],aliases.fields[1]);
assert.notEqual(aliases.fields[0].fields[0],aliases.fields[1].fields[0]);
const unknown={fields:[4n],names:['value']};assert(!stableAggregate(copyValue(unknown)));
let owners=1;const resource={retain(){owners++;},release(){owners--;}};
const duplicates=copyValue([resource,resource]);assert.equal(owners,3);
dropValue(duplicates);assert.equal(owners,1);
const events=[],sparse=[];sparse.length=4;
sparse[0]={copy(){events.push('copy');sparse[2]=9n;return 8n;}};
Object.defineProperty(sparse,1,{get(){events.push('get');return 7n;},enumerable:true});
const mapped=copyValue(sparse);assert.deepEqual(events,['copy','get']);
assert.deepEqual(mapped,[8n,7n,9n,,]);assert(!Object.hasOwn(mapped,3));
const object={a:{copy(){events.push('child');return 1n;}},get b(){events.push('entries');return 2n;}};
events.length=0;assert.deepEqual(copyValue(object),{a:1n,b:2n});assert.deepEqual(events,['entries','child']);
const poison=Object.fromEntries([['__proto__',some(1n)]]),safe=copyValue(poison);
assert(Object.hasOwn(safe,'__proto__'));assert.equal(Object.getPrototypeOf(safe),Object.prototype);
const cyclic={};cyclic.next=cyclic;assert.throws(()=>copyValue(cyclic),/cyclic/);
class CustomArray extends Array {}
const custom=[some(1n)];custom.constructor={[Symbol.species]:CustomArray};
const customCopy=copyValue(custom);assert(customCopy instanceof CustomArray);assert.notEqual(customCopy[0],custom[0]);
custom[0]=custom;assert.throws(()=>copyValue(custom),/cyclic/);
const map=Array.prototype.map;let overridden=0;
try{Array.prototype.map=function(callback){overridden++;return map.call(this,callback);};assert.deepEqual(copyValue([1n]),[1n]);assert.equal(overridden,1);}
finally{Array.prototype.map=map;}
"#,
    );
}

#[test]
fn immutable_projection_work_is_linear_and_mutable_aliases_stay_live() {
    runtime(
        r#"const count=20000,value=list(Array(count).fill(0n));
let reads=0;
for(let node=value;node.tag==='Cons';){const fields=node.fields;Object.defineProperty(node,'fields',{get(){reads++;return fields;}});node=fields[1];}
const slot={value,immutable:true,shared:false},env={1:slot};
let cursor=placeRef({env},1,[],false);reads=0;
for(let i=0;i<count;i++){cursor=fieldRef(cursor,1);assert(stableReferences.get(cursor)?.valid());assert(cursor.get());}
assert.equal(cursor.get().tag,'Nil');assert.equal(reads,count);
const changing={value:pair(1n,2n),immutable:true,shared:false},context={env:{1:changing}};
const first=fieldRef(placeRef(context,1,[],false),'fst');
assert.equal(first.get(),1n);
placeRef(context,1,['fst'],false).set(3n);
assert.equal(first.get(),3n);assert(!stableReferences.get(first).valid());
changing.value=pair(4n,5n);assert.equal(first.get(),4n);
const mutable={value:pair(6n,7n),immutable:false,shared:false};
const mutableField=fieldRef(placeRef({env:{1:mutable}},1,[],false),'fst');
assert(!stableReferences.has(mutableField));mutable.value=pair(8n,9n);assert.equal(mutableField.get(),8n);
const holder=pair(some(none()),0n),changingGraph={value:holder,immutable:false,shared:false};
assert(stableAggregate(holder));
placeRef({env:{1:changingGraph}},1,['fst',0],false).set(some({ref:true,get:()=>9n,set(){}}));
assert(!stableAggregate(holder));assert(!stableAggregate(holder.fields[0]));
const moved={value:holder,immutable:true,shared:false};
assert(!stableReferences.has(placeRef({env:{1:moved}},1,[],false)));
"#,
    );
}

#[test]
fn stable_provenance_is_private_and_does_not_cross_host_boundaries() {
    runtime(
        r#"const raw={owner:'Pair',tag:'Pair',names:['fst','snd'],fields:[1n,2n],struct:true,stable:true};
const foreign=placeRef({env:{1:{value:raw,immutable:true,shared:false}}},1,[],false);
assert(!stableReferences.has(foreign));
let nativeValue=pair(3n,4n);
const native={ref:true,get:()=>nativeValue,set:value=>{nativeValue=value;},project(){throw new Error('not used');}};
const nativeBorrow=placeRef({env:{1:{value:native,immutable:true,shared:false}}},1,[],true);
assert(!stableReferences.has(nativeBorrow));
const original=pair(pair(5n,6n),7n),slot={value:original,immutable:true,shared:false};
const root=placeRef({env:{1:slot}},1,[],false),leaf=fieldRef(fieldRef(root,'fst'),'fst');
assert.equal(leaf.get(),5n);assert(stableReferences.get(leaf).valid());
await drive(external('mutate',[pure(root)]),()=>{},{mutate:borrow=>{borrow.get().fields[0]=pair(8n,9n);return null;}});
assert(!stableReferences.get(leaf).valid());assert.equal(leaf.get(),8n);
assert(!stableReferences.has(placeRef({env:{1:slot}},1,[],false)));
const callback=(c,args,k)=>more(()=>k(c,pair(10n,11n)));
const answer=await drive(external('callback',[pure(callback)]),()=>{},{callback:f=>f()});
assert(!stableAggregate(answer));
"#,
    );
}

#[test]
fn stable_provenance_is_revoked_by_driver_and_io_handoffs() {
    runtime(
        r#"const before=pair(1n,2n);
await drive((c,k)=>{assert(!stableAggregate(before));return k(c,null);},()=>{});
await drive((c,k)=>builtin('Vec::into_array',[pure({kind:'Vec',items:[]})])(c,(d,value)=>{assert(!stableAggregate(value));return k(d,null);}),()=>{});
await drive((c,k)=>builtin('Array::of_list',[pure(list([1n]))])(c,(d,value)=>{assert(!stableAggregate(value));return k(d,null);}),()=>{});
let original,leaf;
function create(){
    original=pair(pair(1n,2n),3n);
    const root=placeRef({env:{1:{value:original,immutable:true,shared:false}}},1,[],false);
    leaf=fieldRef(fieldRef(root,'fst'),'fst');assert(stableReferences.get(leaf).valid());
}
function mutate(){original.fields[0]=pair(7n,8n);}
function check(){assert(!stableReferences.get(leaf).valid());assert.equal(leaf.get(),7n);}
await drive((c,k)=>{create();return route(c,'show','direct',['x',0n],k);},mutate);check();
for(const name of ['print','eprint','read_file','write_file']){
    await drive((c,k)=>{create();return builtin('Os::'+name,[pure('x'),pure('y')])(c,k);},()=>{},{},{['os_'+name]:()=>{mutate();return 'ok';}});check();
    await drive((c,k)=>{create();return builtin('Os::'+name,[pure('x'),pure('y')])(c,k);},()=>{},{},{['os_'+name]:()=>{mutate();throw new Error('host');}}).catch(()=>{});check();
}
for(const reject of [false,true]){
    await drive((c,k)=>{create();return builtin('Os::read_file',[pure('x')])(c,k);},()=>{},{},{os_read_file:async()=>{await Promise.resolve();mutate();if(reject)throw new Error('host');return 'ok';}});check();
}
await drive((c,k)=>{create();return Promise.resolve().then(()=>{mutate();return more(()=>k(c,null));});},()=>{});check();
const callback=(c,args,k)=>{create();return Promise.resolve().then(()=>{mutate();return more(()=>{check();return k(c,null);});});};
await drive(external('invoke',[pure(callback)]),()=>{},{invoke:async callback=>await callback()});check();
const returned=await drive((c,k)=>k(c,pair(9n,10n)),()=>{});assert(!stableAggregate(returned));
await drive((c,k)=>{create();throw new Error('driver');},()=>{}).catch(()=>{});
assert(!stableAggregate(original));assert(!stableReferences.get(leaf).valid());
"#,
    );
}

#[test]
fn stable_factories_and_copies_do_not_trust_custom_intrinsics() {
    runtime(
        r#"const descriptor=Object.getOwnPropertyDescriptor(Array.prototype,'map'),native=descriptor.value;
let captured,mutating=false;
try{
    Array.prototype.map=function(callback,...rest){
        const result=native.call(this,callback,...rest);
        if(result.length===2&&result[0]===1n&&result[1]===2n)captured=result;
        if(mutating&&captured)captured[0]=9n;
        return result;
    };
    const original=pair(pair(1n,2n),3n);
    const root=placeRef({env:{1:{value:original,immutable:true,shared:false}}},1,[],false);
    const leaf=fieldRef(fieldRef(root,'fst'),'fst');assert.equal(leaf.get(),1n);
    assert(!stableAggregate(original));
    mutating=true;pair(4n,5n);assert.equal(leaf.get(),9n);
}finally{Object.defineProperty(Array.prototype,'map',descriptor);}
const original=pair(pair(1n,2n),3n);
const root=placeRef({env:{1:{value:original,immutable:true,shared:false}}},1,[],false);
const leaf=fieldRef(fieldRef(root,'fst'),'fst');assert(stableReferences.get(leaf).valid());
try{
    Object.defineProperty(Array.prototype,'map',{configurable:true,get(){if(this===original.fields)this[0]=pair(8n,9n);return native;}});
    const copied=copyValue(original);assert(!stableAggregate(copied));
    assert(!stableReferences.get(leaf).valid());assert.equal(leaf.get(),8n);
}finally{Object.defineProperty(Array.prototype,'map',descriptor);}
assert(!stableAggregate(copyValue(original)));
for(const [object,key] of [[Array.prototype,'map'],[Array.prototype,'constructor'],[Array,Symbol.species]]){
    const saved=Object.getOwnPropertyDescriptor(object,key);let reads=0;
    try{
        Object.defineProperty(object,key,{configurable:true,get(){reads++;Object.defineProperty(object,key,saved);return Object.hasOwn(saved,'value')?saved.value:saved.get.call(this);}});
        const value=pair(4n,5n);assert.equal(reads,1);assert(!stableAggregate(value));
    }finally{Object.defineProperty(object,key,saved);}
}
const guarded=pair(pair(5n,6n),7n),guardRoot=placeRef({env:{1:{value:guarded,immutable:true,shared:false}}},1,[],false);
const guardLeaf=fieldRef(fieldRef(guardRoot,'fst'),'fst');let getterCalls=0;
try{
    Object.defineProperty(Object.prototype,'ref',{configurable:true,get(){getterCalls++;delete Object.prototype.ref;guarded.fields[0].fields[0]=11n;return false;}});
    assert.equal(guardLeaf.get(),5n);assert.equal(getterCalls,0);assert(!stableReferences.get(guardLeaf).valid());
    void guarded.ref;assert.equal(guardLeaf.get(),11n);
}finally{delete Object.prototype.ref;}
const every=Object.getOwnPropertyDescriptor(Array.prototype,'every');let released=0;
try{
    Array.prototype.every=()=>true;
    const resource={release(){released++;}};
    assert(!allStableMembers([resource]));assert(!stableAggregate(pair(resource,null)));
    const result=await drive((c,k)=>enterFunction((d,target)=>target(d,!!d.restart),[1],{},c,[resource],k,false,false,[true],true),()=>{});
    assert.equal(result,false);assert.equal(released,1);
}finally{Object.defineProperty(Array.prototype,'every',every);}
"#,
    );
}

#[test]
fn stable_temporary_projection_export_keeps_its_real_owner() {
    runtime(
        r#"const original=pair(pair(7n,8n),9n);let drops=0;
const drop=dropValue;
dropValue=value=>{if(value===original)drops++;return drop(value);};
const root=temporaryRef(original,true),borrow=borrowedRef(root);
const child=fieldRef(borrow,'fst'),leaf=fieldRef(child,'fst');
assert(stableReferences.get(leaf)?.valid());
const result=exportBorrow(some(leaf));
root.release();assert.equal(drops,0);assert.equal(result.fields[0].get(),7n);
dropValue(result);assert.equal(drops,1);assert.equal(root.get(),undefined);
assert(!stableReferences.get(leaf).valid());
"#,
    );
}

#[test]
fn generated_deep_aggregate_drop_after_output() {
    assert_eq!(
        generated(
            &r#"var items: List(i64) := Nil
var index := 0
while index < 6000 { items := Cons(index, items); index := index + 1 }
perform show("built", index)"#
                .to_string(),
            "await run(); console.log('closed');",
        ),
        "built = 6000\nclosed\n"
    );
}

#[test]
fn projections_read_and_write_current_root_once_at_arbitrary_depth() {
    runtime(
        r#"let value=list(Array(20000).fill(0n)),reads=0,writes=0;
const root=reference(()=>{reads++;return value;},v=>{writes++;value=v;});
const projected=placeRef({env:{1:{value:root}}},1,Array(20000).fill(1),true);
assert.equal(projected.get().tag,'Nil');
assert.equal(reads,1);
projected.set(construct('End',[],[],[],false,'List'));
assert.equal(reads,2);assert.equal(writes,1);
assert.equal(projected.get().tag,'End');
let tail=root;
for(let i=0;i<20000;i++){
    const bindings={};
    assert(matchPattern(['ctor','Cons',[['wild'],['bind',1,true]],'List'],tail,bindings));
    tail=bindings[1].value;
}
assert.equal(tail.get().tag,'End');
const make=n=>construct('Outer',['child'],[construct('Inner',['value'],[n],[0],true,'Inner')],[0],true,'Outer');
let stored=make(1n),copies=0,sets=0;
const copying=reference(()=>{copies++;return copyValue(stored);},v=>{sets++;stored=v;});
const child=placeRef({env:{1:{value:copying}}},1,['child','value'],true);
const alias=fieldRef(fieldRef(copying,'child'),'value');
stored=make(2n);
assert.equal(child.get(),2n);assert.equal(copies,1);
child.set(3n);assert.equal(copies,2);assert.equal(sets,1);
assert.equal(stored.fields[0].fields[0],3n);assert.equal(alias.get(),3n);
"#,
    );
}

#[test]
fn aggregate_drop_preserves_reverse_order_and_each_owner() {
    runtime(
        r#"const log=[],leaf=name=>({release:()=>log.push(name)});
let deep=leaf('deep');
for(let i=0;i<20000;i++)deep=i%4===0?[deep]:i%4===1?{fields:[deep]}:i%4===2?{items:[deep]}:{union:0,value:deep};
dropValue(deep);assert.deepEqual(log,['deep']);log.length=0;
dropValue({fields:[leaf('a'),{items:[leaf('b'),{union:0,value:leaf('c')}]}]});
assert.deepEqual(log,['c','b','a']);
const changing=[leaf('old'),{release(){log.push('last');changing[0]=leaf('replacement');}}];
dropValue(changing);assert.deepEqual(log,['c','b','a','last','replacement']);log.length=3;
let owners=2,releases=0,finalized=0;
const resource={release(){releases++;if(--owners===0)finalized++;}};
dropValue([resource,resource]);assert.equal(releases,2);assert.equal(finalized,1);
dropValue([{ref:true,fields:[leaf('ref')]},{shared:true,items:[leaf('shared')]}]);
assert.deepEqual(log,['c','b','a']);
"#,
    );
}

#[test]
fn generated_nested_temporary_borrow_matches_named_and_evaluator() {
    let source = &r#"copy struct Record { value: i64 }
fn make_record(): Record { Record { value: 7 } }
fn read_record(&record: Record): i64 { record.value }
fn inspect_record(&record: Record): i64 {
    let first := read_record(&record);
    first + record.value
}
perform show("temporary", inspect_record(&make_record()))
let saved := make_record()
perform show("named", inspect_record(&saved))"#
        .to_string();
    let program = tauto::surface::parse_program(source).unwrap();
    let reference = tauto::eval::run_program_with(
        &program,
        1_000_000,
        tauto::eval::RunOptions {
            check_ownership: true,
            ..Default::default()
        },
    )
    .unwrap();
    let expected = reference
        .outputs
        .iter()
        .map(|(name, value)| format!("{name} = {value}\n"))
        .collect::<String>();
    assert_eq!(expected, "temporary = 14\nnamed = 14\n");
    assert_eq!(generated(source, "await run();"), expected);
}

fn borrowed_probe_source() -> &'static str {
    r#"affine struct Probe { value: i64 }
extern {
    fn make(): Probe
    fn wait(): Unit
}
fn read_probe(&probe: Probe): i64 { probe.value }
fn inspect_probe(&probe: Probe): i64 {
    let first := read_probe(&probe);
    wait();
    first + probe.value
}
perform show("temporary", inspect_probe(&make()))"#
}

#[test]
fn generated_temporary_survives_async_reborrow_and_releases_once() {
    assert_eq!(
        generated(
            borrowed_probe_source(),
            r#"let releases=0;
const make=()=>({owner:'Probe',tag:'Probe',names:['value'],fields:[7n],release(){releases++;}});
await run(console.log,{make,wait:async()=>{if(releases!==0)throw new Error('released before await');await Promise.resolve();if(releases!==0)throw new Error('released during await');return null;}});
if(releases!==1)throw new Error('temporary was not released once');"#,
        ),
        "temporary = 14\n"
    );
}

#[test]
fn generated_temporary_releases_on_throw_and_rejected_promise() {
    generated(
        borrowed_probe_source(),
        r#"for(const asynchronous of [false,true]){
    let releases=0;
    const failure=new Error('host failure');
    const make=()=>({owner:'Probe',tag:'Probe',names:['value'],fields:[7n],release(){releases++;}});
    const wait=()=>{if(releases!==0)throw new Error('premature release');if(asynchronous)return Promise.reject(failure);throw failure;};
    try{await run(()=>{throw new Error('unexpected output');},{make,wait});throw new Error('expected rejection');}
    catch(error){if(error!==failure)throw error;}
    if(releases!==1)throw new Error('rejected temporary was not released once');
}"#,
    );
}

#[test]
fn generated_temporary_survives_multi_shot_resumptions() {
    assert_eq!(
        generated(
            &r#"copy struct Record { value: i64 }
effect choose(): Bool resume ω
fn make_record(): Record { Record { value: 7 } }
fn read_record(&record: Record): i64 { record.value }
fn inspect_record(&record: Record): i64 ! {choose} {
    let first := read_record(&record);
    if perform choose() { first + record.value } else { record.value }
}
let result := handle { inspect_record(&make_record()) } with { choose(), k => k(true) + k(false) }
perform show("result", result)"#
                .to_string(),
            "await run();",
        ),
        "result = 21\n"
    );
}

#[test]
fn temporary_owners_and_scope_registry_close_exactly_once() {
    runtime(
        r#"let releases=0;
const value=temporaryRef({release(){releases++;}});
value.retain();const copy=copyValue(value),borrow=borrowedRef(value);
assert.equal(borrow.retain,undefined);assert.equal(borrow.release,undefined);
value.release();copy.release();assert.equal(releases,0);value.release();assert.equal(releases,1);
for(const fail of [false,true]){
    let registry,drops=0;
    const start=(c,k)=>{registry=c.scope.open;const inner=openScope(c.scope);own(inner,{value:{release(){drops++;}},shared:false});if(fail)throw new Error('stop');closeScope(inner);return k(c,null);};
    try{await drive(start,()=>{},{});assert.equal(fail,false);}catch(error){assert.equal(error.message,'stop');assert.equal(fail,true);}
    assert.equal(drops,1);assert.equal(registry.size,0);
}
"#,
    );
}

#[test]
fn generated_returned_projection_keeps_its_temporary_root() {
    assert_eq!(
        generated(
            &r#"copy struct Inner { value: i64 }
copy struct Holder { child: Inner }
fn get_child(&holder: Holder): &Inner { &holder.child }
fn read_child(&inner: Inner): i64 { inner.value }
perform show("child", read_child(get_child(&Holder { child: Inner { value: 7 } })))"#
                .to_string(),
            "await run();",
        ),
        "child = 7\n"
    );
    runtime(
        r#"let drops=0;
const root=temporaryRef({fields:[{fields:[7n],names:['value']}],names:['child'],release(){drops++;}});
const child=exportBorrow(fieldRef(borrowedRef(root),'child'));
root.release();assert.equal(drops,0);assert.equal(child.get().fields[0],7n);
const leaf=exportBorrow(fieldRef(borrowedRef(child),'value'));
child.release();assert.equal(drops,0);assert.equal(leaf.get(),7n);
leaf.release();assert.equal(drops,1);
"#,
    );
}

#[test]
fn generic_return_export_is_stack_safe_and_retains_only_escaping_views() {
    runtime(
        r#"let plain=list(Array(20000).fill(7n));
let reads=0;const fields=plain.fields;
Object.defineProperty(plain,'fields',{get(){reads++;return fields;}});
assert.equal(exportBorrow(plain),plain);assert.equal(reads,0);
// The same shape from a host boundary has no trusted provenance and must
// still take the conservative traversal.
forgetStableData();assert.equal(exportBorrow(plain),plain);assert(reads>0);
let drops=0;
const root=temporaryRef({fields:[9n],names:['value'],release(){drops++;}});
let nested=pair(plain,some(fieldRef(borrowedRef(root),'value')));
for(let i=0;i<20000;i++)nested=some(nested);
const exported=exportBorrow(nested);
root.release();assert.equal(drops,0);
let leaf=exported;
for(let i=0;i<20000;i++)leaf=leaf.fields[0];
assert.equal(leaf.fields[0],plain);
assert.equal(leaf.fields[1].fields[0].get(),9n);
dropValue(exported);assert.equal(drops,1);
"#,
    );
}

#[test]
fn single_shot_scope_transfer_does_not_duplicate_shared_owners() {
    runtime(
        r#"const root=openScope(null),original=openScope(root);let drops=0;
const slot=own(original,{id:1,value:{release(){drops++;}},shared:true,owners:2});
const snapshot=captureContext({scope:original,env:{1:slot}},root,false);
const resumed=resumeContext(snapshot,root,false);
// The frames move to the new caller, so their owners are not doubled.
assert.equal(resumed.scope,original);assert(root.open.has(original));
closeScope(resumed.scope);assert.equal(slot.owners,1);assert.equal(drops,0);
for(const scope of [...root.open].reverse())closeScope(scope);
assert.equal(slot.owners,1);assert.equal(drops,0);
if(--slot.owners===0)dropValue(slot.value);
assert.equal(drops,1);assert.equal(root.open.size,0);
"#,
    );
}

#[test]
fn retained_continuation_owns_its_snapshot_after_driver_exit() {
    runtime(
        r#"for(const fail of [false,true]){
    let saved,registry,drops=0,resourceOwners=1;
    const body=(c,k)=>{
        registry=c.scope.open;
        const scope=openScope(c.scope),slot=own(scope,{id:1,value:{retain(){resourceOwners++;},release(){if(--resourceOwners===0)drops++;}},shared:false});
        return performValue('pause','many',[])({...c,scope,env:{...c.env,1:slot}},(d,v)=>more(()=>k(d,v)));
    };
    const arm={op:'pause',pats:[],k:2,guard:pure(true),body:(c,k)=>{
        saved=copyValue(c.env[2].value);
        if(fail)throw new Error('handler failed');
        return k(c,0n);
    }};
    const rejected={...arm,guard:pure(false),body:()=>{throw new Error('rejected arm ran');}};
    try{await drive(handleValue(body,[rejected,arm],null),()=>{},{});assert(!fail);}catch(error){assert.equal(error.message,'handler failed');assert(fail);}
    assert.equal(drops,0);assert(registry.size>0);
    assert.equal(await drive((c,k)=>saved(c,[4n],k),()=>{},{}),4n);
    assert.equal(drops,0);assert.equal(resourceOwners,1);
    saved.release();assert.equal(drops,1);assert.equal(registry.size,0);
}
"#,
    );
}

#[test]
fn generated_temporary_releases_when_direct_host_call_refuses_suspension() {
    let source = borrowed_probe_source().replace(
        r#"perform show("temporary", inspect_probe(&make()))"#,
        r#"effect ask(): i64 direct
let result := handle { perform ask() } with { ask(), k => k(inspect_probe(&make())) }
perform show("result", result)"#,
    );
    generated(
        &source,
        r#"let releases=0;
const make=()=>({owner:'Probe',tag:'Probe',names:['value'],fields:[7n],release(){releases++;}});
try{await run(()=>{throw new Error('unexpected output');},{make,wait:async()=>null});throw new Error('expected refusal');}
catch(error){if(!error.message.includes('direct handler cannot await'))throw error;}
if(releases!==1)throw new Error('refused temporary was not released once');"#,
    );
}

#[test]
fn exceptional_handler_exit_invalidates_host_borrows_and_callbacks() {
    runtime(
        r#"let savedBorrow,savedCallback,releases=0;
const failure=new Error('handler failed');
const callback=(c,args,k)=>enterFunction(performValue('ask','one',[]),[],{},c,args,k);
const resource=temporaryRef({fields:[7n],names:['value'],release(){releases++;}});
const body=external('host',[pure(resource),pure(callback)]);
const arm={op:'ask',pats:[],k:1,guard:pure(true),body:()=>{throw failure;}};
try{
    await drive(handleValue(body,[arm],null),()=>{},{host:async(borrow,callback)=>{savedBorrow=borrow;savedCallback=callback;return await callback();}});
    assert.fail('expected handler failure');
}catch(error){assert.equal(error,failure);}
assert.equal(releases,1);
assert.throws(()=>savedBorrow.get(),/borrow outlived its call/);
assert.throws(()=>savedCallback(),/callback outlived its call/);
"#,
    );
}

/// The inputs these tests read, copied from the shared case files.
#[allow(dead_code)]
mod case_inputs {
    pub fn fixture_static(file: &str, name: &str) -> &'static str {
        match (file, name) {
            ("backend-closure-ownership-fixtures.eure", "lambda-body-exception") => {
                r#"affine struct Probe {}
extern { fn make(): Probe
  fn fail(): i64 }
let captured := make()
let consume: affine () -> Probe := () => { fail(); captured }
let result := consume()
"#
            }
            ("backend-closure-ownership-fixtures.eure", "lambda-argument-exception") => {
                r#"affine struct Probe {}
extern { fn make(): Probe
  fn fail(): i64 }
let captured := make()
let consume: affine (i64) -> Probe := (marker) => captured
let result := consume(fail())
"#
            }
            _ => panic!("no copied input {file}/{name}"),
        }
    }
    /// The program of a shared case, by `file/case`.
    pub fn source(name: &str) -> &'static str {
        match name {
            "backend-capture-bindings/borrowed-recursive-capture" => {
                r####"fn pure_helper(): Unit { #() }
fn plain(n: i64, &previous: () -> i64): i64 ! {Div} {
  var x := n
  if n == 0 { previous() } else { plain(n - 1, () => x) }
}
fn with_helper(n: i64, &previous: () -> i64): i64 ! {Div} {
  var x := n
  if n == 0 { previous() } else { with_helper(n - 1, () => { pure_helper(); x }) }
}
perform show("plain", plain(1, () => 99))
perform show("with_helper", with_helper(1, () => 99))
"####
            }
            "backend-capture-bindings/resumed-boundary-capture" => {
                r####"effect pause(): Unit resume ω
fn pure_helper(): Unit { #() }
fn resumed_plain(n: i64, &previous: () -> i64): i64 ! {Div} {
  let x := n
  if n == 0 { previous() } else {
    handle { perform pause(); x } with {
      pause(), k => resumed_plain(n - 1, () => k(#()))
    }
  }
}
fn resumed_with_helper(n: i64, &previous: () -> i64): i64 ! {Div} {
  let x := n
  if n == 0 { previous() } else {
    handle { perform pause(); pure_helper(); x } with {
      pause(), k => resumed_with_helper(n - 1, () => k(#()))
    }
  }
}
perform show("resumed_plain", resumed_plain(1, () => 99))
perform show("resumed_with_helper", resumed_with_helper(1, () => 99))
"####
            }
            "backend-capture-bindings/resumed-operation-arm-capture" => {
                r####"effect pause(): Unit resume ω
effect read(): i64 resume 1
fn pure_helper(): Unit { #() }
fn resumed_arm(n: i64, &previous: () -> i64): i64 ! {Div} {
  let x := n
  if n == 0 { previous() } else {
    handle { perform pause(); perform read() } with {
      pause(), k => resumed_arm(n - 1, () => k(#()))
      read(), k => { pure_helper(); k(x) }
    }
  }
}
perform show("arm", resumed_arm(1, () => 99))
"####
            }
            "backend-capture-bindings/resumed-return-arm-capture" => {
                r####"effect pause(): Unit resume ω
fn pure_helper(): Unit { #() }
fn resumed_return(n: i64, &previous: () -> i64): i64 ! {Div} {
  let x := n
  if n == 0 { previous() } else {
    handle { perform pause(); 7 } with {
      pause(), k => resumed_return(n - 1, () => k(#()))
      return value => { pure_helper(); x }
    }
  }
}
perform show("return", resumed_return(1, () => 99))
"####
            }
            "backend-closure-ownership/copy-captures-remain-readable" => {
                r####"copy struct Stamp { value: i64 }
let original := Stamp { value: 17 }
let read := () => original.value
perform show("first", read())
perform show("original", original.value)
perform show("second", read())
"####
            }
            "backend-closure-ownership/shared-capture-last-use-remains-repeatable" => {
                r####"fn make_read(): () -> Text {
  let text := "kept"
  () => text
}
let read := make_read()
perform show("first", read())
perform show("second", read())
"####
            }
            "backend-closure-ownership/nested-affine-capture" => {
                r####"affine struct Token { value: i64 }
let original := Token { value: 23 }
let outer: affine () -> affine () -> Token := () => () => original
let inner := outer()
let result := inner()
perform show("nested", match result { Token { value } => value })
"####
            }
            "backend-closure-ownership/linear-capture-is-consumed" => {
                r####"linear struct Token { value: i64 }
let original := Token { value: 31 }
let consume: linear () -> Token := () => original
let result := consume()
perform show("linear", match result { Token { value } => value })
"####
            }
            "backend-closure-ownership/borrowed-capture-is-not-consumed" => {
                r####"fn twice(&read: () -> i64): i64 { read() + read() }
var value := 7
perform show("before", twice(() => value))
value := 9
perform show("after", twice(() => value))
perform show("original", value)
"####
            }
            "backend-direct-data/direct-generic-option-text-walk" => {
                r####"fn spaces(t: Text, i: u64, found: List(Option(u64))): List(Option(u64)) ! {Div} {
    match Text::byte(t, i) {
        None => found,
        Some(b) => spaces(t, i + 1, Cons(if b == 32 { Some(i) } else { None }, found))
    }
}
fn count<A>(&l: List(A)): i64 ! {Div} {
    match l { Nil => 0, Cons(h, rest) => 1 + count(&rest) }
}
var t := ""
var n := 0
while n < 500 { t := concat(t, "a b "); n := n + 1 }
let found := spaces(t, 0, Nil)
// A generic function runs in direct form under a caller that is in it.
fn total(&l: List(Option(u64))): i64 ! {Div} { count(&l) }
perform show("bytes", total(&found))"####
            }
            "backend-direct-data/direct-word-bits" => {
                r####"fn mix(n: u64): u64 ! {Div} {
    var a: u32 := 2166136261
    var b: u64 := 1469598103934665603
    var i: u64 := 0
    while i < n {
        let w := U32::of_u64(U64::and(b, 4294967295))
        a := U32::xor(U32::rotl(a, 5), U32::or(U32::and(w, 65535), U32::shl(a, 3)))
        a := U32::rotr(U32::xor(a, U32::shr(a, 7)), 11)
        b := U64::xor(U64::rotl(b, 13), U64::of_u32(a))
        b := U64::or(U64::and(b, U64::shl(b, 1)), U64::shr(U64::rotr(b, 17), 3))
        i := i + 1
    }
    U64::xor(b, U64::of_u32(a))
}
perform show("mix", mix(300))"####
            }
            "backend-direct-data/direct-integer-range" => {
                r####"fn grow(n: u64): u64 ! {Div} {
    var x: u64 := 1
    var i: u64 := 0
    while i < n { x := x * 3 + 1; i := i + 1 }
    x
}
fn shrink(x: u64): u64 ! {Div} {
    var y := x
    var k: u64 := 0
    while y > 1 { y := div(y, 7); k := k + 1 }
    k
}
fn signed(a: i64, b: i64): i64 ! {Div} {
    div(a, b) * 1000 + mod(a, b)
}
fn big_i64(n: u64): i64 ! {Div} {
    var x: i64 := -1
    var i: u64 := 0
    while i < n { x := x * 2; i := i + 1 }
    x
}
fn neg(a: i64): i64 { 0 - a }
fn nat_pow(n: nat): nat ! {Div} {
    var x: nat := 1
    var i: nat := 0
    while i < n { x := x * 10; i := i + 1 }
    x
}
fn classify(n: u64): u64 { match n { 0 => 10, 9007199254740993 => 20, other => 30 } }
fn same(a: u64, b: u64): Bool { a == b }
fn wrap(n: u64): Option(u64) ! {Div} { Some(n * 2) }
fn unwrap(o: Option(u64)): u64 ! {Div} { match o { None => 0, Some(v) => v + 1 } }
fn shifts(a: u32): u32 { U32::xor(U32::shl(a, 31), U32::shr(a, 33)) }
perform show("grow40", grow(40))
perform show("shrink", shrink(grow(40)))
perform show("signed", signed(0 - 7, 2))
perform show("signed2", signed(7, 0 - 2))
perform show("i64min", big_i64(63))
perform show("negsafe", neg(9007199254740991))
perform show("nat", nat_pow(30))
perform show("classify", classify(9007199254740992 + 1))
perform show("classify0", classify(0))
perform show("same", same(9007199254740992 + 1, 9007199254740993))
perform show("opt", unwrap(wrap(4611686018427387904)))
perform show("shifts", shifts(3))"####
            }
            "backend-direct-vectors/direct-vectors-in-place" => {
                r####"struct Canvas { w: u64, h: u64 }

fn blend(dst: u32, src: u32): u32 { U32::or(dst, src) }

// A pixel through a cell: read, then written back.
fn put(&mut px: Vec(u32), i: u64, src: u32): Unit {
  let old := match Vec::get(&px, i) {
    Some(x) => x
    None => 0
  }
  match Vec::get_mut(&mut px, i) {
    Some(at) => {
      at := blend(old, src)
    }
    None => #()
  }
}

fn fill(&mut px: Vec(u32), cv: Canvas, src: u32): Unit ! {Div} {
  var y: u64 := 0
  while y < cv.h {
    var x: u64 := 0
    while x < cv.w {
      put(&mut px, y * cv.w + x, src)
      x := x + 1
    }
    y := y + 1
  }
}

fn sum(&px: Vec(u32)): u64 ! {Div} {
  var s: u64 := 0
  var i: u64 := 0
  while i < Vec::len(&px) {
    s := s + match Vec::get(&px, i) { Some(x) => U64::of_u32(x), None => 0 }
    i := i + 1
  }
  s
}

fn bump(&mut n: u64, r#by: u64): Unit { n := n + r#by }

fn swap_in(&mut v: Vec(u64)): Vec(u64) ! {Div} {
  var w: Vec(u64) := Vec::new()
  Vec::push(&mut w, 7)
  Vec::push(&mut w, 8)
  replace(&mut v, w)
}

fn words(&t: Text): Text ! {Div} {
  var b := Buf::new()
  Buf::push(&mut b, t)
  let sp := " and "
  Buf::push(&mut b, &sp)
  Buf::push(&mut b, t)
  Text::of(b)
}

fn trim(&mut v: Vec(u64)): u64 ! {Div} {
  let popped := match Vec::pop(&mut v) { Some(x) => x, None => 0 }
  Vec::truncate(&mut v, 1)
  popped
}

fn last_twice(&mut v: Vec(u64)): Unit {
  match Vec::last_mut(&mut v) { Some(at) => { at := at * 2 }, None => #() }
}

fn bytes_sum(b: Bytes): u64 ! {Div} {
  var s: u64 := 0
  var i: u64 := 0
  while i < Bytes::len(b) {
    s := s + match Bytes::get(b, i) { Some(x) => U64::of_u8(x), None => 0 }
    i := i + 1
  }
  s
}

fn rows(&cv: Canvas): u64 { cv.h }

var px: Vec(u32) := Vec::new()
var i: u64 := 0
while i < 12 { Vec::push(&mut px, U32::of_u64(i)); i := i + 1 }
fill(&mut px, Canvas { w: 4, h: 3 }, 16)
perform show("sum", sum(&px))
var n: u64 := 5
bump(&mut n, 9007199254740990)
perform show("n", n)
var v: Vec(u64) := Vec::new()
Vec::push(&mut v, 1)
Vec::push(&mut v, 2)
Vec::push(&mut v, 3)
let old := swap_in(&mut v)
perform show("old", Vec::len(&old))
perform show("new", Vec::len(&v))
perform show("words", words("tea"))
Vec::push(&mut v, 9)
perform show("popped", trim(&mut v))
last_twice(&mut v)
perform show("trimmed", Vec::len(&v))
perform show("first", match Vec::get(&v, 0) { Some(x) => x, None => 0 })
var e: Vec(u64) := Vec::new()
Vec::push(&mut e, 4)
Vec::clear(&mut e)
perform show("cleared", Vec::len(&e))
perform show("bytes", bytes_sum(Bytes::of_list([1, 2, 250])))
let cv := Canvas { w: 2, h: 9 }
perform show("rows", rows(&cv))"####
            }
            "backend-direct-vectors/direct-changes-undone-on-restart" => {
                r####"fn fill(&mut v: Vec(u64), n: u64): u64 ! {Div} {
  if n == 0 {
    0
  } else {
    Vec::push(&mut v, n)
    match Vec::get_mut(&mut v, 0) { Some(at) => { at := at + 1 }, None => #() }
    1 + fill(&mut v, n - 1)
  }
}

fn count(&mut c: u64, n: u64): u64 ! {Div} {
  if n == 0 { 0 } else { c := c + 1; 1 + count(&mut c, n - 1) }
}

fn churn(&mut v: Vec(u64), n: u64): u64 ! {Div} {
  if n == 0 {
    0
  } else {
    Vec::clear(&mut v)
    Vec::push(&mut v, n)
    Vec::push(&mut v, n)
    Vec::truncate(&mut v, 1)
    1 + churn(&mut v, n - 1)
  }
}

var v: Vec(u64) := Vec::new()
Vec::push(&mut v, 5)
perform show("depth", fill(&mut v, 30000))
perform show("len", Vec::len(&v))
perform show("first", match Vec::get(&v, 0) { Some(x) => x, None => 0 })
var c: u64 := 3
perform show("count", count(&mut c, 30000))
perform show("c", c)
var w: Vec(u64) := Vec::new()
Vec::push(&mut w, 1)
Vec::push(&mut w, 2)
perform show("churn", churn(&mut w, 30000))
perform show("w", Vec::len(&w))
perform show("w0", match Vec::get(&w, 0) { Some(x) => x, None => 0 })"####
            }
            "backend-tail-self-call/pure-tail-count" => {
                r####"fn count(n: Nat, done: Nat): Nat {
    match n: Nat { Zero => done, Succ(rest) => count(rest, done + 1) }
}
perform show("count", count(60000, 0))"####
            }
            "backend-tail-self-call/pure-non-tail-count" => {
                r####"fn count(n: Nat): Nat {
    match n: Nat { Zero => 0, Succ(rest) => 1 + count(rest) }
}
perform show("count", count(32))"####
            }
            _ => panic!("no copied input {name}"),
        }
    }
    #[allow(dead_code)]
    pub fn fixture(file: &str, name: &str) -> String {
        fixture_static(file, name).to_string()
    }
}
