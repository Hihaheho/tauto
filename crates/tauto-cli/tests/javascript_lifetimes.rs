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
    let package = tauto::nir::compile(source).unwrap();
    let module = tauto_jsgen::generate(&package).unwrap();
    execute(&format!("{module}\n{host}"))
}

fn generated_case(name: &str, host: &str) -> String {
    let source = case_inputs::source(name);
    // The tail-call programs keep the checked extraction evidence (a tote that
    // imports the program) instead of treating proof source as an ordinary
    // runtime function, which would charge divergent-call fuel.
    let package = if name.starts_with("backend-tail-self-call/") {
        compile_extracted(&source)
    } else {
        tauto::nir::compile_javascript(&source).unwrap()
    };
    let module = tauto_jsgen::generate(&package).unwrap();
    execute(&format!("{module}\n{host}"))
}

/// The program, importing `std/base.taut`, loaded through a tote as a build reads it.
fn compile_extracted(source: &str) -> tauto_nir::Package {
    let dir = std::env::temp_dir().join(format!(
        "tauto-js-extracted-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(dir.join("src")).unwrap();
    let base = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../std/base.taut")
        .canonicalize()
        .unwrap();
    let import_base = format!("import {:?}\n", base.to_string_lossy());
    // The program is the tote's own entry: the statements an imported file's
    // top level runs are not run, and these print.
    // A tote's top level performs nothing but its `main`, so the printing
    // statements go in the body of that `main`.
    let (declarations, statements): (Vec<_>, Vec<_>) =
        source.lines().partition(|line| !line.starts_with("show("));
    fs::write(
        dir.join("src/main.taut"),
        format!(
            "{}\n{import_base}perform main(() => {{ {} }})\n",
            declarations.join("\n"),
            statements.join("\n")
        ),
    )
    .unwrap();
    fs::write(
        dir.join("Tauto.eure"),
        "package { name = \"case\"\nversion = \"0.1.0\" }",
    )
    .unwrap();
    let loaded = tauto::program::load_tote_for_build(&dir).unwrap();
    let package = tauto_nibcheck::lower::compile_loaded_with_observer(
        &loaded,
        false,
        tauto_nir::Target::JavaScript,
        |_| {},
    )
    .unwrap();
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
fn generated_owned_callee_and_capture_release_when_host_throws() {
    for name in ["lambda-argument-exception", "lambda-body-exception"] {
        generated(
            &case_inputs::fixture("backend-closure-ownership-fixtures.eure", name),
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
    defineLocal(4,false,closureValue((c,k)=>{envGet(c.env,3).value++;return k(c,envGet(c.env,3).value);},[],[3],true)),
    callFunction(readLocal(4,false,true),[],false),callFunction(readLocal(4,false,true),[],false),
    (c,k)=>{assert.equal(envGet(c.env,3).value,2n);assert.equal(drops,0);return k(c,null);}
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
    const resume=envGet(c.env,3).value;
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
        (c,k)=>{saved=copyValue(envGet(c.env,2).value);return k(c,null);}
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
const scope=openAliasScope(caller,envOf([[1,outer],[7,outer]]));
let restored=restoreEnv(envOf([[1,outer],[7,outer]]),scope);
assert.equal(envGet(restored,1),outer);assert.equal(envGet(restored,7),outer);
const parameter=own(scope,{id:1,value:30n,shared:false});
restored=restoreEnv(envOf([[1,outer],[7,outer]]),scope);
assert.equal(envGet(restored,1),parameter);assert.equal(envGet(restored,7),outer);
outer.value.marker=45n;
assert.equal(envGet(restored,7).value.marker,45n);
closeScope(scope);assert.equal(drops,0);assert.equal(outer.owners,1);
// Unannotated runtime scopes keep their ordinary nearest-slot lookup.
assert.equal(envGet(restoreEnv(envOf([[1,outer]]),caller),1),shadow);
const foreign={value:45n,shared:false},foreignScope=openAliasScope(caller,envOf([[8,foreign]]));
assert.equal(envGet(restoreEnv(envOf([[8,foreign]]),foreignScope),8),foreign);
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
const inner=openAliasScope(outer,envOf([[7,local],[8,outside],[9,shared]]));
const env=envOf([[2,local],[7,local],[8,outside],[9,shared]]);
const snapshot=captureContext({scope:inner,env},root,true,envOf([[10,outside]]));
assert.equal(owners,1);
const first=resumeContext(snapshot,root,true);
const second=resumeContext(snapshot,first.scope,true);
assert.equal(owners,3);
assert.notEqual(envGet(first.env,2),local);assert.notEqual(envGet(second.env,2),envGet(first.env,2));
for(const resumed of [first,second]){
    const restored=restoreEnv(envOf([...envEntries(env),[10,outside]]),resumed.scope);
    assert.equal(envGet(restored,2),envGet(resumed.env,2));assert.equal(envGet(restored,7),envGet(resumed.env,2));
    assert.equal(envGet(restored,8),outside);assert.equal(envGet(restored,9),shared);
    assert.equal(envGet(restored,10),outside);
}
// A callback from the first resumption is not rebound to its nearer sibling.
const callback=openAliasScope(second.scope,envOf([[7,envGet(first.env,2)]]));
assert.equal(envGet(restoreEnv(envOf([[7,envGet(first.env,2)]]),callback),7),envGet(first.env,2));
const nested=captureContext({scope:callback,env:envOf([[7,envGet(first.env,2)]])},second.scope,false);
const transferred=resumeContext(nested,second.scope,false);
// A single-shot resumption moves its frames instead of copying them.
assert.equal(transferred.scope,callback);
assert.equal(envGet(restoreEnv(envOf([[7,envGet(first.env,2)]]),transferred.scope),7),envGet(first.env,2));
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
    const snapshot=captureContext({scope:source,env:envOf([[1,lexical]])},root,clone,envOf([[1,lexical]]));
    // A clone leaves the original alone; a single-shot snapshot moves it.
    assert.equal(scopeAliases.has(source),!clone);
    const resumed=resumeContext(snapshot,caller,clone);
    assert.equal(envGet(restoreEnv(envOf([[1,lexical]]),resumed.scope),1),lexical);
    const empty=captureContext({scope:root,env:envOf([[1,lexical]])},root,clone,envOf([[1,lexical]]));
    assert.equal(empty.frames.length,0);
    const emptyResume=resumeContext(empty,caller,clone);
    assert.equal(emptyResume.scope,caller);
    assert.equal(envGet(restoreEnv(envOf([[1,lexical]]),emptyResume.scope),1),dynamic);
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
        if(quant==='one'||quant==='many')return envGet(c.env,2).value(c,[7n],k);
        return k(c,7n);
    }};
    const start=(c,k)=>{
        registry=c.scope.open;
        const slot=own(c.scope,{id:1,value:{release(){rootDrops++;}},shared:false});
        return handleValue(performValue('ask',quant,[]),[rejected,accepted],null)({...c,env:envOf([[1,slot]])},k);
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
        return handleValue(body,[arm],ret)({...c,env:envOf([[1,slot]])},k);
    };
    await assert.rejects(drive(start,()=>{},{}),error=>error===failure);
    assert.equal(localDrops,1,phase);assert.equal(rootDrops,1,phase);
    assert.equal(registry.size,0,phase);
}
"#,
    );
}

#[test]
fn generated_immutable_borrows_use_cached_projections() {
    assert_eq!(
        generated(
            &r#"fn length(items: &List(i64)): i64 ! {div, overflow} {
    match items { Nil => 0, Cons(head, tail) => 1 + length(&tail) }
}
var items: List(i64) := Nil
var index := 0
while index < 20000 { items := Cons(index, items); index := index + 1 }
let stable_items := items
show(&length(&stable_items))"#
                .to_string(),
            r#"let cached=0;
const project=fieldRef;
fieldRef=(...args)=>{const ref=project(...args);if(stableReferences.get(ref)?.valid())cached++;return ref;};
await run(undefined,{},{os_print:s=>process.stdout.write(s)});
if(cached<20000)throw new Error('immutable borrowed traversal did not use its proven stable root');"#,
        ),
        "20000\n"
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
await run(undefined,{},{os_print:s=>process.stdout.write(s)});
if((restarts<60000&&directs===0)||maximum>100)throw new Error('pure tail calls retained their previous frames: '+JSON.stringify({restarts,directs,maximum}));"#,
        ),
        "60000\n"
    );
}

#[test]
fn generated_walks_over_options_generics_and_text_run_in_direct_form() {
    assert_eq!(
        generated_case(
            "backend-direct-data/direct-generic-option-text-walk",
            r#"let entered=0;const enter=enterFunction;
enterFunction=(...args)=>{entered++;return enter(...args);};
await run(undefined,{},{os_print:s=>process.stdout.write(s)});
if(entered>20)throw new Error('the walk ran in continuation form: '+entered+' frames');"#,
        ),
        "2000\n"
    );
}

#[test]
fn generated_word_bits_run_in_direct_form() {
    assert_eq!(
        generated_case(
            "backend-direct-data/direct-word-bits",
            r#"let entered=0;const enter=enterFunction;
enterFunction=(...args)=>{entered++;return enter(...args);};
await run(undefined,{},{os_print:s=>process.stdout.write(s)});
if(entered>20)throw new Error('the bits ran in continuation form: '+entered+' frames');"#,
        ),
        "18446744072294971391\n"
    );
}

#[test]
fn generated_vectors_change_in_place_in_direct_form() {
    assert_eq!(
        generated_case(
            "backend-direct-vectors/direct-vectors-in-place",
            r#"let entered=0;const enter=enterFunction;
enterFunction=(...args)=>{entered++;return enter(...args);};
await run(undefined,{},{os_print:s=>process.stdout.write(s)});
// Each `show` enters two frames of its own: 11 shows, and the program's.
if(entered>2*11+6)throw new Error('the vectors ran in continuation form: '+entered+' frames');"#,
        ),
        "258\n9007199254740995\n3\n2\n\"tea and tea\"\n9\n1\n14\n0\n253\n9\n"
    );
}

#[test]
fn generated_restart_in_continuation_form_undoes_direct_changes() {
    assert_eq!(
        generated_case(
            "backend-direct-vectors/direct-changes-undone-on-restart",
            r#"let undone=0;const back=undo;
undo=log=>{if(log.length)undone++;return back(log);};
await run(undefined,{},{os_print:s=>process.stdout.write(s)});
if(undone<2)throw new Error('the direct form did not start again with changes to undo: '+undone);"#,
        ),
        "30000\n30001\n30005\n30000\n30003\n30000\n1\n1\n"
    );
}

#[test]
fn generated_integers_past_the_safe_range_run_in_direct_form() {
    assert_eq!(
        generated_case(
            "backend-direct-data/direct-integer-range",
            r#"let entered=0;const enter=enterFunction;
enterFunction=(...args)=>{entered++;return enter(...args);};
await run(undefined,{},{os_print:s=>process.stdout.write(s)});
// Each `show` enters two frames of its own: 12 shows, and the program's.
if(entered>2*12+8)throw new Error('the integers ran in continuation form: '+entered+' frames');"#,
        ),
        "18236498188585393201\n23\n-3001\n-2999\n-9223372036854775808\n-9007199254740991\n1000000000000000000000000000000\n20\n10\ntrue\n9223372036854775809\n2147483649\n"
    );
}

#[test]
fn generated_non_tail_recursion_keeps_its_return_work() {
    assert_eq!(
        generated_case(
            "backend-tail-self-call/pure-non-tail-count",
            r#"let restarts=0;const enter=enterFunction;
enterFunction=(...args)=>{if(args[9]===true)restarts++;return enter(...args);};
await run(undefined,{},{os_print:s=>process.stdout.write(s)});if(restarts!==0)throw new Error('non-tail recursive result was discarded');"#,
        ),
        "32\n"
    );
}

#[test]
fn tail_self_restart_preserves_ownership_order_and_unknown_fallback() {
    runtime(
        r#"async function test(value,optimized,n){
    let maximum=0;const order=[];
    const body=(c,k)=>{
        maximum=Math.max(maximum,c.scope.open.size);
        const n=envGet(c.env,1).value;
        if(n===0n)return readLocal(2,false,false,true)(c,k);
        return tailSelfCall(pure(f),[
            mapValue(pure(n-1n),v=>{if(n<4n)order.push('n'+n);return v;}),
            mapValue(readLocal(2,false,false,true),v=>{if(n<4n)order.push('v'+n);return v;})
        ])(c,k);
    };
    const f=(c,args,k)=>enterFunction(body,[1,2],null,c,args,k,false,false,[true,true],optimized);
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
fn retained_aggregate_spines_own_callbacks_once_and_copy_only_written_paths() {
    runtime(
        r#"let owners=1,releases=0;
const callback=retainedLeaf(Object.assign(()=>0,{retain(){owners++;},release(){assert(owners>0);owners--;releases++;}}));
const cons=(head,tail)=>construct('Cons',[null,null],[head,tail],[0,1],false,'List',true);
let value=construct('Nil',[],[],[],false,'List',true);
for(let i=0;i<20000;i++)value=cons(i===0?callback:copyValue(callback),value);
assert.equal(owners,20000);
const alias=copyValue(value);assert.equal(alias,value);assert.equal(owners,20000);
const hostCopy=thaw(copyValue(value));assert.equal(owners,40000);assert(!Object.isFrozen(hostCopy));
dropValue(hostCopy);assert.equal(owners,20000);releases=0;
forgetStableData();assert.equal(copyValue(value),value);dropValue(value);
let root=value;
projectionRef(reference(()=>root,x=>{root=x;}),{parent:{parent:null,key:1},key:0}).set(7n);
assert.equal(root.fields[1].fields[0],7n);assert.equal(alias.fields[1].fields[0],callback);
assert.equal(root.fields[1].fields[1],alias.fields[1].fields[1]);
dropValue(root);assert.equal(releases,1);dropValue(alias);assert.equal(owners,0);assert.equal(releases,20001);
// Crossing the host boundary transfers an owner to independent mutable nodes.
owners=1;releases=0;
const source=cons(callback,construct('Nil',[],[],[],false,'List',true)),held=copyValue(source);
const host=thaw(source);assert.notEqual(host,held);assert(!Object.isFrozen(host));assert.equal(owners,2);
dropValue(held);assert.equal(owners,1);dropValue(host);assert.equal(owners,0);
// A host borrowing a nested node owns a copy, not its parent's live edge.
owners=1;releases=0;
const child=cons(callback,construct('Nil',[],[],[],false,'List',true));
let parent=construct('Box',[null],[child],[0],true,'Box',true);
const parentAlias=copyValue(parent),nested=projectionRef(reference(()=>parent,x=>{parent=x;}),{parent:null,key:0});
thawReference(nested);assert.notEqual(parent,parentAlias);assert.equal(owners,2);assert.equal(releases,0);
assert(!Object.isFrozen(nested.get()));assert.equal(parentAlias.fields[0],child);
dropValue(parent);assert.equal(owners,1);dropValue(parentAlias);assert.equal(owners,0);
// A mutable ancestor owns the retained edge replaced by a field write.
owners=1;releases=0;
const selected=cons(callback,construct('Nil',[],[],[],false,'List',true)),selectedAlias=copyValue(selected);
let mutable={fields:[selected],names:[null]};
projectionRef(reference(()=>mutable,x=>{mutable=x;}),{parent:{parent:null,key:0},key:0}).set(3n);
assert.equal(owners,1);dropValue(mutable);assert.equal(owners,1);dropValue(selectedAlias);assert.equal(owners,0);
// Internal path copies do not dispatch through a host-replaced array map.
owners=1;releases=0;
let guarded=cons(callback,construct('Nil',[],[],[],false,'List',true));
const guardedAlias=copyValue(guarded),arrayMap=Array.prototype.map;
try{
    Array.prototype.map=()=>{throw new Error('host map must not own internal fields');};
    projectionRef(reference(()=>guarded,x=>{guarded=x;}),{parent:null,key:0}).set(5n);
}finally{Array.prototype.map=arrayMap;}
assert.equal(guarded.fields[0],5n);dropValue(guarded);assert.equal(owners,1);dropValue(guardedAlias);assert.equal(owners,0);
// A type hint alone cannot certify unknown values or custom copy hooks.
owners=1;
const unknown={fields:[callback],names:[null]};
const fallback=cons(unknown,construct('Nil',[],[],[],false,'List',true));
assert(!retainedGraphs.has(fallback));
const copied=copyValue(fallback);assert.notEqual(copied,fallback);assert.notEqual(copied.fields[0],unknown);
dropValue(fallback);dropValue(copied);assert.equal(owners,0);
const order=[],leaf=n=>retainedLeaf({retain(){},release(){order.push(n);}});
const ordered=construct('Pair',[null,null],[leaf(1),leaf(2)],[0,1],true,'Pair',true);
copyValue(ordered);dropValue(ordered);assert.deepEqual(order,[]);
dropValue(ordered);assert.deepEqual(order,[2,1]);
// Every resumption owns its root; only the last root releases the leaf.
owners=1;releases=0;
const graph=cons(callback,construct('Nil',[],[],[],false,'List',true));
const body=sequence([defineLocal(1,false,pure(graph)),performValue('pause','many',[]),readLocal(1,false,true)]);
const arm={op:'pause',pats:[],k:2,guard:pure(true),body:(c,k)=>{
    const resume=envGet(c.env,2).value;
    return resume(c,[null],(d,first)=>{assert.equal(first,graph);dropValue(first);
        return resume(d,[null],(e,second)=>{assert.equal(second,graph);dropValue(second);assert.equal(releases,0);return k(e,null);});});
}};
await drive(handleValue(body,[arm],null),()=>{},{});
assert.equal(owners,0);assert.equal(releases,1);
"#,
    );
}

#[test]
fn owned_borrow_captures_survive_their_original_slots() {
    runtime(
        r#"let value=17n,saved;
await drive(sequence([
    defineLocal(1,false,pure(reference(()=>value,x=>{value=x;}))),
    // Keep the closure outside the call that created its borrowed capture.
    (c,k)=>closureValue(readLocal(1,true,true),[],[1],false,[],false,[],[],false,[1])(c,(d,f)=>{saved=f;return k(d,null);})
]),()=>{},{});
value=99n;
for(let i=0;i<2;i++)assert.equal(await drive(callFunction(pure(copyValue(saved)),[],false),()=>{},{}),17n);
dropValue(saved);
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
const slot={value,immutable:true,shared:false},env=envOf([[1,slot]]);
let cursor=placeRef({env},1,[],false);reads=0;
for(let i=0;i<count;i++){cursor=fieldRef(cursor,1);assert(stableReferences.get(cursor)?.valid());assert(cursor.get());}
assert.equal(cursor.get().tag,'Nil');assert.equal(reads,count);
const changing={value:pair(1n,2n),immutable:true,shared:false},context={env:envOf([[1,changing]])};
const first=fieldRef(placeRef(context,1,[],false),'fst');
assert.equal(first.get(),1n);
placeRef(context,1,['fst'],false).set(3n);
assert.equal(first.get(),3n);assert(!stableReferences.get(first).valid());
changing.value=pair(4n,5n);assert.equal(first.get(),4n);
const mutable={value:pair(6n,7n),immutable:false,shared:false};
const mutableField=fieldRef(placeRef({env:envOf([[1,mutable]])},1,[],false),'fst');
assert(!stableReferences.has(mutableField));mutable.value=pair(8n,9n);assert.equal(mutableField.get(),8n);
const holder=pair(some(none()),0n),changingGraph={value:holder,immutable:false,shared:false};
assert(stableAggregate(holder));
placeRef({env:envOf([[1,changingGraph]])},1,['fst',0],false).set(some({ref:true,get:()=>9n,set(){}}));
assert(!stableAggregate(holder));assert(!stableAggregate(holder.fields[0]));
const moved={value:holder,immutable:true,shared:false};
assert(!stableReferences.has(placeRef({env:envOf([[1,moved]])},1,[],false)));
"#,
    );
}

#[test]
fn stable_provenance_is_private_and_does_not_cross_host_boundaries() {
    runtime(
        r#"const raw={owner:'Pair',tag:'Pair',names:['fst','snd'],fields:[1n,2n],struct:true,stable:true};
const foreign=placeRef({env:envOf([[1,{value:raw,immutable:true,shared:false}]])},1,[],false);
assert(!stableReferences.has(foreign));
let nativeValue=pair(3n,4n);
const native={ref:true,get:()=>nativeValue,set:value=>{nativeValue=value;},project(){throw new Error('not used');}};
const nativeBorrow=placeRef({env:envOf([[1,{value:native,immutable:true,shared:false}]])},1,[],true);
assert(!stableReferences.has(nativeBorrow));
const original=pair(pair(5n,6n),7n),slot={value:original,immutable:true,shared:false};
const root=placeRef({env:envOf([[1,slot]])},1,[],false),leaf=fieldRef(fieldRef(root,'fst'),'fst');
assert.equal(leaf.get(),5n);assert(stableReferences.get(leaf).valid());
await drive(external('mutate',[pure(root)]),()=>{},{mutate:borrow=>{borrow.get().fields[0]=pair(8n,9n);return null;}});
assert(!stableReferences.get(leaf).valid());assert.equal(leaf.get(),8n);
assert(!stableReferences.has(placeRef({env:envOf([[1,slot]])},1,[],false)));
const callback=(c,args,k)=>more(()=>k(c,pair(10n,11n)));
const answer=await drive(external('callback',[pure(callback)]),()=>{},{callback:f=>f()});
assert(!stableAggregate(answer));
"#,
    );
}

#[test]
fn stable_provenance_is_revoked_by_driver_and_io_handoffs() {
    runtime(
        r#"// An `Array` the runtime shares is frozen, so its certificate needs no revoking.
const frozenArray=value=>sharedData.has(value)&&Object.isFrozen(value)&&Object.isFrozen(value.items);
const before=pair(1n,2n);
await drive((c,k)=>{assert(!stableAggregate(before));return k(c,null);},()=>{});
await drive((c,k)=>builtin('Vec::into_array',[pure({kind:'Vec',items:[]})])(c,(d,value)=>{assert(!stableAggregate(value)||frozenArray(value));return k(d,null);}),()=>{});
await drive((c,k)=>builtin('Array::of_list',[pure(list([1n]))])(c,(d,value)=>{assert(!stableAggregate(value)||frozenArray(value));return k(d,null);}),()=>{});
let original,leaf;
function create(){
    original=pair(pair(1n,2n),3n);
    const root=placeRef({env:envOf([[1,{value:original,immutable:true,shared:false}]])},1,[],false);
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
    const root=placeRef({env:envOf([[1,{value:original,immutable:true,shared:false}]])},1,[],false);
    const leaf=fieldRef(fieldRef(root,'fst'),'fst');assert.equal(leaf.get(),1n);
    assert(!stableAggregate(original));
    mutating=true;pair(4n,5n);assert.equal(leaf.get(),9n);
}finally{Object.defineProperty(Array.prototype,'map',descriptor);}
const original=pair(pair(1n,2n),3n);
const root=placeRef({env:envOf([[1,{value:original,immutable:true,shared:false}]])},1,[],false);
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
const guarded=pair(pair(5n,6n),7n),guardRoot=placeRef({env:envOf([[1,{value:guarded,immutable:true,shared:false}]])},1,[],false);
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
    const result=await drive((c,k)=>enterFunction((d,target)=>target(d,!!d.restart),[1],null,c,[resource],k,false,false,[true],true),()=>{});
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
fn projections_read_and_write_current_root_once_at_arbitrary_depth() {
    runtime(
        r#"let value=list(Array(20000).fill(0n)),reads=0,writes=0;
const root=reference(()=>{reads++;return value;},v=>{writes++;value=v;});
const projected=placeRef({env:envOf([[1,{value:root}]])},1,Array(20000).fill(1),true);
assert.equal(projected.get().tag,'Nil');
assert.equal(reads,1);
projected.set(construct('End',[],[],[],false,'List'));
assert.equal(reads,2);assert.equal(writes,1);
assert.equal(projected.get().tag,'End');
let tail=root;
for(let i=0;i<20000;i++){
    const bindings=new Map();
    assert(matchPattern(['ctor','Cons',[['wild'],['bind',1,true]],'List'],tail,bindings));
    tail=bindings.get(1).value;
}
assert.equal(tail.get().tag,'End');
const make=n=>construct('Outer',['child'],[construct('Inner',['value'],[n],[0],true,'Inner')],[0],true,'Outer');
let stored=make(1n),copies=0,sets=0;
const copying=reference(()=>{copies++;return copyValue(stored);},v=>{sets++;stored=v;});
const child=placeRef({env:envOf([[1,{value:copying}]])},1,['child','value'],true);
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
            &r#"struct(copy) Inner { value: i64 }
struct(copy) Holder { child: Inner }
fn get_child(holder: &Holder): &Inner { &holder.child }
fn read_child(inner: &Inner): i64 { inner.value }
show(&read_child(get_child(&Holder { child: Inner { value: 7 } })))"#
                .to_string(),
            "await run(undefined,{},{os_print:s=>process.stdout.write(s)});",
        ),
        "7\n"
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
const snapshot=captureContext({scope:original,env:envOf([[1,slot]])},root,false);
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
        return performValue('pause','many',[])({...c,scope,env:envWith(c.env,1,slot)},(d,v)=>more(()=>k(d,v)));
    };
    const arm={op:'pause',pats:[],k:2,guard:pure(true),body:(c,k)=>{
        saved=copyValue(envGet(c.env,2).value);
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
fn exceptional_handler_exit_invalidates_host_borrows_and_callbacks() {
    runtime(
        r#"let savedBorrow,savedCallback,releases=0;
const failure=new Error('handler failed');
const callback=(c,args,k)=>enterFunction(performValue('ask','one',[]),[],null,c,args,k);
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

/// The inputs these tests read, kept as files under `tests/fixtures`.
mod case_inputs {
    fn read(path: &str) -> String {
        let path = format!("{}/tests/fixtures/{path}", env!("CARGO_MANIFEST_DIR"));
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {path}: {e}"))
    }
    pub fn fixture(file: &str, name: &str) -> String {
        read(&format!("{}/{}.taut", file.trim_end_matches(".eure"), name))
    }
    pub fn source(name: &str) -> String {
        read(&format!("source/{name}.taut"))
    }
}
