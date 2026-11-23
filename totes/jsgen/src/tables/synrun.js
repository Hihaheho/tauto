
const synTote=(()=>{// The runtime of the JavaScript backend, written by hand and copied into
// the generated programs. Integers retain their complete declared range.
// An operator whose result does not exist: the operation it performs, with what
// the host says when nothing handles it.
class OpFail extends Error {
    constructor(op, message) { super(message); this.op = op; }
}
function checked(n, min, max) {
    if (n < min || n > max) throw new OpFail('overflow', 'the number is too large');
    return n;
}
// An operator's value in CPS code: a result that does not exist performs
// `overflow` or `divzero` where the operator stands.
function operated(c, k, f) {
    let r;
    try { r = f(); } catch (e) {
        if (e instanceof OpFail) return route(c, e.op, 'zero', [], k);
        throw e;
    }
    return more(() => k(c, r));
}
function divide(op, [a, b], min, max) {
    if (b === 0n) throw new Error('division by zero');
    if (a === min && b === -1n) throw new Error('the number is too large');
    return checked(op === 'div' ? a / b : a % b, min, max);
}
// A direct body holds an integer as a number while it is a safe integer,
// and as a BigInt otherwise; every other place holds a BigInt. Each
// operation below gives what the BigInt one gives: the number path is taken
// only when its result is exact and in range, and the rest falls back.
// `lo` and `hi` are the bounds clamped to the safe integers.
function small(n){return typeof n==='bigint'&&n>=-9007199254740991n&&n<=9007199254740991n?Number(n):n;}
function big(n){return typeof n==='number'?BigInt(n):n;}
function iadd(a,b,lo,hi,min,max){if(typeof a==='number'&&typeof b==='number'){const r=a+b;if(r>=lo&&r<=hi)return r;}return small(checked(big(a)+big(b),min,max));}
function isub(a,b,lo,hi,min,max){if(typeof a==='number'&&typeof b==='number'){const r=a-b;if(r>=lo&&r<=hi)return r;}return small(checked(big(a)-big(b),min,max));}
function imul(a,b,lo,hi,min,max){if(typeof a==='number'&&typeof b==='number'){const r=a*b;if(r>=lo&&r<=hi)return r+0;}return small(checked(big(a)*big(b),min,max));}
function idivide(op,a,b,lo,hi,min,max){
    if(typeof a==='number'&&typeof b==='number'&&b!==0){const r=op==='div'?Math.trunc(a/b):a%b;if(r>=lo&&r<=hi)return r+0;}
    return small(divide(op,[big(a),big(b)],min,max));
}
function field(v,name,index) {if(v?.project){const part=v.project(index??name,false);try{return dereference(part,true);}finally{part.release();}}const obj=unref(v);const i=index??obj.names.indexOf(name);return copyValue(unref(obj.fields[i]));}
// Compares with a stack of its own, not the host's: a long list is a deep
// chain of constructors, and a recursive walk would overflow the host stack.
function equal(a,b) {
    const work=[a,b];
    while(work.length){
        b=unref(work.pop());a=unref(work.pop());
        if(a?.union!==undefined)a=a.value;
        if(b?.union!==undefined)b=b.value;
        requireDataOwner(a);requireDataOwner(b);
        if(a===b)continue;
        if(a?.hostType!==undefined||b?.hostType!==undefined)return false;
        if(!a||!b||typeof a!=='object'||typeof b!=='object')return false;
        if(a.kind!==b.kind||a.tag!==b.tag||a.owner!==b.owner)return false;
        if(a.kind==='Buf'){if(a.text!==b.text)return false;continue;}
        if(a.kind==='Bytes'){if(a.bytes.length!==b.bytes.length||!a.bytes.every((x,i)=>x===b.bytes[i]))return false;continue;}
        const x=Array.isArray(a)?a:a.fields??a.items,y=Array.isArray(b)?b:b.fields??b.items;
        if(!Array.isArray(x)||!Array.isArray(y)||x.length!==y.length)return false;
        for(let i=x.length-1;i>=0;i--)work.push(x[i],y[i]);
    }
    return true;
}
function shown(v) {
    v=unref(v);
    if(v?.union!==undefined)return shown(v.value);
    switch(v?.kind) {
        case 'Shown':return v.text;
        case 'Buf':return 'Buf('+quoteText(v.text)+')';
        case 'Vec':case 'Array':return v.kind+'['+v.items.map(shown).join(', ')+']';
        case 'Ref':return 'Ref('+shown(v.value)+')';
        case 'Atomic':return 'Atomic('+v.value+')';
        case 'Bytes':return 'Bytes['+Array.from(v.bytes).join(', ')+']';
        case 'Mutex':return 'Mutex';
        case 'MutexGuard':return 'MutexGuard';
        case 'Signal':return 'Signal';
        case 'Pending':return 'Pending';
        case 'Secret':return 'Secret';
    }
    if (v === null) return '()';
    if (typeof v === 'symbol') return '<declaration reference>';
    if (typeof v === 'string') return quoteText(v);
    if (typeof v === 'number') return floatText(v);
    if (typeof v !== 'object') return String(v);
    // A constructor is shown by the name written, not by its full name `m::C`:
    // the compiler, which knows the modules, writes that name in `shownNames`.
    const tag = shownNames.get(v.tag) ?? v.tag;
    // `#(a, b, c)`: the `Pair`s nested to the right, as the value was written.
    if (v.struct && tag === 'Pair' && v.fields.length === 2) {
        const items = [shown(v.fields[0])];
        let rest = v.fields[1];
        while (rest && rest.fields && rest.struct && (shownNames.get(rest.tag) ?? rest.tag) === 'Pair' && rest.fields.length === 2) {
            items.push(shown(rest.fields[0]));
            rest = rest.fields[1];
        }
        items.push(shown(rest));
        return '#(' + items.join(', ') + ')';
    }
    if ((v.struct || v.fields.length > 0) && v.names.every(n => n !== null)) return tag + ' {' + (v.fields.length ? ' ' + v.fields.map((x,i) => v.names[i] + ': ' + shown(x)).join(', ') + ' ' : '') + '}';
    return tag + (v.fields.length ? '(' + v.fields.map(shown).join(', ') + ')' : '');
}
// Only generated, resource-free value graphs qualify for cached projections.
// Provenance is private and is discarded whenever control crosses the host ABI.
// A set of objects, as a `WeakSet` is, that stays fast with millions of
// members (the cells of a long `List`): a member carries a private field of
// this set's own class, which no other code can read, write or forge. An
// object that cannot take the field is kept in a `WeakSet` instead.
function marks(){
    class Base{constructor(o){return o;}}
    class Mark extends Base{
        #in;
        constructor(o){super(o);this.#in=true;}
        static has(o){return #in in o&&o.#in;}
        // Whether `o` is now a member: false when `o` cannot take the field.
        static put(o,x){
            if(#in in o){o.#in=x;return true;}
            if(!x)return true;
            try{new Mark(o);return true;}catch{return false;}
        }
    }
    const rest=new WeakSet();
    const object=o=>o!==null&&(typeof o==='object'||typeof o==='function');
    return {
        has:o=>object(o)&&(Mark.has(o)||rest.has(o)),
        add(o){
            if(!object(o))throw new TypeError('Invalid value used in weak set');
            if(!Mark.has(o)&&!rest.has(o)&&!Mark.put(o,true))rest.add(o);
            return this;
        },
        delete:o=>{
            if(!object(o))return false;
            if(rest.delete(o))return true;
            if(!Mark.has(o))return false;
            Mark.put(o,false);return true;
        },
    };
}
let stableData=marks(),stableEpoch={};
const stableReferences=new WeakMap(),stableSlots=new WeakMap();
const provenanceArray=Array,provenanceArrayPrototype=Array.prototype,provenanceObjectPrototype=Object.prototype;
const provenanceDescriptor=Object.getOwnPropertyDescriptor,provenancePrototype=Object.getPrototypeOf;
const provenanceOwn=Object.hasOwn,provenanceIsArray=Array.isArray;
const provenanceArrayMethods=['map','every','push','pop','indexOf',Symbol.iterator].map(key=>[key,provenanceDescriptor(provenanceArrayPrototype,key).value]);
const provenanceSpecies=provenanceDescriptor(provenanceArray,Symbol.species);
function ordinaryArrayMethods(value){return ordinaryArrayValue(value)&&ordinaryArrayGlobals();}
// Both arrays are ordinary; the shared prototypes are checked once.
function ordinaryArrayPair(a,b){return ordinaryArrayValue(a)&&ordinaryArrayValue(b)&&ordinaryArrayGlobals();}
function ordinaryArrayValue(value){
    if(!provenanceIsArray(value)||provenancePrototype(value)!==provenanceArrayPrototype
        ||provenanceDescriptor(value,'constructor')!==undefined)return false;
    const ownMap=provenanceDescriptor(value,'map');
    return ownMap===undefined||ownMap.value===provenanceArrayMethods[0][1];
}
function ordinaryArrayGlobals(){
    if(Array!==provenanceArray
        ||provenancePrototype(provenanceArrayPrototype)!==provenanceObjectPrototype
        ||provenancePrototype(provenanceObjectPrototype)!==null)return false;
    for(let i=0;i<provenanceArrayMethods.length;i++){
        const key=provenanceArrayMethods[i][0],method=provenanceArrayMethods[i][1];
        if(provenanceDescriptor(provenanceArrayPrototype,key)?.value!==method)return false;
    }
    const constructor=provenanceDescriptor(provenanceArrayPrototype,'constructor');
    const species=provenanceDescriptor(provenanceArray,Symbol.species);
    return constructor?.value===provenanceArray&&species?.get===provenanceSpecies.get
        &&species?.set===provenanceSpecies.set&&!provenanceOwn(species,'value');
}
function constructorArray(value){
    if(!ordinaryArrayMethods(value))return false;
    for(let i=0;i<value.length;i++){
        const item=provenanceDescriptor(value,`${i}`);
        if(!item||!provenanceOwn(item,'value'))return false;
    }
    return true;
}
function stableMember(value){
    if(value===null)return true;
    switch(typeof value){
        case 'string':case 'number':case 'bigint':case 'boolean':case 'undefined':return true;
        default:return stableAggregate(value);
    }
}
function allStableMembers(values){
    for(let i=0;i<values.length;i++)if(!stableMember(values[i]))return false;
    return true;
}
function aggregateHooks(value){
    return 'ref' in value||'resource' in value||'shared' in value||'retain' in value
        ||'release' in value||'copy' in value||'project' in value||'operation' in value;
}
function stableAggregate(value){
    if(sharedData.has(value))return true;
    if(value===null||typeof value!=='object'||!stableData.has(value))return false;
    // These keys are absent from generated plain data. Do not invoke a host
    // getter while deciding whether an existing certificate is still usable.
    if(aggregateHooks(value)){
        forgetStableData();return false;
    }
    return true;
}
const retainedGraphs=new WeakMap(),retainedLeaves=new WeakSet();
function retainedLeaf(value){retainedLeaves.add(value);return value;}
function retainedMember(value){return stableMember(value)||retainedGraphs.has(value)||retainedLeaves.has(value);}
function generatedAggregate(value,fields,retainable=false){
    if(aggregateHooks(value)){forgetStableData();return value;}
    if(allStableMembers(fields)){
        if(retainable)share(value);
        else stableData.add(value);
    }
    else if(retainable&&fields.every(retainedMember)){
        // The node owns each field once. Copies own the node, so retaining a
        // callback list does not visit its spine or its captures.
        for(const field of fields)if(stableAggregate(field))share(field);
        sharedFreeze(value.names);sharedFreeze(fields);sharedFreeze(value);
        retainedGraphs.set(value,{owners:1});
    }
    return value;
}
function forgetStableData(){stableData=marks();stableEpoch={};}
// A copy of a proven graph shares it instead of copying it, as persistent
// data does on the other backends; otherwise every copy of a tree costs its
// whole size. A shared graph is frozen, so this certificate is never
// revoked: nobody can change it, a write in Tauto copies the path to the
// change, and a host gets a fresh copy (`thaw`).
const sharedData=marks(),sharedFreeze=Object.freeze;
function share(value){
    const pending=[value];
    while(pending.length){
        const v=pending.pop();
        if(v===null||typeof v!=='object'||sharedData.has(v))continue;
        if(v.kind==='Array'&&provenanceIsArray(v.items)){
            sharedFreeze(v.items);sharedFreeze(v);sharedData.add(v);
            for(let i=0;i<v.items.length;i++)pending.push(v.items[i]);
            continue;
        }
        if(!v.fields)continue;
        sharedFreeze(v.names);sharedFreeze(v.fields);sharedFreeze(v);sharedData.add(v);
        for(let i=0;i<v.fields.length;i++)pending.push(v.fields[i]);
    }
    return value;
}
// An `Array` cannot change after it is made, so one whose items need no copy,
// are shared, or are proven graphs (which are shared with it, as a copy would
// share them) is shared as a proven graph is: a copy of it is itself, not a
// walk over every item.
function shareArray(array){
    const items=array.items;
    for(let i=0;i<items.length;i++){
        const x=items[i];
        if(x!==null&&typeof x==='object'&&!sharedData.has(x)
            &&!(stableAggregate(x)&&ordinaryArrayValue(x.fields)))return array;
    }
    if(!ordinaryArrayGlobals())return array;
    for(let i=0;i<items.length;i++){const x=items[i];if(x!==null&&typeof x==='object')share(x);}
    sharedFreeze(items);sharedFreeze(array);sharedData.add(array);
    return array;
}
// Gives the host a value it may change: shared parts are copied, once per
// occurrence like any copy, and other parts are kept.
function thaw(value){
    if(retainedGraphs.has(value)){
        // Transfer this owner to a mutable host graph. Each field copy owns
        // its callbacks/handles independently of the persistent source.
        const top={...value,fields:[]},pending=[[value,top]];
        while(pending.length){
            const [source,target]=pending.pop();
            for(let i=0;i<source.fields.length;i++){
                const field=source.fields[i];
                if(retainedGraphs.has(field)){
                    const child={...field,fields:[]};target.fields[i]=child;pending.push([field,child]);
                }else target.fields[i]=thaw(copyValue(field));
            }
        }
        dropValue(value);return top;
    }
    // A shared `Array` (`shareArray`) holds only values that need no copy.
    const unshare=v=>v.fields?{...v,fields:v.fields.slice()}:{...v,items:v.items.slice()};
    const copyShared=root=>{
        const top=unshare(root),pending=[top];
        while(pending.length){
            const fields=pending.pop().fields;
            if(!fields)continue;
            for(let i=0;i<fields.length;i++){const f=fields[i];if(sharedData.has(f)){fields[i]=unshare(f);pending.push(fields[i]);}}
        }
        return top;
    };
    if(sharedData.has(value))return copyShared(value);
    const pending=[value],seen=new Set();
    while(pending.length){
        const v=pending.pop();
        if(v===null||typeof v!=='object'||v.ref||v.shared||v.resource||seen.has(v))continue;
        seen.add(v);
        const slots=Array.isArray(v)?v:Array.isArray(v.fields)?v.fields:Array.isArray(v.items)?v.items:null;
        if(slots){for(let i=0;i<slots.length;i++){const f=slots[i];if(retainedGraphs.has(f))slots[i]=thaw(f);else if(sharedData.has(f))slots[i]=copyShared(f);else pending.push(f);}}
        else if(v.union!==undefined){if(retainedGraphs.has(v.value))v.value=thaw(v.value);else if(sharedData.has(v.value))v.value=copyShared(v.value);else pending.push(v.value);}
    }
    return value;
}
function construct(tag, names, fields, order, isStruct, owner, retainable=false) {
    charge(1+order.length);
    // Custom array operations may expose the fresh field storage to the host.
    // Preserve those operations, but never certify their result as private.
    let ordinary=constructorArray(order)&&constructorArray(names)&&constructorArray(fields);
    if(ordinary)for(let i=0;i<order.length;i++){
        const index=order[i];
        if(typeof index!=='number'||index%1!==0||index<0||index>=names.length||index>=fields.length
            ||(names[index]!==null&&typeof names[index]!=='string')){ordinary=false;break;}
    }
    if(!ordinary)forgetStableData();
    try{
        const value={owner, tag, names: order.map(i => names[i]), fields: order.map(i => fields[i]), struct:isStruct};
        return ordinary?generatedAggregate(value,value.fields,retainable):value;
    }finally{if(!ordinary)forgetStableData();}
}
function tick(ev) {
    if (ev.fuel.left-- <= 0) throw stepLimitError(ev);
}
// The host's step limit ran out, in the language of `options.lang` (`ja`,
// `ja_JP.UTF-8`, `ja-JP`), else English: the words of `eval-step-limit`.
function stepLimitError(host) {
    const ja = /^ja([-_.@]|$)/i.test(host?.options?.lang ?? '');
    return new Error(ja ? '中断: ステップの上限に達した' : 'interrupted: the step limit ran out');
}

function quoteText(text) {
    let out = '"';
    for (const c of text) {
        const n = c.codePointAt(0);
        if (c === '"' || c === '\\') out += '\\' + c;
        else if (c === '\n') out += '\\n';
        else if (c === '\r') out += '\\r';
        else if (c === '\t') out += '\\t';
        else if (n === 0) out += '\\0';
        else if (/\p{C}|\p{Zl}|\p{Zp}/u.test(c)) out += '\\u{' + n.toString(16) + '}';
        else out += c;
    }
    return out + '"';
}

function requireDataOwner(v) {
    if(v && typeof v === 'object' && typeof v.tag === 'string' && Array.isArray(v.fields) && typeof v.owner !== 'string')
        throw new Error('constructor '+v.tag+' requires an owner type in the JavaScript data ABI');
}
// Computations return a trampoline step. Promise suspension belongs to the
// driver; effect continuations remain ordinary, reusable values.
const more = f => f;
const pure = value => {const e=(c, k) => more(() => k(c, value));e.now=()=>value;return e;};
const mapValue = (e, f) => (c, k) => e(c, (d, v) => more(() => k(d, f(v))));
const values = (es, f) => {
    // When each part is known at once (`now`: a constant or a local), no part can
    // suspend between them, so the parts need no slots unless one is a temporary.
    if(es.every(e=>e.now))return (c,k)=>{
        const args=new Array(es.length);let held=false;
        for(let i=0;i<es.length;i++){const v=es[i].now(c);args[i]=v;if(v?.temporary)held=true;}
        if(!held)return more(()=>f(c,args,k));
        return slotted(es,f,c,k,args);
    };
    return (c,k)=>slotted(es,f,c,k,null);
};
// `values` with a slot for each part; `known` holds the parts already computed.
function slotted(es,f,c,k,known){
    const scope=openScope(c.scope),env=envChild(c.env);
    // Temporaries are numbered by their depth in the context, so siblings reuse
    // ids and environments keep the same shape from one iteration to the next.
    const base=c.td??0,ids=es.map((_,i)=>-(base+i+1));
    for(const id of ids)envSet(env,id,own(scope,{id,value:undefined,shared:false}));
    const finish=(d,value)=>{
        const parent=exitScope(d.scope,scope.id);
        return more(()=>k({...d,scope:parent,env:restoreEnv(c.env,parent),td:c.td},value));
    };
    const loop = (i, d) => {
        if(i===es.length){
            const args=ids.map(id=>{const slot=envGet(d.env,id),value=slot.value;if(!value?.temporary)slot.value=undefined;return value;});
            return more(()=>f(d,args,finish));
        }
        if(known){envGet(d.env,ids[i]).value=known[i];return loop(i+1,d);}
        return es[i](d,(next,value)=>{envGet(next.env,ids[i]).value=value;return more(()=>loop(i+1,next));});
    };
    return loop(0,{...c,scope,env,td:base+ids.length});
}
function readLocal(id,deref=false,copy=false,move=false) {
    const now=c=>{const slot=envGet(c.env,id);let v=slot.value,cp=copy;if(deref&&cp&&v?.cloneOwned){v=v.cloneOwned();cp=false;}else if(deref)v=unref(v);if(move)slot.value=undefined;return cp?copyValue(v):!deref&&!move&&v?.ref?borrowedRef(v):v;};
    const e=(c,k)=>more(()=>k(c,now(c)));e.now=now;return e;
}
function defineLocal(id, shared, init, immutable=false) {
    return (c, k) => init(c, (d, v) => {
        const env = envWith(d.env,id,own(d.scope,{id,value: v, shared,immutable}));
        return more(() => k({...d, env}, null));
    });
}
function sequence(es) {
    return (c, k) => {
        const scope=openScope(c.scope);
        const loop = (i, d, v) => i === es.length ? more(() => {closeScope(d.scope);return k({...d,scope:d.scope.parent},v);})
            : more(()=>{dropValue(v);return es[i](d, (next, value) => more(() => loop(i + 1,next,value)));});
        return loop(0,{...c,scope},null);
    };
}
function branch(cond, yes, no) {
    return (c, k) => cond(c, (d,v) => more(() => (v ? yes : no)(d,k)));
}
function callFunction(fn, args, ticked) {
    return values([fn,...args], (c,[value,...vs],k) => {
        const f=unref(value),scope=openScope(c.scope),id=-(c.td??0)-1;
        // A temporary stays with the statement's slot until the statement
        // ends (`slotted`); the call's slot is another owner of it, as a
        // parameter is (`enterFunction`).
        if(value?.temporary&&value.retain)value.retain();
        const env=envWith(c.env,id,own(scope,{id,value,shared:false}));
        const inner={...c,env,scope,td:-id};
        const finish=(d,v)=>{const parent=exitScope(d.scope,scope.id);return more(()=>k({...d,scope:parent,env:restoreEnv(c.env,parent),td:c.td},v));};
        const enter=d=>f.tautoNative?external(f,vs.map(pure))(d,finish):more(()=>f(d,vs,finish));
        return ticked?tickBudget(inner,enter):enter(inner);
    });
}
// The arguments a frame may restart with: stable values, and borrows, which
// the `recur` mark lets point only outside the frame. A loop, not `every`,
// which the program's host may have replaced.
function restartableArgs(values){
    for(let i=0;i<values.length;i++){const v=values[i];if(!stableMember(v)&&!v?.ref)return false;}
    return true;
}
function tailSelfCall(fn,args) {
    return (c,k)=>{
        if(!c.restart)return callFunction(fn,args,false)(c,k);
        return values(args,(d,vs,finish)=>{
            // A borrow passed on points outside the frame (the `recur` mark asks
            // it); other unknown host values keep the ordinary ownership path.
            if(d.h!==d.restart.handlers||!restartableArgs(vs))return callFunction(fn,vs.map(pure),false)(d,finish);
            return more(()=>d.restart.run(d,vs));
        })(c,k);
    };
}
function enterFunction(body, params, captures, caller, args, k, borrowed=false, exportBorrows=true, ownedParams=[], restartable=false, consumeCaptures=false) {
    const env = envNew(),scope=openScope(caller.scope);
    if(captures)for(const [id,slot] of captures){
        if(borrowed||slot.shared){envSet(env,id,slot);scopeAlias(scope,id,slot);}
        else {
            envSet(env,id,own(scope,{...slot,value:consumeCaptures?slot.value:copyValue(slot.value)}));
            if(consumeCaptures)slot.value=undefined;
        }
    }
    for (let i=0;i<params.length;i++){if(args[i]?.ref&&args[i]?.retain)args[i].retain();envSet(env,params[i],own(scope,{id:params[i],value:args[i],shared:false,immutable:ownedParams[i]===true}));}
    const boundary = caller.h?.id;
    const ret = (d,v) => {
        if(exportBorrows)v=exportBorrow(v);
        let h = d.h;
        while (h && h.id !== boundary) h = h.outer;
        const scope=unwind(d.scope,caller.scope);
        return more(() => k({...caller,scope,env:restoreEnv(caller.env,scope),h},v));
    };
    const restart=restartable&&restartableArgs(args)?{
        handlers:caller.h,
        run:(d,values)=>{
            const parent=unwind(d.scope,caller.scope);
            return more(()=>enterFunction(body,params,captures,{...caller,scope:parent},values,k,borrowed,exportBorrows,ownedParams,true));
        }
    }:null;
    return more(() => body({...caller,env,ret,scope,restart},ret));
}
function matchPattern(p,v,bindings,taken=null,from=null,index=0) {
    switch(p[0]) {
        case 'wild': return true;
        case 'bind':
            if(taken&&!p[2]&&!v?.ref){const slot={value:v,shared:false,immutable:p[3]===true};bindings.set(p[1],slot);taken.push([from,index,slot]);return true;}
            bindings.set(p[1],{value:p[2]?(v?.ref?copyValue(v):reference(()=>v,x=>{v=x;})):copyValue(unref(v)),shared:false,immutable:!p[2]&&p[3]===true});return true;
        case 'literal': return equal(p[1],unref(v));
        case 'product': { const obj=unref(v);const inner=v?.ref||retainedGraphs.has(obj)?null:taken;return p[1].every((q,i)=>matchPattern(q,v?.ref?fieldRef(v,i):obj.fields[i],bindings,inner,obj,i)); }
        case 'ctor': { const obj=unref(v);requireDataOwner(obj);const inner=v?.ref||retainedGraphs.has(obj)?null:taken;return obj?.tag===p[1]&&obj.owner===p[3]&&p[2].every((q,i)=>matchPattern(q,v?.ref?fieldRef(v,i):obj.fields[i],bindings,inner,obj,i)); }
        // A union's value `{union,variant,value}`: what was injected, taken as the whole scrutinee is.
        case 'variant': { const u=unref(v);if(u?.variant!==p[1])return false;return matchPattern(p[2],v?.ref?reference(()=>unref(v).value,x=>{unref(v).value=x;}):u.value,bindings,v?.ref?null:taken,from,index); }
    }
}
// `take` is set only when the scrutinee is a fresh owned value and no arm has
// a guard, so a matched arm is final once its pattern fits.
function matchValue(scrut,arms,take=false) {
    return (c,k)=>scrut(c,(d,v)=>{
        const scope=openScope(d.scope),id=-(d.td??0)-1;
        const slot=own(scope,{id,value:v,shared:false});
        const env=envWith(d.env,id,slot);
        const finish=(after,value)=>{const parent=exitScope(after.scope,scope.id);return more(()=>k({...after,scope:parent,env:restoreEnv(d.env,parent),td:d.td},value));};
        const loop=i=>{
            if(i===arms.length)throw new Error('no arm of the match fits');
            const [pat,guard,body]=arms[i],bindings=new Map(),taken=take?[]:null;
            if(!matchPattern(pat,v,bindings,taken)){
                const kept=new Set(taken?.map(t=>t[2]));
                for(const binding of bindings.values())if(!kept.has(binding))dropValue(binding.value);
                return more(()=>loop(i+1));
            }
            if(taken)for(const [from,index] of taken){if(from){if(sharedData.has(from))continue;stableData.delete(from);from.fields[index]=undefined;}else slot.value=undefined;}
            for(const [id,slot] of bindings)own(scope,Object.assign(slot,{id}));
            const inner={...d,scope,env:envWithAll(env,bindings),td:-id};
            return guard(inner,(next,yes)=>{
                if(yes)return more(()=>body(next,finish));
                for(const slot of bindings.values()){dropValue(slot.value);slot.value=undefined;}
                return more(()=>loop(i+1));
            });
        };
        return loop(0);
    });
}
function route(c,op,quant,vs,k,inside=null,skip=null) {
    let outside=inside===null;
    const prefix=[];
    const search=frame=>{
        if(!frame) {
            if(op==='show'){const text=vs[0]+' = '+shown(vs[1]);forgetStableData();try{c.host.show(text);}finally{forgetStableData();}return more(()=>k(c,null));}
            // The host answers `wait`: the task goes on once its signal is raised.
            if(op==='wait'&&vs[0]?.kind==='Signal'){const s=vs[0];if(s.raised)return more(()=>k(c,null));return new Promise(resolve=>waitSignal(s,()=>resolve(more(()=>k(c,null)))));}
            // The host answers `overflow` and `divzero` by stopping the program.
            if(op==='overflow'&&vs.length===0)throw new Error('the number is too large');
            if(op==='divzero'&&vs.length===0)throw new Error('division by zero');
            throw new Error('nothing handles '+op);
        }
        if(frame.callback && quant!=='direct' && frame.id!==skip?.id)return frame.suspend(c,op,quant,vs,k);
        prefix.push(frame);
        if(frame.budget===inside)outside=true;
        const arms=outside?frame.arms.filter(a=>a.op===op):[];
        const armAt=i=>{
            if(i===arms.length)return more(()=>search(frame.outer));
            const arm=arms[i],bindings=new Map();
            if(!arm.pats.every((p,j)=>matchPattern(p,vs[j],bindings)))return more(()=>armAt(i+1));
            const captured=[...prefix];
            const snapshot=captureContext(c,frame.scope,quant==='many',frame.env);
            let resumed=false;
            const resume=(caller,[v],target)=>{
                resumed=true;
                if(quant!=='many')unprotect();
                const back=(d,result)=>more(()=>target({...caller,h:d.h},result));
                const context=resumeContext(snapshot,caller.scope,quant==='many');
                let h=caller.h;
                for(let i=captured.length-1;i>=0;i--) {
                    const old=captured[i];
                    const scope=context.scopes.get(old.scope)??caller.scope;
                    const env=envOf(envEntries(old.env).map(([id,slot])=>[id,context.sourceSlots.get(slot)??slot]));
                    h={...old,outer:h,scope,env,target:i===captured.length-1?back:old.target};
                }
                return more(()=>k({...c,env:context.env,scope:context.scope,h},v));
            };
            let owners=1,accepted=false,initialOwned=true;
            const ownsSnapshot=()=>accepted&&quant!=='direct'&&(quant==='many'||!resumed);
            const live=()=>owners>0&&ownsSnapshot();
            const unprotect=()=>{for(const scope of snapshot.originals){scope.suspended?.delete(live);if(!scope.suspended?.size)scope.suspended=undefined;}};
            // The arm owns one continuation reference until it completes or
            // fails, unless it moved `k` out (into a value it returns).
            const pending=c.scope.pending;
            const releaseInitial=()=>{if(!initialOwned)return;initialOwned=false;pending.delete(releaseInitial);if(accepted&&!resumed)for(const frame of captured)frame.cancel?.();if(arm.k===null||bindings.get(arm.k).value===resume)resume.release();keepAround();};
            if(quant!=='direct')pending.add(releaseInitial);
            resume.retain=()=>{owners++;};
            // The bindings around the handle: a `k` kept past its arm reads
            // them after their scope may have closed, so that scope leaves
            // them to it.
            let around=[];
            const keepAround=()=>{if(owners===0||quant==='direct')return;around=envEntries(frame.env).map(e=>e[1]);for(const slot of around)(slot.keptBy??=new Set()).add(resume);};
            resume.release=()=>{if(--owners!==0)return;unprotect();if(ownsSnapshot())for(const scope of snapshot.originals)closeScope(scope);for(const slot of around)unkeep(slot,resume);};
            if(arm.k!==null)bindings.set(arm.k,{value:resume,shared:false});
            const env=envWithAll(frame.env,bindings),scope=openAliasScope(frame.scope,env);
            const outside={...c,h:frame.outer,scope,env};
            return arm.guard(outside,(next,yes)=>{
                if(!yes){releaseInitial();exitScope(next.scope,scope.id);return more(()=>armAt(i+1));}
                accepted=true;
                if(ownsSnapshot())for(const scope of snapshot.originals){scope.suspended??=new Set();scope.suspended.add(live);}
                if(quant==='direct') {
                    return arm.body({...next,direct:true},(after,v)=>{exitScope(after.scope,scope.id);return more(()=>k({...c,host:after.host},v));});
                }
                return arm.body(next,(after,v)=>{
                    releaseInitial();
                    exitScope(after.scope,scope.id);
                    return more(()=>frame.target({...after,scope:frame.scope,env:frame.env},v));
                });
            });
        };
        return armAt(0);
    };
    return more(()=>search(c.h));
}
// A host object stays in its handle; Tauto values hold the handle. Copies
// retain it. A value moved to an extern is held by the host, and the host
// returns that same handle for the object. The release binding runs when
// neither Tauto nor the host holds it, or when the instance ends.
const hostHandles=new WeakSet();
function hostHandle(host,type,object){
    const known=object!==null&&(typeof object==='object'||typeof object==='function')?host.objects.get(object):undefined;
    if(known)return known.fromHost(type);
    let refs=1,held=0,live=true,busy=0,closing=false;
    const kept=[];
    const handle={kept,owner:type,
        // A kept callback that is still running keeps its owner; the release
        // waits for it, and no new host call starts meanwhile.
        get closing(){return closing||!live;},
        enter(){busy++;},
        leave(){if(--busy===0&&closing&&live)dispose();},tag:type,names:[],fields:[],struct:true,hostType:type,
        retain(){if(!live)throw new Error('javascript host value '+type+' was released');refs++;},
        release(){if(live&&--refs===0&&held===0)dispose();},
        toHost(){refs--;held++;},
        fromHost(want){
            if(want!==type)throw new Error('javascript host value '+type+' returned as '+want);
            if(held>0)held--;
            refs++;return handle;
        },
        dispose(){if(live)dispose();},
        object(want,instance){
            if(!live)throw new Error('javascript host value '+type+' was released');
            if(want!==type)throw new Error('javascript host value '+type+' passed as '+want);
            if(instance!==host.instance)throw new Error('javascript host value '+type+' belongs to another run');
            return object;
        }};
    const dispose=()=>{if(busy>0){closing=true;return;}live=false;refs=0;held=0;host.handles.delete(handle);
        if(object!==null&&(typeof object==='object'||typeof object==='function'))host.objects.delete(object);
        for(const callback of kept.splice(0).reverse())callback.close();const release=host.externs['@release:'+type]??host.options.release?.[type];if(typeof release==='function')release(object);};
    hostHandles.add(handle);host.handles.add(handle);retainedLeaves.add(handle);
    if(object!==null&&(typeof object==='object'||typeof object==='function'))host.objects.set(object,handle);
    return handle;
}
function hostObject(host,type,value){
    if(!hostHandles.has(value))throw new Error('javascript extern expected a host value '+type);
    return value.object(type,host.instance);
}
// A kept callback runs in a call of its own on the instance; the host value
// that owns it ends it, after which a host call does nothing.
function keptCallback(host,owner,f){
    let open=true;
    const callback=(...values)=>{
        if(!open||owner.closing)return undefined;
        forgetStableData();
        const {c,finish,result}=startCall(host);
        const end=()=>{try{endCall(c);}finally{owner.leave();}};
        owner.enter();
        let step;
        try{
            step=f(c,values,finish);
            while(typeof step==='function')step=step();
        }catch(e){end();throw e;}
        if(step===null){end();return result();}
        return (async()=>{
            try{
                while(step!==null){
                    if(typeof step==='function')step=step();
                    else{forgetStableData();try{step=await step;}finally{forgetStableData();}}
                }
            }finally{end();}
            return result();
        })();
    };
    callback.close=()=>{if(!open)return;open=false;dropValue(f);};
    owner.kept.push(callback);
    return callback;
}
function external(name,args) {
    return values(args,(c,vs,k)=>{
        const fn=typeof name==='function'?name:c.host.externs[name];
        if(typeof fn!=='function')throw new Error('missing javascript extern: '+name);
        forgetStableData();
        let active=true,waiting=null,context=c;
        const cancel=()=>{active=false;c.scope.pending.delete(cancel);};
        c.scope.pending.add(cancel);
        const events=[];
        const enqueue=e=>{events.push(e);if(waiting){const wake=waiting;waiting=null;wake();}};
        const next=()=>{
            if(events.length){const event=events.shift();return event(context);}
            return new Promise(resolve=>{waiting=()=>resolve(more(next));});
        };
        const boundary={id:{},arms:[],outer:c.h,env:c.env,callback:true,cancel};
        const callback=(f,wasmContext=c.wasm)=>(...values)=>{
            if(!active)throw new Error('javascript extern callback outlived its call');
            forgetStableData();
            let finished=false,result,resolve,reject;
            const promise=new Promise((a,b)=>{resolve=a;reject=b;});promise.catch(()=>{});
            const finish=(_,v)=>{forgetStableData();finished=true;result=thaw(v);resolve(result);return null;};
            const pump=step=>{
                try{
                    while(typeof step==='function')step=step();
                    if(step!==null){forgetStableData();Promise.resolve(step).then(next=>{forgetStableData();pump(next);},error=>{forgetStableData();reject(error);});}
                }catch(e){forgetStableData();reject(e);enqueue(()=>{cancel();throw e;});}
            };
            // Every queued event keeps its own pump, including concurrent callbacks.
            const ownBoundary={...boundary};
            if(fn.tautoNative)ownBoundary.cancel=()=>{cancel();reject(new Error('a Rust wasm callback cannot abandon its native frame'));};
            ownBoundary.suspend=(ctx,op,quant,values,continuation)=>{
                enqueue(()=>route(ctx,op,quant,values,(after,value)=>{
                    let h=after.h;while(h&&h.id!==boundary.id)h=h.outer;
                    context={...c,h:h?h.outer:after.h};
                    pump(continuation(after,value));return next();
                },null,ownBoundary));
                return null;
            };
            pump(f({...c,h:ownBoundary,wasm:wasmContext},values,finish));
            forgetStableData();return finished?result:promise;
        };
        const alive=()=>{if(!active)throw new Error('javascript extern borrow outlived its call');};
        const signature=typeof name==='string'&&typeof hostSignatures!=='undefined'?hostSignatures[name]:undefined;
        const consumed=[];
        const hostArgs=vs.map((v,i)=>{const type=signature?.params[i];if(type){if(v?.ref)return hostObject(c.host,type,v.get());const object=hostObject(c.host,type,v);consumed.push(v);return object;}const value=unref(v);if(typeof value==='function'&&signature?.owner!=null)return keptCallback(c.host,vs[signature.owner]?.ref?vs[signature.owner].get():vs[signature.owner],value);if(typeof value==='function'){if(value.tautoNative)return value;const adapted=callback(value);adapted.nib=value;adapted.release=()=>{if(!v?.ref)dropValue(value);};return adapted;}if(fn.tautoNative)return v;if(!v?.ref)return thaw(v);thawReference(v);return reference(()=>{alive();return v.get();},x=>{alive();v.set(x);});});
        let value;
        try{value=fn.tautoNative?fn.invoke(hostArgs,callback,!c.direct,c.wasm??null):fn(...hostArgs);}catch(e){forgetStableData();cancel();throw e;}
        // The host has the object now; the moved Tauto references end.
        finally{for(const handle of consumed)handle.toHost();}
        forgetStableData();
        if(value&&typeof value.then==='function') {
            // A Promise is a wait on the host, which the extern's row says.
            if(typeof name==='string'&&!fn.tautoNative&&typeof hostWaits!=='undefined'&&!hostWaits.has(name)){cancel();Promise.resolve(value).catch(()=>{});throw new Error('extern '+name+' returned a Promise but its row has no wait');}
            if(c.direct){cancel();Promise.resolve(value).catch(()=>{});throw new Error('a direct handler cannot await javascript extern '+name);}
            Promise.resolve(value).then(v=>enqueue(d=>{forgetStableData();cancel();if(signature?.ret)v=hostHandle(c.host,signature.ret,v);return more(()=>k(d,v));}),e=>enqueue(()=>{forgetStableData();cancel();throw e;}));
            return next();
        }
        forgetStableData();cancel();
        if(events.length)throw new Error('javascript extern must await its suspending callbacks');
        if(signature?.ret)value=hostHandle(c.host,signature.ret,value);
        return more(()=>k(c,value));
    });
}
// The host's step limit: `options.steps`, else ten million; none when
// `permissions.div` lets `div` run without it (`--allow-div`).
function hostSteps(options){return options.steps??(options.permissions?.div===true?Infinity:10000000);}
function newHost(show,externs,options){
    return {show,externs,options,temporary:0,fuel:{left:hostSteps(options)},handles:new Set(),objects:new WeakMap(),instance:{}};
}
// Each call has its own context, handlers and step budget; the instance's
// host values outlive the call.
function startCall(host){
    const call={...host,temporary:0,fuel:{left:hostSteps(host.options)}};
    let result;
    const c={env:envNew(),h:null,host:call,ret:null,direct:false,scope:openScope(null)};
    const finish=(_,v)=>{result=thaw(v);return null;};
    c.ret=finish;
    return {c,finish,result:()=>result};
}
function endCall(c){
    try{
        for(const scope of [...c.scope.open].reverse())if(![...scope.suspended??[]].some(live=>live()))closeScope(scope);
        for(const release of [...c.scope.pending])release();
    }finally{forgetStableData();}
}
function disposeHost(host){
    try{for(const handle of [...host.handles].reverse())handle.dispose();}
    finally{forgetStableData();}
}
// The task running now (`null` on the program's main): the mutexes it takes
// from note it, so that its failure poisons them (`poisonHeld`).
let TASK=null;
async function driveIn(start,host,task=null){
    forgetStableData();
    const {c,finish,result}=startCall(host);
    try {
        TASK=task;
        let step=start(c,finish);
        while(step!==null){
            // A task of a disposed instance stops at its next step.
            if(host.instance.disposed)throw new Error('the instance was disposed');
            TASK=task;
            if(typeof step==='function')step=step();
            else{forgetStableData();try{step=await step;}finally{forgetStableData();}}
        }
    } catch(e) {
        // Before its guards are dropped with its scopes, which then give
        // nothing back to a poisoned mutex.
        if(task)poisonHeld(task);
        throw e;
    } finally {endCall(c);}
    return result();
}
// A task failed: each mutex whose content it holds is poisoned, and the places
// in its line wake to fail.
function poisonHeld(task){
    for(const m of task.held){
        if(m.taker!==task)continue;
        m.poisoned=true;
        for(const s of m.waiting.splice(0))raise(s);
    }
    task.held.clear();
}
function tookMutex(m){m.taker=TASK;if(TASK)TASK.held.add(m);}
function checkPoisoned(m){if(m.poisoned)throw new Error('the Mutex is poisoned: a task that held its content failed');}
// The host hears of a task's failure at once: `options.task_failed(message)`,
// else its standard error.
function reportTaskFailure(host,e){
    const message=e?.message??String(e);
    const f=host.options.task_failed;
    if(typeof f==='function'){f(message);return;}
    const line='a task failed: '+message+'\n';
    if(typeof host.options.os_eprint==='function')host.options.os_eprint(line);else console.error(line.trimEnd());
}
function driveSync(start,host,name){
    forgetStableData();
    const {c,finish,result}=startCall(host);
    try {
        let step=start(c,finish);
        while(step!==null){
            if(typeof step!=='function'){Promise.resolve(step).catch(()=>{});throw new Error('exported function '+name+' cannot wait on the host');}
            step=step();
        }
    } finally {endCall(c);}
    return result();
}
async function drive(start,show,externs,options={},task=null) {
    const host=newHost(show,externs,options);
    try{return await driveIn(start,host,task);}finally{disposeHost(host);}
}
// An instance runs exported functions; importing the module runs nothing.
// A host object argument gets a handle of the instance, a borrowed one only
// for the call; a host function is callable during the call; a function
// result is kept by the instance until it is disposed.
function instantiateWith(table,externs,options){
    const host=newHost(options.show??console.log,externs,options);
    // A task an export starts runs in the instance, after the call returns,
    // until the instance is disposed.
    host.instance.tasks=host;host.instance.disposed=false;
    let disposed=false,running=0;
    const owner={kept:[],closing:false,enter(){},leave(){}};
    const instance={dispose(){if(disposed)return;disposed=true;host.instance.disposed=true;owner.closing=true;
        try{for(const callback of owner.kept.splice(0).reverse())callback.close();}finally{disposeHost(host);}}};
    for(const [name,[f,sync,params,ret]] of Object.entries(table)){
        instance[name]=(...args)=>{
            if(disposed)throw new Error('the instance was disposed');
            if(running)throw new Error('exported function '+name+' re-entered its instance');
            const lent=[],ends=[];
            const values=args.map((v,i)=>{
                const p=params[i];
                if(p?.host){const handle=hostHandle(host,p.host,v);if(p.borrowed){handle.retain();lent.push(handle);}return handle;}
                if(p?.fn){
                    if(typeof v!=='function')throw new Error('exported function '+name+' expected a function');
                    let active=true;ends.push(()=>{active=false;});
                    return (c,vs,k)=>{if(!active)throw new Error('a host function outlived the call of '+name);return external(v,vs.map(pure))(c,k);};
                }
                // The call owns what it is given, and may take its parts apart; the host
                // keeps its value, which it may pass again (a shared graph is not copied).
                return v!==null&&typeof v==='object'?copyValue(v):v;
            });
            const out=v=>{
                if(ret?.host){const object=hostObject(host,ret.host,v);v.toHost();return object;}
                if(ret?.kept)return keptCallback(host,owner,v);
                return v;
            };
            const end=()=>{for(const e of ends)e();for(const handle of lent)handle.toHost();};
            const start=(c,k)=>f(c,values,k);
            if(sync){running++;try{return out(driveSync(start,host,name));}finally{running--;end();}}
            return driveIn(start,host).then(out).finally(end);
        };
    }
    return instance;
}
// Direct forms run on the host stack. `H` is the host whose fuel they count;
// they never reach the driver, so it stays the same until they return.
let H=null;
function T(v){if(H.fuel.left--<=0)throw stepLimitError(H);return v;}
// What a direct form changes in place is logged, so that starting again in
// continuation form starts from the same values: `J` holds triples of a
// target, a key and the value before (an index or a property of the target;
// `-1`: an array's length, `-2`: a reference's value, `-3`: a popped item).
// Vectors and `Buf`s made in the run (`F`) are not logged.
let J=null,F=null;
function logged(a){return !F.has(a);}

function undo(log){
    for(let i=log.length-3;i>=0;i-=3){
        const t=log[i],key=log[i+1],old=log[i+2];
        if(key===-1)t.length=old;else if(key===-2)t.set(old);else if(key===-3)t.push(old);else t[key]=old;
    }
}
// Data a direct form builds, its fields in the declaration's order. The
// arrays are the form's own, never a host's, so the value is certified as
// `construct` certifies ordinary arrays.
function dcons(tag,names,fields,isStruct,owner,retainable=false){charge(1+fields.length);return generatedAggregate({owner,tag,names,fields,struct:isStruct},fields,retainable&&ordinaryArrayPair(fields,names));}
const dsome=v=>dcons('Some',[null],[v],false,'Option'),dnone=()=>dcons('None',[],[],false,'Option');
function vecGet(v,i){const a=v.items;i=Number(i);return i>=0&&i<a.length?dsome(a[i]):dnone();}
function bufOf(t){const b={kind:'Buf',text:t.text??t};F.add(b);return b;}
function bufPush(b,text){if(logged(b))J.push(b,'text',b.text);b.text+=text;return null;}
// `replace` of a vector's or a `Buf`'s content: the old content comes out as a value.
function direct(d,cps,c,args,k,borrowed){
    let budget=false;
    for(let h=c.h;h;h=h.outer)if(h.budget){budget=true;break;}
    for(let i=0;i<args.length;i++)if(borrowed[i]===2&&args[i]?.operation)budget=true;
    if(!budget&&!c.continuationOnly){
        const outer=H,left=c.host.fuel.left,log=[],outerJ=J,outerF=F;
        H=c.host;J=log;F=new WeakSet();
        try{const v=d(...args.map((a,i)=>borrowed[i]===1||borrowed[i]===2?unref(a):a));return more(()=>k(c,v));}
        catch(e){
            // Too deep for the host stack, or an operator whose result does not
            // exist (which performs `overflow` or `divzero`, as only the
            // continuation form can): start again in continuation form.
            if(!(e instanceof RangeError)&&!(e instanceof OpFail))throw e;
            undo(log);
            c.host.fuel.left=left;
        }finally{H=outer;J=outerJ;F=outerF;}
        return cps({...c,continuationOnly:true},args,(d,v)=>more(()=>k(c,v)));
    }
    return cps(c,args,k);
}
// Lexical scopes own values; moves empty their slot. Continuation copies get
// their own owned slots, while explicitly shared cells keep their identity.
function dropValue(value) {
    const pending=[{value}];
    while(pending.length){
        const action=pending.pop();
        if(action.array){
            if(action.index>=0){pending.push({array:action.array,index:action.index-1});pending.push({value:action.array[action.index]});}
            continue;
        }
        const v=action.value;
        if(v==null||sharedData.has(v))continue;
        const retained=retainedGraphs.get(v);
        if(retained){if(--retained.owners===0)pending.push({array:v.fields,index:v.fields.length-1});continue;}
        if(typeof v.release==='function'){v.release();continue;}
        if(v.ref||v.shared)continue;
        // Each entry is an owner, even if two entries have the same identity.
        if(Array.isArray(v)){pending.push({array:v,index:v.length-1});continue;}
        if(typeof v==='object'){
            if(v.union!==undefined)pending.push({value:v.value});
            else if(v.fields)pending.push({value:v.fields});
            else if(v.items)pending.push({value:v.items});
        }
    }
}
// The registry also covers suspended computations whose active context is not
// on the driver stack. Retained continuations keep their own snapshot owners.
function registerScope(scope){scope.open=scope.parent?.open??new Set();scope.pending=scope.parent?.pending??new Set();scope.open.add(scope);return scope;}
function openScope(parent){return registerScope({id:{},parent,slots:[],closed:false});}
function own(scope,slot){slot.owners??=1;scope.slots.push(slot);return slot;}
// A lexical alias names an existing binding without owning its value.
// The scope's owned slots take precedence over these borrowed bindings.
const scopeAliases=new WeakMap();
// Set once an alias or a resumption puts another slot under a binding's id.
let slotsRebound=false;
// An alias of the slot that already answers its id, or of an id that no
// scope owns, rebinds nothing, so handler arms keep the fast path.
function nearestSlot(scope,id){
    for(let s=scope;s;s=s.parent){
        for(let i=s.slots.length-1;i>=0;i--)if(s.slots[i].id===id)return s.slots[i];
        const aliases=scopeAliases.get(s);
        if(aliases)for(let i=aliases.length-1;i>=0;i--)if(aliases[i].id===id)return aliases[i].slot;
    }
    return undefined;
}
function scopeAlias(scope,id,slot){
    if(!slotsRebound){const found=nearestSlot(scope,id);if(found!==undefined&&found!==slot)slotsRebound=true;}
    let aliases=scopeAliases.get(scope);
    if(!aliases){aliases=[];scopeAliases.set(scope,aliases);}
    aliases.push({id,slot});
}
function openAliasScope(parent,env){
    const scope=openScope(parent);
    for(const [id,slot] of envEntries(env))scopeAlias(scope,id,slot);
    return scope;
}
function copyScopeAliases(source,target,slots){
    const aliases=scopeAliases.get(source);
    if(aliases)scopeAliases.set(target,aliases.map(({id,slot})=>({id,slot:slots.get(slot)??slot})));
}
function closeScope(scope){
    if(scope.closed)return;
    scope.closed=true;
    scope.open.delete(scope);
    for(let i=scope.slots.length-1;i>=0;i--){const slot=scope.slots[i];if(slot.keptBy?.size){slot.orphaned=true;continue;}dropSlot(slot);}
}
function dropSlot(slot){if(slot.shared&&--slot.owners>0)return;dropValue(slot.value);slot.value=undefined;}
// A kept continuation lets go of a binding around its handle; the last one
// drops it if its scope has closed.
function unkeep(slot,resume){if(!slot.keptBy?.delete(resume)||slot.keptBy.size)return;slot.keptBy=undefined;if(slot.orphaned){slot.orphaned=false;dropSlot(slot);}}
function unwind(scope,boundary){
    if(boundary){let found=scope;while(found&&found.id!==boundary.id)found=found.parent;if(!found)return scope;}
    while(scope&&scope.id!==boundary?.id){closeScope(scope);scope=scope.parent;}
    return scope;
}
// Scope identity distinguishes copies of the same lexical scope in nested resumptions.
function captureContext(c,boundary,clone,boundaryEnv=null){
    const slots=new Map(),frames=[];
    for(let s=c.scope;s&&s!==boundary;s=s.parent)frames.push(s);
    // A single-shot continuation keeps its own frames: it is resumed once, so
    // it moves them under its new caller instead of copying the whole stack
    // at every perform.
    if(!clone){
        if(boundaryEnv&&frames.length)for(const [id,slot] of envEntries(boundaryEnv))scopeAlias(frames[frames.length-1],id,slot);
        return {originals:frames,sourceSlots:slots,frames,env:c.env,inPlace:true};
    }
    for(const s of frames)for(const slot of s.slots)if(clone&&!slot.shared)slots.set(slot,{...slot});
    const copies=frames.map(s=>{const frame={...s,slots:s.slots.map(slot=>slots.get(slot)??slot)};copyScopeAliases(s,frame,slots);return frame;});
    // A resumed body keeps its lexical boundary before its new dynamic caller.
    // Empty raw snapshots have no body frame on which to install a boundary.
    if(boundaryEnv&&copies.length)for(const [id,slot] of envEntries(boundaryEnv))scopeAlias(copies[copies.length-1],id,slots.get(slot)??slot);
    return {originals:frames,sourceSlots:slots,frames:copies,env:envOf(envEntries(c.env).map(([id,slot])=>[id,slots.get(slot)??slot]))};
}
function resumeContext(snapshot,parent,clone){
    slotsRebound=true;
    if(snapshot.inPlace){
        const frames=snapshot.frames,scopes=new Map();
        for(const s of frames){s.open.delete(s);s.closed=false;s.suspended=undefined;scopes.set(s,s);}
        if(frames.length)frames[frames.length-1].parent=parent;
        for(let i=frames.length-1;i>=0;i--)registerScope(frames[i]);
        return {scope:frames.length?frames[0]:parent,scopes,sourceSlots:snapshot.sourceSlots,env:snapshot.env};
    }
    const slots=new Map();
    if(clone)for(const s of snapshot.frames)for(const slot of s.slots)if(!slot.shared&&!slots.has(slot))slots.set(slot,{...slot,value:copyValue(slot.value)});
    let scope=parent;const scopes=new Map();
    for(let i=snapshot.frames.length-1;i>=0;i--){const s=snapshot.frames[i];scope=registerScope({...s,parent:scope,closed:false,suspended:undefined,slots:s.slots.filter(slot=>!clone||!slot.shared).map(slot=>slots.get(slot)??slot)});copyScopeAliases(s,scope,slots);scopes.set(snapshot.originals[i],scope); }
    // Handler environments must point to this resumption's slots, including temporaries.
    const sourceSlots=new Map([...snapshot.sourceSlots].map(([original,saved])=>[original,slots.get(saved)??saved]));
    return {scope,scopes,sourceSlots,env:envOf(envEntries(snapshot.env).map(([id,slot])=>[id,slots.get(slot)??slot]))};
}

// An environment maps binding ids to slots. A child keeps the environment it
// extends and holds only the bindings it adds, so binding a name does not copy
// the bindings around it; a chain longer than `envDepthLimit` is written out
// flat again, which keeps reads short. Ids are kept in arrays, not as keys of
// an object: an id is an array index to the engine, and an object keyed by
// ids far apart gets an element store as long as the largest one, so every
// call would allocate in proportion to the size of the program.
const envDepthLimit=16;
class Env{constructor(parent,depth){this.parent=parent;this.depth=depth;this.ids=[];this.slots=[];}}
function envNew(){return new Env(null,0);}
function envGet(env,id){
    for(let e=env;e;e=e.parent){const ids=e.ids;for(let i=ids.length-1;i>=0;i--)if(ids[i]===id)return e.slots[i];}
    return undefined;
}
function envSet(env,id,slot){const i=env.ids.indexOf(id);if(i>=0)env.slots[i]=slot;else{env.ids.push(id);env.slots.push(slot);}}
// Each id once, with its innermost binding.
function envEntries(env){
    if(!env.parent){const out=new Array(env.ids.length);for(let i=0;i<out.length;i++)out[i]=[env.ids[i],env.slots[i]];return out;}
    const seen=new Set(),out=[];
    for(let e=env;e;e=e.parent)for(let i=e.ids.length-1;i>=0;i--){const id=e.ids[i];if(!seen.has(id)){seen.add(id);out.push([id,e.slots[i]]);}}
    return out;
}
function envOf(entries){const out=envNew();for(const [id,slot] of entries){out.ids.push(id);out.slots.push(slot);}return out;}
function envChild(env){
    const d=env.depth+1;
    if(d>envDepthLimit)return envOf(envEntries(env));
    return new Env(env,d);
}
function envWith(env,id,slot){const out=envChild(env);envSet(out,id,slot);return out;}
// `bindings` is a Map from ids to slots.
function envWithAll(env,bindings){const out=envChild(env);for(const [id,slot] of bindings)envSet(out,id,slot);return out;}

function restoreEnv(env,scope){
 // Every return runs this, so it allocates only when a slot was replaced.
 // Until an alias or a resumption rebinds an id, every binding is still
 // its own, and the walk is skipped.
 if(!slotsRebound)return env;
 const entries=envEntries(env),bound=new Map(entries),found=new Map();
 let left=entries.length;
 for(let s=scope;s&&left;s=s.parent){
  for(const slot of s.slots)if(bound.has(slot.id)&&!found.has(slot.id)){found.set(slot.id,slot);left--;}
  const aliases=scopeAliases.get(s);
  if(aliases)for(const {id,slot} of aliases)if(bound.has(id)&&!found.has(id)){found.set(id,slot);left--;}
 }
 let same=true;
 for(const [id,slot] of entries)if(found.has(id)&&found.get(id)!==slot){same=false;break;}
 if(same)return env;
 return envOf(entries.map(([id,slot])=>[id,found.has(id)?found.get(id):slot]));
}

function exitScope(scope,id){let found=scope;while(found&&found.id!==id)found=found.parent;if(!found)return scope;while(scope){const done=scope.id===id;closeScope(scope);scope=scope.parent;if(done)break;}return scope;}
// `Float`'s functions: the same algorithms as `crates/tauto-rt/src/float_math.rs`,
// operation for operation, so that a program prints the same digits under
// every backend. The engine's own `Math.sin`, `Math.log`, … are not used:
// engines differ from each other and from the Rust backend in the last bit.
//
// Derived from the same sources as `float_math.rs`: the `libm` crate (MIT OR
// Apache-2.0), musl libc and FreeBSD's msun; see NOTICE.
// ====================================================
// Copyright (C) 1993, 2004 by Sun Microsystems, Inc. All rights reserved.
//
// Developed at SunPro, a Sun Microsystems, Inc. business.
// Permission to use, copy, modify, and distribute this
// software is freely granted, provided that this notice
// is preserved.
// ====================================================
const floatMath=(()=>{
    const F=new Float64Array(1),U=new Uint32Array(F.buffer);
    const LE=new Uint8Array(new Uint16Array([1]).buffer)[0]===1,H=LE?1:0,L=LE?0:1;
    const hi=x=>{F[0]=x;return U[H];};
    const lo=x=>{F[0]=x;return U[L];};
    const words=(h,l)=>{U[H]=h;U[L]=l;return F[0];};
    const setHi=(x,h)=>{F[0]=x;U[H]=h;return F[0];};
    const setLo=(x,l)=>{F[0]=x;U[L]=l;return F[0];};
    const scalbn=(x,n)=>{
        const x1p1023=words(0x7fe00000,0),x1p53=words(0x43400000,0),x1p_1022=words(0x00100000,0);
        let y=x;
        if(n>1023){y*=x1p1023;n-=1023;if(n>1023){y*=x1p1023;n-=1023;if(n>1023)n=1023;}}
        else if(n< -1022){y*=x1p_1022*x1p53;n+=1022-53;if(n< -1022){y*=x1p_1022*x1p53;n+=1022-53;if(n< -1022)n=-1022;}}
        return y*words((0x3ff+n)<<20>>>0,0);
    };
    const kSin=(x,y,iy)=>{
        const S1=-1.66666666666666324348e-01,S2=8.33333333332248946124e-03,S3=-1.98412698298579493134e-04,
            S4=2.75573137070700676789e-06,S5=-2.50507602534068634195e-08,S6=1.58969099521155010221e-10;
        const z=x*x,w=z*z,r=S2+z*(S3+z*S4)+z*w*(S5+z*S6),v=z*x;
        return iy===0?x+v*(S1+z*r):x-((z*(0.5*y-v*r)-y)-v*S1);
    };
    const kCos=(x,y)=>{
        const C1=4.16666666666666019037e-02,C2=-1.38888888888741095749e-03,C3=2.48015872894767294178e-05,
            C4=-2.75573143513906633035e-07,C5=2.08757232129817482790e-09,C6=-1.13596475577881948265e-11;
        const z=x*x,w=z*z,r=z*(C1+z*(C2+z*C3))+w*w*(C4+z*(C5+z*C6)),hz=0.5*z,w1=1.0-hz;
        return w1+(((1.0-w1)-hz)+(z*r-x*y));
    };
    const T=[3.33333333333334091986e-01,1.33333333333201242699e-01,5.39682539762260521377e-02,
        2.18694882948595424599e-02,8.86323982359930005737e-03,3.59207910759131235356e-03,
        1.45620945432529025516e-03,5.88041240820264096874e-04,2.46463134818469906812e-04,
        7.81794442939557092300e-05,7.14072491382608190305e-05,-1.85586374855275456654e-05,
        2.59073051863633712884e-05];
    const kTan=(x,y,odd)=>{
        const PIO4=7.85398163397448278999e-01,PIO4_LO=3.06161699786838301793e-17;
        const hx=hi(x),big=(hx&0x7fffffff)>=0x3FE59428;
        if(big){if(hx>>>31){x=-x;y=-y;}x=(PIO4-x)+(PIO4_LO-y);y=0.0;}
        const z=x*x,w=z*z;
        let r=T[1]+w*(T[3]+w*(T[5]+w*(T[7]+w*(T[9]+w*T[11]))));
        let v=z*(T[2]+w*(T[4]+w*(T[6]+w*(T[8]+w*(T[10]+w*T[12])))));
        const s=z*x;
        r=y+z*(s*(r+v)+y)+s*T[0];
        const w1=x+r;
        if(big){const s1=1.0-2.0*odd;v=s1-2.0*(x+(r-w1*w1/(w1+s1)));return hx>>>31?-v:v;}
        if(odd===0)return w1;
        const w0=setLo(w1,0);v=r-(w0-x);
        const a=-1.0/w1,a0=setLo(a,0);
        return a0+a*(1.0+a0*w0+a0*v);
    };
    const INIT_JK=[3,4,4,6];
    const IPIO2=[0xA2F983,0x6E4E44,0x1529FC,0x2757D1,0xF534DD,0xC0DB62,0x95993C,0x439041,0xFE5163,
        0xABDEBB,0xC561B7,0x246E3A,0x424DD2,0xE00649,0x2EEA09,0xD1921C,0xFE1DEB,0x1CB129,
        0xA73EE8,0x8235F5,0x2EBB44,0x84E99C,0x7026B4,0x5F7E41,0x3991D6,0x398353,0x39F49C,
        0x845F8B,0xBDF928,0x3B1FF8,0x97FFDE,0x05980F,0xEF2F11,0x8B5A0A,0x6D1F6D,0x367ECF,
        0x27CB09,0xB74F46,0x3F669E,0x5FEA2D,0x7527BA,0xC7EBE5,0xF17B3D,0x0739F7,0x8A5292,
        0xEA6BFB,0x5FB11F,0x8D5D08,0x560330,0x46FC7B,0x6BABF0,0xCFBC20,0x9AF436,0x1DA9E3,
        0x91615E,0xE61B08,0x659985,0x5F14A0,0x68408D,0xFFD880,0x4D7327,0x310606,0x1556CA,
        0x73A8C9,0x60E27B,0xC08C6B];
    const PIO2=[1.57079625129699707031e+00,7.54978941586159635335e-08,5.39030252995776476554e-15,
        3.28200341580791294123e-22,1.27065575308067607349e-29,1.22933308981111328932e-36,
        2.73370053816464559624e-44,2.16741683877804819444e-51];
    // `y` gets the result; `prec` is 1 here (a double's two pieces).
    const remPio2Large=(x,y,e0,prec)=>{
        const x1p24=words(0x41700000,0),x1p_24=words(0x3e700000,0);
        const nx=x.length,f=new Array(20).fill(0),fq=new Array(20).fill(0),q=new Array(20).fill(0),iq=new Array(20).fill(0);
        let fw,n,ih,z;
        const jk=INIT_JK[prec],jp=jk,jx=nx-1;
        let jv=Math.trunc((e0-3)/24);if(jv<0)jv=0;
        let q0=e0-24*(jv+1);
        let j=jv-jx;const m=jx+jk;
        for(let i=0;i<=m;i++){f[i]=j<0?0:IPIO2[j];j++;}
        for(let i=0;i<=jk;i++){fw=0;for(let j=0;j<=jx;j++)fw+=x[j]*f[jx+i-j];q[i]=fw;}
        let jz=jk;
        for(;;){
            let i=0;z=q[jz];
            for(let j=jz;j>=1;j--){fw=Math.trunc(x1p_24*z);iq[i]=Math.trunc(z-x1p24*fw);z=q[j-1]+fw;i++;}
            z=scalbn(z,q0);z-=8.0*Math.floor(z*0.125);
            n=Math.trunc(z);z-=n;ih=0;
            if(q0>0){i=iq[jz-1]>>(24-q0);n+=i;iq[jz-1]-=i<<(24-q0);ih=iq[jz-1]>>(23-q0);}
            else if(q0===0)ih=iq[jz-1]>>23;
            else if(z>=0.5)ih=2;
            if(ih>0){
                n+=1;let carry=0;
                for(let i=0;i<jz;i++){const j=iq[i];if(carry===0){if(j!==0){carry=1;iq[i]=0x1000000-j;}}else iq[i]=0xffffff-j;}
                if(q0>0){if(q0===1)iq[jz-1]&=0x7fffff;else if(q0===2)iq[jz-1]&=0x3fffff;}
                if(ih===2){z=1-z;if(carry!==0)z-=scalbn(1,q0);}
            }
            if(z===0){
                let j=0;for(let i=jz-1;i>=jk;i--)j|=iq[i];
                if(j===0){
                    let k=1;while(iq[jk-k]===0)k++;
                    for(let i=jz+1;i<=jz+k;i++){f[jx+i]=IPIO2[jv+i];fw=0;for(let j=0;j<=jx;j++)fw+=x[j]*f[jx+i-j];q[i]=fw;}
                    jz+=k;continue;
                }
            }
            break;
        }
        if(z===0){jz-=1;q0-=24;while(iq[jz]===0){jz-=1;q0-=24;}}
        else{
            z=scalbn(z,-q0);
            if(z>=x1p24){fw=Math.trunc(x1p_24*z);iq[jz]=Math.trunc(z-x1p24*fw);jz+=1;q0+=24;iq[jz]=Math.trunc(fw);}
            else iq[jz]=Math.trunc(z);
        }
        fw=scalbn(1,q0);
        for(let i=jz;i>=0;i--){q[i]=fw*iq[i];fw*=x1p_24;}
        for(let i=jz;i>=0;i--){fw=0;let k=0;while(k<=jp&&k<=jz-i){fw+=PIO2[k]*q[i+k];k++;}fq[jz-i]=fw;}
        fw=0;for(let i=jz;i>=0;i--)fw+=fq[i];
        y[0]=ih===0?fw:-fw;
        fw=fq[0]-fw;for(let i=1;i<=jz;i++)fw+=fq[i];
        y[1]=ih===0?fw:-fw;
        return n&7;
    };
    const remPio2=x=>{
        const TO_INT=1.5/2.2204460492503131e-16,INV_PIO2=6.36619772367581382433e-01,
            PIO2_1=1.57079632673412561417e+00,PIO2_1T=6.07710050650619224932e-11,
            PIO2_2=6.07710050630396597660e-11,PIO2_2T=2.02226624879595063154e-21,
            PIO2_3=2.02226624871116645580e-21,PIO2_3T=8.47842766036889956997e-32;
        const x1p24=words(0x41700000,0);
        const h=hi(x),sign=h>>>31,ix=h&0x7fffffff;
        const medium=()=>{
            const fn=(x*INV_PIO2+TO_INT)-TO_INT,n=Math.trunc(fn);
            let r=x-fn*PIO2_1,w=fn*PIO2_1T,y0=r-w;
            const ex=ix>>>20;
            if(ex-((hi(y0)>>>20)&0x7ff)>16){
                let t=r;w=fn*PIO2_2;r=t-w;w=fn*PIO2_2T-((t-r)-w);y0=r-w;
                if(ex-((hi(y0)>>>20)&0x7ff)>49){t=r;w=fn*PIO2_3;r=t-w;w=fn*PIO2_3T-((t-r)-w);y0=r-w;}
            }
            return [n,y0,(r-y0)-w];
        };
        const near=k=>{
            if(sign===0){const z=x-k*PIO2_1,y0=z-k*PIO2_1T;return [k,y0,(z-y0)-k*PIO2_1T];}
            const z=x+k*PIO2_1,y0=z+k*PIO2_1T;return [-k,y0,(z-y0)+k*PIO2_1T];
        };
        if(ix<=0x400f6a7a){
            if((ix&0xfffff)===0x921fb)return medium();
            return near(ix<=0x4002d97c?1:2);
        }
        if(ix<=0x401c463b){
            if(ix<=0x4015fdbc){if(ix===0x4012d97c)return medium();return near(3);}
            if(ix===0x401921fb)return medium();
            return near(4);
        }
        if(ix<0x413921fb)return medium();
        if(ix>=0x7ff00000){const y0=x-x;return [0,y0,y0];}
        let z=words((hi(x)&0x000fffff)|((0x3ff+23)<<20),lo(x));
        const tx=[0,0,0];
        for(let i=0;i<2;i++){tx[i]=Math.trunc(z);z=(z-tx[i])*x1p24;}
        tx[2]=z;
        let i=2;while(i!==0&&tx[i]===0)i--;
        const ty=[0,0,0];
        const n=remPio2Large(tx.slice(0,i+1),ty,(ix>>20)-(0x3ff+23),1);
        return sign?[-n,-ty[0],-ty[1]]:[n,ty[0],ty[1]];
    };
    const sin=x=>{
        const ix=hi(x)&0x7fffffff;
        if(ix<=0x3fe921fb){if(ix<0x3e500000)return x;return kSin(x,0,0);}
        if(ix>=0x7ff00000)return x-x;
        const [n,y0,y1]=remPio2(x);
        switch(n&3){case 0:return kSin(y0,y1,1);case 1:return kCos(y0,y1);case 2:return -kSin(y0,y1,1);default:return -kCos(y0,y1);}
    };
    const cos=x=>{
        const ix=hi(x)&0x7fffffff;
        if(ix<=0x3fe921fb){if(ix<0x3e46a09e&&Math.trunc(x)===0)return 1;return kCos(x,0);}
        if(ix>=0x7ff00000)return x-x;
        const [n,y0,y1]=remPio2(x);
        switch(n&3){case 0:return kCos(y0,y1);case 1:return -kSin(y0,y1,1);case 2:return -kCos(y0,y1);default:return kSin(y0,y1,1);}
    };
    const tan=x=>{
        const ix=hi(x)&0x7fffffff;
        if(ix<=0x3fe921fb){if(ix<0x3e400000)return x;return kTan(x,0,0);}
        if(ix>=0x7ff00000)return x-x;
        const [n,y0,y1]=remPio2(x);
        return kTan(y0,y1,n&1);
    };
    const exp=x=>{
        const HALF=[0.5,-0.5],LN2HI=6.93147180369123816490e-01,LN2LO=1.90821492927058770002e-10,
            INVLN2=1.44269504088896338700e+00,P1=1.66666666666666019037e-01,P2=-2.77777777770155933842e-03,
            P3=6.61375632143793436117e-05,P4=-1.65339022054652515390e-06,P5=4.13813679705723846039e-08;
        const x1p1023=words(0x7fe00000,0);
        let hx=hi(x);const sign=hx>>>31;hx&=0x7fffffff;
        if(hx>=0x4086232b){
            if(Number.isNaN(x))return x;
            if(x>709.782712893383973096)return x*x1p1023;
            if(x< -708.39641853226410622&&x< -745.13321910194110842)return 0;
        }
        let k,hi1,lo1;
        if(hx>0x3fd62e42){
            k=hx>=0x3ff0a2b2?Math.trunc(INVLN2*x+HALF[sign]):1-sign-sign;
            hi1=x-k*LN2HI;lo1=k*LN2LO;x=hi1-lo1;
        }else if(hx>0x3e300000){k=0;hi1=x;lo1=0;}
        else return 1+x;
        const xx=x*x,c=x-xx*(P1+xx*(P2+xx*(P3+xx*(P4+xx*P5)))),y=1+(x*c/(2-c)-lo1+hi1);
        return k===0?y:scalbn(y,k);
    };
    const expm1=x=>{
        const O_THRESHOLD=7.09782712893383973096e+02,LN2_HI=6.93147180369123816490e-01,LN2_LO=1.90821492927058770002e-10,
            INVLN2=1.44269504088896338700e+00,Q1=-3.33333333333331316428e-02,Q2=1.58730158725481460165e-03,
            Q3=-7.93650757867487942473e-05,Q4=4.00821782732936239552e-06,Q5=-2.01099218183624371326e-07;
        const h=hi(x),hx=h&0x7fffffff,sign=h>>>31;
        let hi1,lo1,k,c,t,y;
        if(hx>=0x4043687A){
            if(Number.isNaN(x))return x;
            if(sign)return -1;
            if(x>O_THRESHOLD)return x*words(0x7fe00000,0);
        }
        if(hx>0x3fd62e42){
            if(hx<0x3FF0A2B2){
                if(sign===0){hi1=x-LN2_HI;lo1=LN2_LO;k=1;}else{hi1=x+LN2_HI;lo1=-LN2_LO;k=-1;}
            }else{
                k=Math.trunc(INVLN2*x+(sign?-0.5:0.5));t=k;hi1=x-t*LN2_HI;lo1=t*LN2_LO;
            }
            x=hi1-lo1;c=(hi1-x)-lo1;
        }else if(hx<0x3c900000)return x;
        else{c=0;k=0;}
        const hfx=0.5*x,hxs=x*hfx,r1=1+hxs*(Q1+hxs*(Q2+hxs*(Q3+hxs*(Q4+hxs*Q5))));
        t=3-r1*hfx;
        let e=hxs*((r1-t)/(6-x*t));
        if(k===0)return x-(x*e-hxs);
        e=x*(e-c)-c;e-=hxs;
        if(k===-1)return 0.5*(x-e)-0.5;
        if(k===1){if(x< -0.25)return -2*(e-(x+0.5));return 1+2*(x-e);}
        const twopk=words(((0x3ff+k)<<20)>>>0,0);
        if(k<0||k>56){
            y=x-e+1;
            y=k===1024?y*2*words(0x7fe00000,0):y*twopk;
            return y-1;
        }
        const uf=words(((0x3ff-k)<<20)>>>0,0);
        return k<20?(x-e+(1-uf))*twopk:(x-(e+uf)+1)*twopk;
    };
    const expo2=x=>{
        const kln2=words(0x40962066,0x151add8b),scale=words(((0x3ff+1021)<<20)>>>0,0);
        return exp(x-kln2)*scale*scale;
    };
    const LG1=6.666666666666735130e-01,LG2=3.999999999940941908e-01,LG3=2.857142874366239149e-01,
        LG4=2.222219843214978396e-01,LG5=1.818357216161805012e-01,LG6=1.531383769920937332e-01,
        LG7=1.479819860511658591e-01;
    // The reduction `log`, `log2` and `log10` share: `x = 2^k (1 + f)`, or the
    // answer when there is one without it.
    const logReduce=x=>{
        let h=hi(x),l=lo(x),k=0;
        if(h<0x00100000||(h>>>31)){
            if(((h&0x7fffffff)|l)===0)return {done:-1/(x*x)};
            if(h>>>31)return {done:(x-x)/0};
            k-=54;x*=words(0x43500000,0);h=hi(x);l=lo(x);
        }else if(h>=0x7ff00000)return {done:x};
        else if(h===0x3ff00000&&l===0)return {done:0};
        h=(h+(0x3ff00000-0x3fe6a09e))>>>0;
        k+=(h>>>20)-0x3ff;
        h=(h&0x000fffff)+0x3fe6a09e;
        return {k,f:words(h,l)-1};
    };
    const log=x=>{
        const r0=logReduce(x);if('done' in r0)return r0.done;
        const {k,f}=r0,LN2_HI=6.93147180369123816490e-01,LN2_LO=1.90821492927058770002e-10;
        const hfsq=0.5*f*f,s=f/(2+f),z=s*s,w=z*z,t1=w*(LG2+w*(LG4+w*LG6)),t2=z*(LG1+w*(LG3+w*(LG5+w*LG7))),r=t2+t1,dk=k;
        return s*(hfsq+r)+dk*LN2_LO-hfsq+f+dk*LN2_HI;
    };
    const log2=x=>{
        const r0=logReduce(x);if('done' in r0)return r0.done;
        const {k,f}=r0,IVLN2HI=1.44269504072144627571e+00,IVLN2LO=1.67517131648865118353e-10;
        const hfsq=0.5*f*f,s=f/(2+f),z=s*s;let w=z*z;
        const t1=w*(LG2+w*(LG4+w*LG6)),t2=z*(LG1+w*(LG3+w*(LG5+w*LG7))),r=t2+t1;
        const hi1=setLo(f-hfsq,0),lo1=f-hi1-hfsq+s*(hfsq+r);
        let valHi=hi1*IVLN2HI,valLo=(lo1+hi1)*IVLN2LO+lo1*IVLN2HI;
        const y=k;w=y+valHi;valLo+=(y-w)+valHi;valHi=w;
        return valLo+valHi;
    };
    const log10=x=>{
        const r0=logReduce(x);if('done' in r0)return r0.done;
        const {k,f}=r0,IVLN10HI=4.34294481878168880939e-01,IVLN10LO=2.50829467116452752298e-11,
            LOG10_2HI=3.01029995663611771306e-01,LOG10_2LO=3.69423907715893078616e-13;
        const hfsq=0.5*f*f,s=f/(2+f),z=s*s;let w=z*z;
        const t1=w*(LG2+w*(LG4+w*LG6)),t2=z*(LG1+w*(LG3+w*(LG5+w*LG7))),r=t2+t1;
        const hi1=setLo(f-hfsq,0),lo1=f-hi1-hfsq+s*(hfsq+r);
        let valHi=hi1*IVLN10HI;const dk=k,y=dk*LOG10_2HI;
        let valLo=dk*LOG10_2LO+(lo1+hi1)*IVLN10LO+lo1*IVLN10HI;
        w=y+valHi;valLo+=(y-w)+valHi;valHi=w;
        return valLo+valHi;
    };
    const pow=(x,y)=>{
        const BP=[1.0,1.5],DP_H=[0.0,5.84962487220764160156e-01],DP_L=[0.0,1.35003920212974897128e-08],
            TWO53=9007199254740992.0,HUGE=1.0e300,TINY=1.0e-300,
            L1=5.99999999999994648725e-01,L2=4.28571428578550184252e-01,L3=3.33333329818377432918e-01,
            L4=2.72728123808534006489e-01,L5=2.30660745775561754067e-01,L6=2.06975017800338417784e-01,
            P1=1.66666666666666019037e-01,P2=-2.77777777770155933842e-03,P3=6.61375632143793436117e-05,
            P4=-1.65339022054652515390e-06,P5=4.13813679705723846039e-08,
            LG2=6.93147180559945286227e-01,LG2_H=6.93147182464599609375e-01,LG2_L=-1.90465429995776804525e-09,
            OVT=8.0085662595372944372e-017,CP=9.61796693925975554329e-01,CP_H=9.61796700954437255859e-01,
            CP_L=-7.02846165095275826516e-09,IVLN2=1.44269504088896338700e+00,IVLN2_H=1.44269502162933349609e+00,
            IVLN2_L=1.92596299112661746887e-08;
        let t1,t2;
        const hx=hi(x)|0,lx=lo(x),hy=hi(y)|0,ly=lo(y);
        let ix=hx&0x7fffffff;const iy=hy&0x7fffffff;
        if((iy|ly)===0)return 1;
        if(hx===0x3ff00000&&lx===0)return 1;
        if(ix>0x7ff00000||(ix===0x7ff00000&&lx!==0)||iy>0x7ff00000||(iy===0x7ff00000&&ly!==0))return x+y;
        let yisint=0,k,j;
        if(hx<0){
            if(iy>=0x43400000)yisint=2;
            else if(iy>=0x3ff00000){
                k=(iy>>20)-0x3ff;
                if(k>20){j=ly>>>(52-k);if(((j<<(52-k))|0)===(ly|0))yisint=2-(j&1);}
                else if(ly===0){j=iy>>(20-k);if((j<<(20-k))===iy)yisint=2-(j&1);}
            }
        }
        if(ly===0){
            if(iy===0x7ff00000){
                if(((ix-0x3ff00000)|lx)===0)return 1;
                if(ix>=0x3ff00000)return hy>=0?y:0;
                return hy>=0?0:-y;
            }
            if(iy===0x3ff00000)return hy>=0?x:1/x;
            if(hy===0x40000000)return x*x;
            if(hy===0x3fe00000&&hx>=0)return Math.sqrt(x);
        }
        let ax=Math.abs(x);
        if(lx===0&&(ix===0x7ff00000||ix===0||ix===0x3ff00000)){
            let z=ax;
            if(hy<0)z=1/z;
            if(hx<0){if(((ix-0x3ff00000)|yisint)===0)z=(z-z)/(z-z);else if(yisint===1)z=-z;}
            return z;
        }
        let s=1;
        if(hx<0){if(yisint===0)return (x-x)/(x-x);if(yisint===1)s=-1;}
        if(iy>0x41e00000){
            if(iy>0x43f00000){
                if(ix<=0x3fefffff)return hy<0?HUGE*HUGE:TINY*TINY;
                if(ix>=0x3ff00000)return hy>0?HUGE*HUGE:TINY*TINY;
            }
            if(ix<0x3fefffff)return hy<0?s*HUGE*HUGE:s*TINY*TINY;
            if(ix>0x3ff00000)return hy>0?s*HUGE*HUGE:s*TINY*TINY;
            const t=ax-1,w=(t*t)*(0.5-t*(0.3333333333333333333333-t*0.25)),u=IVLN2_H*t,v=t*IVLN2_L-w*IVLN2;
            t1=setLo(u+v,0);t2=v-(t1-u);
        }else{
            let n=0;
            if(ix<0x00100000){ax*=TWO53;n-=53;ix=hi(ax)|0;}
            n+=(ix>>20)-0x3ff;j=ix&0x000fffff;
            let kk;ix=j|0x3ff00000;
            if(j<=0x3988E)kk=0;else if(j<0xBB67A)kk=1;else{kk=0;n+=1;ix-=0x00100000;}
            ax=setHi(ax,ix>>>0);
            let u=ax-BP[kk],v=1/(ax+BP[kk]);
            const ss=u*v,sH=setLo(ss,0);
            let tH=words((((ix>>>1)|0x20000000)+0x00080000+(kk<<18))>>>0,0);
            let tL=ax-(tH-BP[kk]);
            const sL=v*((u-sH*tH)-sH*tL);
            let s2=ss*ss;
            let r=s2*s2*(L1+s2*(L2+s2*(L3+s2*(L4+s2*(L5+s2*L6)))));
            r+=sL*(sH+ss);s2=sH*sH;
            tH=setLo(3+s2+r,0);tL=r-((tH-3)-s2);
            u=sH*tH;v=sL*tH+tL*ss;
            const pH=setLo(u+v,0),pL=v-(pH-u),zH=CP_H*pH,zL=CP_L*pH+pL*CP+DP_L[kk],t=n;
            t1=setLo(((zH+zL)+DP_H[kk])+t,0);t2=zL-(((t1-t)-DP_H[kk])-zH);
        }
        const y1=setLo(y,0),pL=(y-y1)*t1+y*t2;
        let pH=y1*t1;
        let z=pL+pH;
        j=hi(z)|0;const i0=lo(z)|0;
        if(j>=0x40900000){
            if(((j-0x40900000)|i0)!==0)return s*HUGE*HUGE;
            if(pL+OVT>z-pH)return s*HUGE*HUGE;
        }else if((j&0x7fffffff)>=0x4090cc00){
            if((((j>>>0)-0xc090cc00)|i0)!==0)return s*TINY*TINY;
            if(pL<=z-pH)return s*TINY*TINY;
        }
        const i=j&0x7fffffff;
        k=(i>>20)-0x3ff;
        let n=0;
        if(i>0x3fe00000){
            n=j+(0x00100000>>(k+1));
            k=((n&0x7fffffff)>>20)-0x3ff;
            const t=words((n&~(0x000fffff>>k))>>>0,0);
            n=((n&0x000fffff)|0x00100000)>>(20-k);
            if(j<0)n=-n;
            pH-=t;
        }
        const t=setLo(pL+pH,0),u=t*LG2_H,v=(pL-(t-pH))*LG2+t*LG2_L;
        z=u+v;
        const w=v-(z-u),tt=z*z,tt1=z-tt*(P1+tt*(P2+tt*(P3+tt*(P4+tt*P5)))),r=(z*tt1)/(tt1-2)-(w+z*w);
        z=1-(r-z);
        j=hi(z)|0;j=(j+(n<<20))|0;
        z=(j>>20)<=0?scalbn(z,n):setHi(z,j>>>0);
        return s*z;
    };
    const cbrt=x=>{
        const B1=715094163,B2=696219795,P0=1.87595182427177009643,P1=-1.88497979543377169875,
            P2=1.621429720105354466140,P3=-0.758397934778766047437,P4=0.145996192886612446982;
        let hx=hi(x)&0x7fffffff;
        if(hx>=0x7ff00000)return x+x;
        if(hx<0x00100000){
            hx=hi(x*words(0x43500000,0))&0x7fffffff;
            if(hx===0)return x;
            hx=Math.floor(hx/3)+B2;
        }else hx=Math.floor(hx/3)+B1;
        let t=words(((hi(x)&0x80000000)|hx)>>>0,0);
        let r=(t*t)*(t/x);
        t=t*((P0+r*(P1+r*P2))+((r*r)*r)*(P3+r*P4));
        // Round t away from zero to 23 bits: (bits + 0x80000000) & 0xffffffffc0000000.
        let h=hi(t),l=lo(t);
        if(l>=0x80000000)h=(h+1)>>>0;
        t=words(h,((l+0x80000000)>>>0)&0xc0000000);
        const s=t*t;r=x/s;const w=t+t;r=(r-t)/(w+r);
        return t+t*r;
    };
    const ATANHI=[4.63647609000806093515e-01,7.85398163397448278999e-01,9.82793723247329054082e-01,1.57079632679489655800e+00];
    const ATANLO=[2.26987774529616870924e-17,3.06161699786838301793e-17,1.39033110312309984516e-17,6.12323399573676603587e-17];
    const AT=[3.33333333333329318027e-01,-1.99999999998764832476e-01,1.42857142725034663711e-01,
        -1.11111104054623557880e-01,9.09088713343650656196e-02,-7.69187620504482999495e-02,
        6.66107313738753120669e-02,-5.83357013379057348645e-02,4.97687799461593236017e-02,
        -3.65315727442169155270e-02,1.62858201153657823623e-02];
    const atan=x=>{
        const h=hi(x),sign=h>>>31,ix=h&0x7fffffff;
        if(ix>=0x44100000){
            if(Number.isNaN(x))return x;
            const z=ATANHI[3]+words(0,0x03800000);
            return sign?-z:z;
        }
        let id;
        if(ix<0x3fdc0000){if(ix<0x3e400000)return x;id=-1;}
        else{
            x=Math.abs(x);
            if(ix<0x3ff30000){
                if(ix<0x3fe60000){x=(2*x-1)/(2+x);id=0;}else{x=(x-1)/(x+1);id=1;}
            }else if(ix<0x40038000){x=(x-1.5)/(1+1.5*x);id=2;}
            else{x=-1/x;id=3;}
        }
        const z=x*x,w=z*z;
        const s1=z*(AT[0]+w*(AT[2]+w*(AT[4]+w*(AT[6]+w*(AT[8]+w*AT[10])))));
        const s2=w*(AT[1]+w*(AT[3]+w*(AT[5]+w*(AT[7]+w*AT[9]))));
        if(id<0)return x-x*(s1+s2);
        const r=ATANHI[id]-(x*(s1+s2)-ATANLO[id]-x);
        return sign?-r:r;
    };
    const atan2=(y,x)=>{
        const PI=3.1415926535897931160E+00,PI_LO=1.2246467991473531772E-16;
        if(Number.isNaN(x)||Number.isNaN(y))return x+y;
        let ix=hi(x);const lx=lo(x);let iy=hi(y);const ly=lo(y);
        if((((ix-0x3ff00000)>>>0)|lx)===0)return atan(y);
        const m=((iy>>>31)&1)|((ix>>>30)&2);
        ix&=0x7fffffff;iy&=0x7fffffff;
        if((iy|ly)===0)return m<2?y:m===2?PI:-PI;
        if((ix|lx)===0)return m&1?-PI/2:PI/2;
        if(ix===0x7ff00000){
            if(iy===0x7ff00000)return [PI/4,-PI/4,3*PI/4,-3*PI/4][m];
            return [0,-0,PI,-PI][m];
        }
        if(((ix+(64<<20))>>>0)<iy||iy===0x7ff00000)return m&1?-PI/2:PI/2;
        const z=(m&2)&&((iy+(64<<20))>>>0)<ix?0:atan(Math.abs(y/x));
        switch(m){case 0:return z;case 1:return -z;case 2:return PI-(z-PI_LO);default:return (z-PI_LO)-PI;}
    };
    const PIO2_HI=1.57079632679489655800e+00,PIO2_LO=6.12323399573676603587e-17;
    const R=z=>{
        const PS0=1.66666666666666657415e-01,PS1=-3.25565818622400915405e-01,PS2=2.01212532134862925881e-01,
            PS3=-4.00555345006794114027e-02,PS4=7.91534994289814532176e-04,PS5=3.47933107596021167570e-05,
            QS1=-2.40339491173441421878e+00,QS2=2.02094576023350569471e+00,QS3=-6.88283971605453293030e-01,
            QS4=7.70381505559019352791e-02;
        const p=z*(PS0+z*(PS1+z*(PS2+z*(PS3+z*(PS4+z*PS5))))),q=1+z*(QS1+z*(QS2+z*(QS3+z*QS4)));
        return p/q;
    };
    const asin=x=>{
        const hx=hi(x),ix=hx&0x7fffffff;
        if(ix>=0x3ff00000){
            if(((ix-0x3ff00000)|lo(x))===0)return x*PIO2_HI+words(0x38700000,0);
            return 0/(x-x);
        }
        if(ix<0x3fe00000){
            if(ix<0x3e500000&&ix>=0x00100000)return x;
            return x+x*R(x*x);
        }
        const z=(1-Math.abs(x))*0.5,s=Math.sqrt(z),r=R(z);
        if(ix>=0x3fef3333)x=PIO2_HI-(2*(s+s*r)-PIO2_LO);
        else{
            const f=setLo(s,0),c=(z-f*f)/(s+f);
            x=0.5*PIO2_HI-(2*s*r-(PIO2_LO-2*c)-(0.5*PIO2_HI-2*f));
        }
        return hx>>>31?-x:x;
    };
    const acos=x=>{
        const x1p_120f=words(0x38700000,0);
        const hx=hi(x),ix=hx&0x7fffffff;
        if(ix>=0x3ff00000){
            if(((ix-0x3ff00000)|lo(x))===0)return hx>>>31?2*PIO2_HI+x1p_120f:0;
            return 0/(x-x);
        }
        if(ix<0x3fe00000){
            if(ix<=0x3c600000)return PIO2_HI+x1p_120f;
            return PIO2_HI-(x-(PIO2_LO-x*R(x*x)));
        }
        if(hx>>>31){
            const z=(1+x)*0.5,s=Math.sqrt(z),w=R(z)*s-PIO2_LO;
            return 2*(PIO2_HI-(s+w));
        }
        const z=(1-x)*0.5,s=Math.sqrt(z),df=setLo(s,0),c=(z-df*df)/(s+df),w=R(z)*s+c;
        return 2*(df+w);
    };
    const sinh=x=>{
        const h=hi(x)>>>31?-0.5:0.5,absx=Math.abs(x),w=hi(absx);
        if(w<0x40862e42){
            const t=expm1(absx);
            if(w<0x3ff00000){
                if(w<0x3ff00000-(26<<20))return x;
                return h*(2*t-t*t/(t+1));
            }
            return h*(t+t/(t+1));
        }
        return 2*h*expo2(absx);
    };
    const cosh=x=>{
        x=Math.abs(x);
        const w=hi(x);
        if(w<0x3fe62e42){
            if(w<0x3ff00000-(26<<20))return 1;
            const t=expm1(x);
            return 1+t*t/(2*(1+t));
        }
        if(w<0x40862e42){const t=exp(x);return 0.5*(t+1/t);}
        return expo2(x);
    };
    const tanh=x=>{
        const sign=hi(x)>>>31;x=Math.abs(x);
        const w=hi(x);let t;
        if(w>0x3fe193ea){
            if(w>0x40340000)t=1-0/x;
            else{t=expm1(2*x);t=1-2/(t+2);}
        }else if(w>0x3fd058ae){t=expm1(2*x);t=t/(t+2);}
        else if(w>=0x00100000){t=expm1(-2*x);t=-t/(t+2);}
        else t=x;
        return sign?-t:t;
    };
    return {sin,cos,tan,asin,acos,atan,atan2,exp,log,log2,log10,pow,cbrt,sinh,cosh,tanh};
})();
// `/` of `Float`: by zero (either sign), the run-time error.
function floatText(x){
    if(Number.isNaN(x))return 'NaN';
    if(x===Infinity)return 'inf';
    if(x===-Infinity)return '-inf';
    if(x===0)return Object.is(x,-0)?'-0':'0';
    const sign=x<0?'-':'',[m,e]=Math.abs(x).toExponential().split('e');
    let digits=m.replace('.','');const exp=Number(e);
    // Of two shortest digit strings exactly as near, JavaScript takes the
    // even one and Rust the larger: take the larger.
    const last=digits.charCodeAt(digits.length-1)-48;
    if(last%2===0&&last<9){
        const up=digits.slice(0,-1)+String(last+1);
        if(Number(up[0]+'.'+up.slice(1)+'e'+exp)===Math.abs(x)&&floatTie(Math.abs(x),BigInt(digits),exp-digits.length+1))digits=up;
    }
    if(exp>=digits.length-1)return sign+digits+'0'.repeat(exp-digits.length+1);
    if(exp<0)return sign+'0.'+'0'.repeat(-exp-1)+digits;
    return sign+digits.slice(0,exp+1)+'.'+digits.slice(exp+1);
}
// Whether `x` is exactly halfway between `d·10^p` and `(d+1)·10^p`.
function floatTie(x,d,p){
    const v=new DataView(new ArrayBuffer(8));v.setFloat64(0,x);
    const bits=v.getBigUint64(0),be=Number((bits>>52n)&0x7ffn);
    let m=bits&0xfffffffffffffn,e=be-1075;
    if(be===0)e=-1074;else m|=0x10000000000000n;
    // 2·m·2^e = (2d+1)·10^p, both sides scaled to integers.
    let l=2n*m,r=2n*d+1n;
    if(e>=0)l<<=BigInt(e);else r<<=BigInt(-e);
    if(p>=0)r*=10n**BigInt(p);else l*=10n**BigInt(-p);
    return l===r;
}
// `float_of_text`: a number as a literal writes one, with an optional `-`.
function floatOfText(t){
    return /^-?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?$/.test(t)?some(Number(t)):none();
}
function floatBuiltin(name,vs){
    const a=unref(vs[0]),b=unref(vs[1]);
    switch(name){
        case 'Float::of_i64':return Number(a);
        case 'I64::of_float':{
            const t=Math.trunc(a);
            if(!(t>=-9223372036854775808&&t<9223372036854775808))throw new Error('the number is too large');
            return BigInt(t);
        }
        case 'Float::of_text':return floatOfText(a);
        case 'Text::of_float':return floatText(a);
        case 'Float::bits':{if(a!==a)return 0x7ff8000000000000n;const v=new DataView(new ArrayBuffer(8));v.setFloat64(0,a);return v.getBigUint64(0);}
        case 'Float::of_bits':{const v=new DataView(new ArrayBuffer(8));v.setBigUint64(0,a);return v.getFloat64(0);}
        case 'Float::is_nan':return Number.isNaN(a);
        case 'Float::abs':return Math.abs(a);
        case 'Float::floor':return Math.floor(a);
        case 'Float::ceil':return Math.ceil(a);
        case 'Float::trunc':return Math.trunc(a);
        // Halves away from zero; `Math.round` takes them towards +∞.
        case 'Float::round':{
            if(!Number.isFinite(a))return a;
            const t=Math.trunc(a);
            return Math.abs(a-t)>=0.5?t+(a<0?-1:1):t;
        }
        case 'Float::sqrt':return Math.sqrt(a);
        case 'Float::cbrt':return floatMath.cbrt(a);
        case 'Float::exp':return floatMath.exp(a);
        case 'Float::ln':return floatMath.log(a);
        case 'Float::log2':return floatMath.log2(a);
        case 'Float::log10':return floatMath.log10(a);
        case 'Float::pow':return floatMath.pow(a,b);
        case 'Float::sin':return floatMath.sin(a);
        case 'Float::cos':return floatMath.cos(a);
        case 'Float::tan':return floatMath.tan(a);
        case 'Float::asin':return floatMath.asin(a);
        case 'Float::acos':return floatMath.acos(a);
        case 'Float::atan':return floatMath.atan(a);
        case 'Float::atan2':return floatMath.atan2(a,b);
        case 'Float::sinh':return floatMath.sinh(a);
        case 'Float::cosh':return floatMath.cosh(a);
        case 'Float::tanh':return floatMath.tanh(a);
        case 'Float::of_float32':return a;
    }
    throw new Error('unknown builtin '+name);
}
// `Float32` is a number too, always one `Math.fround` gives back: `+ - * /`
// and `sqrt` of two such, rounded once more by `Math.fround`, are IEEE 754's
// binary32 results (the binary64 result is never a double-rounding tie).
function float32Builtin(name,vs){
    const a=unref(vs[0]),b=unref(vs[1]),f=Math.fround;
    switch(name){
        case 'Float32::of_float':return f(a);
        case 'Float32::bits':{if(a!==a)return 0x7fc00000n;const v=new DataView(new ArrayBuffer(4));v.setFloat32(0,a);return BigInt(v.getUint32(0));}
        case 'Float32::of_bits':{const v=new DataView(new ArrayBuffer(4));v.setUint32(0,Number(a));return v.getFloat32(0);}
        case 'Float32::is_nan':return Number.isNaN(a);
        case 'Float32::abs':return Math.abs(a);
        case 'Float32::floor':return Math.floor(a);
        case 'Float32::ceil':return Math.ceil(a);
        case 'Float32::trunc':return Math.trunc(a);
        case 'Float32::round':return floatBuiltin('Float::round',[a]);
        case 'Float32::sqrt':return f(Math.sqrt(a));
        case 'Float32::pow':return f(floatMath.pow(a,b));
        case 'Float32::atan2':return f(floatMath.atan2(a,b));
        default:return f(floatBuiltin('Float::'+name.slice(9),[a]));
    }
}
const identity=x=>x;
// `t` as `Debug` writes it between its quotes, as Rust's `{:?}` of a `str` does.
const escapeDebugUnprinted=/^[\p{Cc}\p{Cf}\p{Cn}\p{Co}\p{Cs}\p{Zl}\p{Zp}\p{Mn}\p{Me}]$|^[\p{Zs}]$/u;
function escapeDebug(t){let out='';for(const c of t){const n=c.codePointAt(0);if(c==='\\')out+='\\\\';else if(c==='"')out+='\\"';else if(c==='\n')out+='\\n';else if(c==='\r')out+='\\r';else if(c==='\t')out+='\\t';else if(n===0)out+='\\0';else if(n!==32&&escapeDebugUnprinted.test(c))out+='\\u{'+n.toString(16)+'}';else out+=c;}return out;}
const reference=(get,set)=>({ref:true,get,set});
// Only a reference's own `ref` marks it: reading `ref` on the value behind it
// would run a getter a host put on `Object.prototype`.
const isReference=x=>x!==null&&(typeof x==='object'||typeof x==='function')&&Object.hasOwn(x,'ref')&&x.ref;
const unref=x=>{if(stableData.has(x))stableAggregate(x);while(isReference(x))x=x.get();return x;};
const copyArray=Array,copyArrayPrototype=Array.prototype,copyArrayMap=Array.prototype.map;
function copyValue(value) {
    const retained=retainedGraphs.get(value);
    if(retained){retained.owners++;return value;}
    if(sharedData.has(value))return value;
    if(retainedLeaves.has(value)){value.retain?.();return value;}
    return copyWithin(value,new WeakSet());
}
function copyWithin(value,active) {
    // Keep per-occurrence copies/retains, without spending the host stack on
    // recursive data. Objects snapshot entries before visiting children;
    // ordinary arrays visit present indexes lazily, preserving sparse maps.
    const parents=[];
    const next=frame=>{
        if(frame.array){while(frame.index<frame.length){const key=frame.index++;if(key in frame.source)return [key,frame.source[key]];}return null;}
        return frame.index<frame.entries.length?frame.entries[frame.index++]:null;
    };
    let result;
    copy:for(;;){
        const retained=retainedGraphs.get(value);
        if(retained){retained.owners++;result=value;}
        else {
            if(stableData.has(value))stableAggregate(value);
            if(provenanceIsArray(value)&&!ordinaryArrayMethods(value))forgetStableData();
            // Sharing a proof made before the intrinsics changed would trust them.
            if(stableAggregate(value)&&(sharedData.has(value)||ordinaryArrayMethods(value.fields)))result=share(value);
            else if(value?.copy)result=value.copy();
            else if(value?.retain){value.retain();result=value;}
            else if(!value||typeof value!=='object'||value.ref||value.shared||value.resource)result=value;
            else if(Array.isArray(value)&&(Array!==copyArray||Object.getPrototypeOf(value)!==copyArrayPrototype||value.map!==copyArrayMap||Object.hasOwn(value,'constructor')||value.constructor!==copyArray||Array[Symbol.species]!==copyArray)){
                if(active.has(value))throw new Error('cyclic JavaScript value cannot be copied');
                active.add(value);
                forgetStableData();
                try{result=value.map(item=>copyWithin(item,active));}finally{active.delete(value);forgetStableData();}
            }
            else{
                if(active.has(value))throw new Error('cyclic JavaScript value cannot be copied');
                const array=Array.isArray(value),length=array?value.length:0,frame=array
                    ?{source:value,target:new Array(length),array:true,length,index:0}
                    :{source:value,target:{},array:false,entries:Object.entries(value),index:0};
                const child=next(frame);
                if(child){active.add(value);frame.key=child[0];parents.push(frame);value=child[1];continue;}
                result=frame.target;
                if(stableAggregate(value))stableData.add(result);
            }
        }
        while(parents.length){
            const frame=parents[parents.length-1];
            Object.defineProperty(frame.target,frame.key,{value:result,writable:true,enumerable:true,configurable:true});
            const child=next(frame);
            if(child){frame.key=child[0];value=child[1];continue copy;}
            parents.pop();active.delete(frame.source);result=frame.target;
            if(stableAggregate(frame.source))stableData.add(result);
        }
        return result;
    }
}
function borrowedRef(value){
    if(!value?.retain)return value;
    const ref={ref:true,wire:value,projection:value.projection,get:()=>value.get(),set:x=>value.set(x),cloneOwned:value.cloneOwned?()=>value.cloneOwned():undefined,operation:value.operation?(...args)=>value.operation(...args):undefined,project:value.project?(...args)=>value.project(...args):undefined};
    const state=stableReferences.get(value);
    if(state)trackStableReference(ref,state);
    return ref;
}
function trackStableReference(ref,state){
    const set=ref.set;
    ref.set=value=>{state.enabled=false;return set(value);};
    stableReferences.set(ref,state);
    return ref;
}
function stableState(valid){
    const epoch=stableEpoch;
    const state={enabled:true,valid:()=>state.enabled&&epoch===stableEpoch&&valid()};
    return state;
}
function immutableSlotReference(slot,ref){
    if(!slot.immutable||slot.shared||!stableAggregate(slot.value))return ref;
    let state=stableSlots.get(slot);
    if(!state){const value=slot.value;state=stableState(()=>slot.value===value&&stableAggregate(value));stableSlots.set(slot,state);}
    return trackStableReference(ref,state);
}
function dereference(value,copy){return copy&&value?.cloneOwned?value.cloneOwned():copy?copyValue(unref(value)):unref(value);}
// A borrow an extern call returned and only copied from: nothing holds the
// view after the copy, so its loan of the owner ends here.
function exportBorrow(value){
    // A generic return may contain a deeply recursive aggregate. Retain views
    // without using the host stack, and rebuild only ancestors of a changed
    // field; ordinary values keep their representation and ownership. Private
    // generated-graph provenance also proves generic values borrow-free. Host
    // crossings and field writes revoke that proof; unknown graphs still walk.
    const parents=[];
    let result;
    for(;;){
        if(value?.wire)result=copyValue(value.wire);
        else if(value?.projection){
            const {root,path}=value.projection,owner=root.wire??(root.retain?root:null);
            if(owner){const retained=copyValue(owner),ref=projectionRef(retained,path);ref.temporary=true;ref.retain=()=>retained.retain();ref.release=()=>retained.release();result=ref;}
            else result=value;
        }else if(stableAggregate(value)||retainedGraphs.has(value))result=value;
        else if(value?.fields?.length){
            parents.push({value,fields:value.fields,index:0,changed:null});
            value=value.fields[0];continue;
        }else result=value;
        for(;;){
            if(parents.length===0)return result;
            const parent=parents[parents.length-1];
            if(result!==parent.fields[parent.index]){
                parent.changed??=parent.fields.slice();
                parent.changed[parent.index]=result;
            }
            if(++parent.index<parent.fields.length){value=parent.fields[parent.index];break;}
            result=parent.changed?{...parent.value,fields:parent.changed}:parent.value;
            parents.pop();
        }
    }
}
// Paths share their prefixes. Mutable and unknown roots stay live; references
// to proven immutable owned graphs cache their selection until invalidated.
// A root getter may produce a copy, so writes return that whole copy once.
function fieldRef(base,key) {
    const projection=base.projection??{root:base,path:null};
    const ref=projectionRef(projection.root,{parent:projection.path,key});
    const state=stableReferences.get(base);
    if(state?.valid()){
        const value=unref(base);
        if(stableAggregate(value)){
            const fields=value.fields;
            if(!fields)return ref;
            const selected=fields[typeof key==='number'?key:value.names.indexOf(key)],live=ref.get;
            ref.get=()=>state.valid()?selected:live();
            trackStableReference(ref,state);
        }
    }
    return ref;
}
function projectionRef(root,path) {
    const keys=()=>{const out=[];for(let p=path;p;p=p.parent)out.push(p.key);return out;};
    const ref=reference(()=>{
        const path=keys();let value=unref(root);
        for(let i=path.length-1;i>=0;i--){const key=path[i];value=value.fields[typeof key==='number'?key:value.names.indexOf(key)];}
        return value;
    },replacement=>{
        const path=keys(),parents=[];let value=unref(root);
        for(let i=path.length-1;i>=0;i--){const key=path[i],index=typeof key==='number'?key:value.names.indexOf(key),child=value.fields[index];parents.push([value,index,child]);value=child;}
        for(let i=parents.length-1;i>=0;i--){
            const [parent,index,previous]=parents[i];
            if(retainedGraphs.has(parent)){
                const fields=[];
                for(let j=0;j<parent.fields.length;j++)Object.defineProperty(fields,j,{value:j===index?replacement:copyValue(parent.fields[j]),writable:true,enumerable:true,configurable:true});
                replacement=generatedAggregate({...parent,fields},fields,ordinaryArrayMethods(fields));
                if(i===0)dropValue(parent);
                continue;
            }
            if(sharedData.has(parent)){const fields=parent.fields.slice();fields[index]=replacement;replacement={...parent,fields};continue;}
            if(retainedGraphs.has(previous))dropValue(previous);
            stableData.delete(parent);parent.fields[index]=replacement;replacement=parent;
        }
        root.set(replacement);
    });
    ref.projection={root,path};
    return ref;
}
function thawReference(ref){
    const target=ref.get();
    // A projection borrows an edge owned by its parent. Rebuilding that
    // parent releases the edge; materializing the host copy must not do so.
    const value=retainedGraphs.has(target)&&ref.projection?.path?copyValue(target):target;
    const mutable=thaw(value);
    if(mutable!==target)ref.set(mutable);
}
function placeRef(c,id,path,borrowed) {
    const slot=envGet(c.env,id);
    let ref=borrowed&&slot.value?.ref?borrowedRef(slot.value):immutableSlotReference(slot,reference(()=>slot.value,v=>{slot.value=v;}));
    for(const key of path){const base=ref;if(base.project){ref=base.project(key,true);ref.temporary=true;if(base.temporary)base.release();continue;}ref=fieldRef(base,key);}
    return ref;
}
function borrowPlace(id,path,borrowed) {return (c,k)=>more(()=>k(c,placeRef(c,id,path,borrowed)));}
const some=v=>construct('Some',[null],[v],[0],false,'Option');
const none=()=>construct('None',[],[],[],false,'Option');
const ok=v=>construct('Ok',[null],[v],[0],false,'Result');
const err=v=>construct('Err',[null],[v],[0],false,'Result');
const pair=(a,b)=>construct('Pair',['fst','snd'],[a,b],[0,1],true,'Pair');
const vec=items=>({kind:'Vec',items});
// A `List` of millions of cells (`bytes_to_list`) is made as `construct`
// makes each cell, but the arrays it checks are its own: the intrinsics are
// checked once for the whole list, not once per cell, and the cells share
// one frozen array of field names, as cells that are shared already do.
// Each byte value once, not once per byte of a long `Bytes`.
const byteValues=Array.from({length:256},(_,i)=>BigInt(i));
const listNames=Object.freeze([null,null]);
function list(items){
    let out=construct('Nil',[],[],[],false,'List');
    if(!ordinaryArrayMethods(items)||!ordinaryArrayMethods([])){
        for(let i=items.length-1;i>=0;i--)out=construct('Cons',[null,null],[items[i],out],[0,1],false,'List');
        return out;
    }
    for(let i=items.length-1;i>=0;i--){
        const item=items[i];
        const value={owner:'List',tag:'Cons',names:listNames,fields:[item,out],struct:false};
        if(stableMember(item)&&stableData.has(out))stableData.add(value);
        out=value;
    }
    return out;
}
// A `Signal`: raised once, never lowered; a `wait` the host answers resumes when it is.
function signal(){return retainedLeaf({kind:'Signal',shared:true,raised:false,waiters:[]});}
function raise(s){if(s.raised)return;s.raised=true;const ws=s.waiters;s.waiters=[];for(const w of ws)w();}
function waitSignal(s,done){
    const inputs=s.inputs??[s];
    if(s.raised){done();return;}
    const wake=()=>{for(const input of inputs)input.waiters=input.waiters.filter(w=>w!==wake);done();};
    for(const input of inputs)input.waiters.push(wake);
}

// The host's answer to `Os::entry(what, args)` (`Entry::run` of the prelude): `options.entry`
// says what the run is for (`mode`: 'test', 'list', or a run of the program; `names`, the tests to select) and takes
// each event of the report (`report(fields)`).
function entryCall(options,what,args){
    const config=options.entry??{},state=options.entryState??(options.entryState={mains:0,found:[],failures:new Map()});
    const report=fields=>{if(config.report)config.report(fields);};
    const stop=why=>{report(['error',why]);return ['stop',why];};
    if(what==='found'&&args[0]==='main'){state.mains++;report(['main']);return [];}
    if(what==='found'&&args[0]==='test'){state.found.push(args[1]);report(['found',args[1]]);return [];}
    // A test that failed is called again while retries are left.
    if(what==='failed'){const failed=(state.failures.get(args[0])??0)+1;state.failures.set(args[0],failed);if(failed<=(config.retries??0)){report(['retry',...args]);return ['retry'];}}
    if(what==='start'||what==='passed'||what==='failed'){report([what,...args]);return [];}
    if(what==='check')return config.check?config.check(args[0]):['error','check-unavailable','0','0','0','0','this host cannot check a file'];
    if(what!=='plan')return [];
    if(config.mode!=='test'&&config.mode!=='list'){
        if(state.mains===1){report(['planned']);return ['main'];}
        if(state.mains===0)return stop('the module performs no `main`: there is no program to run');
        return stop('the module performs `main` '+state.mains+' times: a program has one `main`');
    }
    const seen=new Set();
    for(const name of state.found){if(seen.has(name))return stop('two tests are named `'+name+'`: a test\'s name is its own');seen.add(name);}
    const names=config.names,selected=state.found.filter(name=>names===undefined||names===null||names.includes(name));
    for(const name of selected)report(['selected',name]);
    report(['planned']);
    return config.mode==='list'?[]:['test',...selected];
}
function listItems(value){const out=[];for(let v=value;v.tag==='Cons';v=v.fields[1])out.push(v.fields[0]);return out;}
// The slots and their marks are sparse arrays: a slot nobody put in is a hole, and so is a mark still
// the one `new` was given, so a new `Slots` costs nothing until it is written.
function slotsCap(n){n=unref(n);if(n>4294967295n)throw new Error('Slots: capacity '+n+' exceeds the host memory');return Number(n);}
function slotsNew(cap,state,mark){
    const n=slotsCap(cap);
    return {kind:'Slots',items:new Array(n),marks:new Array(n),state,vacant:mark,
        // A dropped `Slots` drops only the slots in use.
        release(){const items=this.items;this.items=[];this.marks=[];items.forEach(x=>{if(x!==undefined)dropValue(x);});}};
}
function slotsMark(a,i){const m=a.marks[Number(i)];return m===undefined?a.vacant:m;}
function indexRef(v,i){return reference(()=>unref(v).items[Number(i)],x=>{unref(v).items[Number(i)]=x;});}
function inRange(v,i){return i>=0n&&i<BigInt(unref(v).items.length);}
// The UTF-8 bytes of the texts read last. Byte access walks a text by index, so
// encoding it again on each access would make the walk quadratic. Callers only read.
const textByteCache=new Map(),textEncoder=new TextEncoder();
function textBytes(text){
    let bytes=textByteCache.get(text);
    if(bytes===undefined){
        bytes=textEncoder.encode(text);
        if(textByteCache.size>=16)textByteCache.delete(textByteCache.keys().next().value);
        textByteCache.set(text,bytes);
    }
    return bytes;
}
// `Bytes`: shared and read-only, so a slice is a view on the same storage.
const bytesValue=bytes=>({kind:'Bytes',shared:true,bytes});
const utf8Decoder=new TextDecoder('utf-8',{fatal:true,ignoreBOM:true});
// The exchanges of `Os::http_*` of a run, by the run's options: each task and
// each offloaded call runs with a host of its own, but all share the options.
const HTTP=new WeakMap();
// A header value as a host's HTTP API gives it (one code unit per byte), read
// as UTF-8; `null` when it is not, so that it does not reach the program changed.
function headerText(v){try{return utf8Decoder.decode(Uint8Array.from(String(v),ch=>ch.charCodeAt(0)&255));}catch{return null;}}
// The builtins that only compute on plain values, for both forms.
function pureBuiltin(name,vs){
    if(name.startsWith('Float32::'))return float32Builtin(name,vs);
    if(name.startsWith('Float::')||name.endsWith('::of_float'))return floatBuiltin(name,vs);
    const a=unref(vs[0]),n=vs[1],b=unref(n);
    switch(name){
        case 'Text::byte':{const bytes=textBytes(a);return n>=0n&&n<BigInt(bytes.length)?some(BigInt(bytes[Number(n)])):none();}
        case 'Text::slice':{
            const bytes=textBytes(a),end=vs[2];
            if(n<0n||end<n||end>BigInt(bytes.length))return none();
            try{return some(new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(bytes.slice(Number(n),Number(end))));}catch{return none();}
        }
        case 'Text::escape_debug':return escapeDebug(a);
        case 'Text::of_code_point':return a<0n||a>0x10ffffn||(a>=0xd800n&&a<=0xdfffn)?none():some(String.fromCodePoint(Number(a)));
        case 'Text::of_utf8':try{return some(new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(Uint8Array.from(listItems(a),Number)));}catch{return none();}
        case 'I8::of_i64':return checked(a,-128n,127n);
        case 'I16::of_i64':return checked(a,-32768n,32767n);
        case 'U16::of_u64':return checked(a,0n,65535n);
        case 'U64::of_u16':return a;
        case 'I64::of_i8':case 'I64::of_i16':case 'I64::of_i32':case 'I64::of_u64':return checked(a,-9223372036854775808n,9223372036854775807n);
        case 'I32::of_i64':return checked(a,-2147483648n,2147483647n);
        case 'Nat::of_u64':return a;case 'U64::of_i64':case 'U64::of_u32':case 'U64::of_u8':case 'U64::of_uhost':case 'U64::of_nat':return checked(a,0n,18446744073709551615n);
        case 'U32::of_u64':return checked(a,0n,4294967295n);
        case 'UHost::succ_below':return a+1n;
        case 'UHost::pred_nz':return a-1n;
        case 'UHost::add_within':return a+b;
        case 'UHost::sub':return a-b;
        case 'UHost::of_u64_below':return a;
        case 'U8::of_u64':return checked(a,0n,255n);
        // The bitwise operations, of a 32- or 64-bit word.
        case 'U32::and':return a&b;
        case 'U32::or':return a|b;
        case 'U32::xor':return a^b;
        case 'U32::shl':return BigInt.asUintN(32,a<<(b%32n));
        case 'U32::shr':return a>>(b%32n);
        case 'U32::rotl':{const s=b%32n;return BigInt.asUintN(32,(a<<s)|(a>>((32n-s)%32n)));}
        case 'U32::rotr':{const s=b%32n;return BigInt.asUintN(32,(a>>s)|(a<<((32n-s)%32n)));}
        case 'U64::and':return a&b;
        case 'U64::or':return a|b;
        case 'U64::xor':return a^b;
        case 'U64::shl':return BigInt.asUintN(64,a<<(b%64n));
        case 'U64::shr':return a>>(b%64n);
        case 'U64::rotl':{const s=b%64n;return BigInt.asUintN(64,(a<<s)|(a>>((64n-s)%64n)));}
        case 'U64::rotr':{const s=b%64n;return BigInt.asUintN(64,(a>>s)|(a<<((64n-s)%64n)));}
        case 'U64::wrapping_add':return BigInt.asUintN(64,a+b);
        case 'U64::wrapping_sub':return BigInt.asUintN(64,a-b);
        case 'U64::wrapping_mul':return BigInt.asUintN(64,a*b);
    }
}
function builtin(name,args) {
    return values(args,(c,vs,k)=>{
        const done=v=>more(()=>k(c,v));
        if(vs[0]?.operation&&['replace','Buf::push','Vec::push','Vec::pop','Vec::len','Slice::len','Vec::as_slice','Vec::as_mut_slice','Vec::clear','Vec::truncate','Vec::get','Vec::get_mut','Slice::get','Vec::last_mut','Vec::swap_within'].includes(name)){
            const result=vs[0].operation(name,vs.slice(1));
            return result?.abiEffect?route(c,result.abiEffect,'zero',[],k):done(result);
        }
        if(name==='clone'&&vs[0]?.cloneOwned)return done(vs[0].cloneOwned());
        const a=unref(vs[0]),b=unref(vs[1]),n=vs[1];
        switch(name) {
            case 'clone':return done(copyValue(a));
            case 'replace':vs[0].set(vs[1]);return done(a);
            case 'Buf::new':return done({kind:'Buf',text:''});
            case 'Buf::of':case 'Buf::clone':return done({kind:'Buf',text:a.text??a});
            case 'Buf::push':a.text+=b;return done(null);
            case 'Text::of':return done(a.text);
            case 'Vec::new':return done(vec([]));
            case 'Vec::push':a.items.push(vs[1]);return done(null);
            case 'Vec::pop':return done(a.items.length?some(a.items.pop()):none());
            case 'Vec::len':case 'Slice::len':case 'Array::len':return done(BigInt(a.items.length));
            case 'Vec::as_slice':case 'Vec::as_mut_slice':return done(vs[0]);
            case 'Vec::clear':a.items.length=0;return done(null);
            case 'Vec::truncate':if(n<BigInt(a.items.length))a.items.length=Number(n);return done(null);
            case 'Vec::get':case 'Vec::get_mut':case 'Slice::get':return done(inRange(a,n)?some(indexRef(vs[0],n)):none());
            case 'Vec::last_mut':return done(a.items.length?some(indexRef(vs[0],BigInt(a.items.length-1))):none());
            case 'Vec::swap_within':if(!inRange(a,n)||!inRange(a,vs[2]))return done(false);[a.items[Number(n)],a.items[Number(vs[2])]]=[a.items[Number(vs[2])],a.items[Number(n)]];return done(true);
            // `Slots`: slots that may be uninitialised (`undefined`) and their marks. The proofs are erased,
            // so nothing is checked; a slot is occupied when the policy says so, and a taken slot is emptied
            // so that a drop only drops the used ones (`slotsRelease`).
            case 'Slots::new':return done(slotsNew(vs[0],vs[1],vs[2]));
            case 'Slots::state':return done(copyValue(a.state));
            case 'Slots::cap':return done(BigInt(a.items.length));
            // `mark` is total in the model: past the capacity it is the vacant mark.
            case 'Slots::mark':{const i=unref(vs[1]);if(!inRange(a,i))return done(copyValue(a.vacant));return done(copyValue(slotsMark(a,i)));}
            case 'Slots::get':case 'Slots::get_mut':{const i=unref(vs[1]);if(!inRange(a,i))throw new Error('Slots: index out of range');const j=Number(i);if(a.items[j]===undefined)throw new Error('Slots: slot '+j+' holds no value');return done(indexRef(vs[0],i));}
            case 'Slots::put':{const i=unref(vs[1]);if(!inRange(a,i))throw new Error('Slots: index out of range');const j=Number(i);if(a.items[j]!==undefined)dropValue(a.items[j]);a.items[j]=vs[3];a.marks[j]=vs[2];a.state=vs[4];return done(null);}
            case 'Slots::take':{const i=unref(vs[1]);if(!inRange(a,i))throw new Error('Slots: index out of range');const j=Number(i);if(a.items[j]===undefined)throw new Error('Slots: slot '+j+' holds no value');const x=a.items[j];a.items[j]=undefined;a.marks[j]=vs[2];a.state=vs[3];return done(x);}
            // Growing keeps each old mark as it is: materialise holes under the
            // old vacant before the vacant template changes, then fill the new
            // slots with the new mark.
            case 'Slots::resize':{const n=slotsCap(vs[1]);const oldVacant=a.vacant,oldLen=a.items.length;for(let i=0;i<Math.min(oldLen,n);i++)if(a.marks[i]===undefined)a.marks[i]=copyValue(oldVacant);for(let i=n;i<a.items.length;i++)if(a.items[i]!==undefined)dropValue(a.items[i]);a.items.length=n;a.marks.length=n;a.vacant=vs[2];for(let i=oldLen;i<n;i++)a.marks[i]=copyValue(vs[2]);a.state=vs[3];return done(null);}
            case 'Vec::into_list':case 'Array::to_list':return done(list(a.items.map(copyValue)));
            case 'Vec::into_array':{const items=a.items;a.items=[];return done(shareArray({kind:'Array',items}));}
            case 'Array::of_list':return done(shareArray({kind:'Array',items:listItems(a)}));
            // Every value goes on the heap: a region keeps nothing, and a place says nothing.
            case 'Region::new':case 'Region::place':case 'RcRegion::new':case 'RcRegion::place':case 'RcPlace::heap':return done(null);
            // `Secret`: shared like its content; `shown` does not print it.
            case 'secret':return done({kind:'Secret',shared:true,value:a});
            case 'expose':return done(a.value);
            case 'Bytes::of_list':return done(bytesValue(Uint8Array.from(listItems(a),Number)));
            case 'Bytes::to_list':return done(list(Array.from(a.bytes,x=>byteValues[x])));
            case 'Bytes::len':return done(BigInt(a.bytes.length));
            case 'Bytes::find':{const c=vs[1],s=vs[2],e=vs[3],l=BigInt(a.bytes.length),m=e<l?e:l;for(let i=s;i<m;i++){if(BigInt(a.bytes[Number(i)])===c)return done(i);}return done(e);}
            case 'Bytes::get':return done(n>=0n&&n<BigInt(a.bytes.length)?some(BigInt(a.bytes[Number(n)])):none());
            case 'Bytes::slice':{const end=vs[2];return done(n<0n||end<n||end>BigInt(a.bytes.length)?none():some(bytesValue(a.bytes.subarray(Number(n),Number(end)))));}
            case 'Bytes::concat':{const out=new Uint8Array(a.bytes.length+b.bytes.length);out.set(a.bytes);out.set(b.bytes,a.bytes.length);return done(bytesValue(out));}
            case 'Syn::same_declaration':return done(a===b);
            case 'Bytes::eq':return done(a.bytes.length===b.bytes.length&&a.bytes.every((x,i)=>x===b.bytes[i]));
            case 'Bytes::of_text':return done(bytesValue(textEncoder.encode(a)));
            case 'Text::of_bytes':try{return done(some(utf8Decoder.decode(a.bytes)));}catch{return done(none());}
            // Arrays are shared, so a write copies.
            case 'Array::set':{if(!inRange(a,n))return done(a);const items=a.items.slice();items[Number(n)]=vs[2];return done(shareArray({kind:'Array',items}));}
            case 'Array::get':return done(inRange(a,n)?some(copyValue(a.items[Number(n)])):none());
            case 'Text::byte':case 'Text::slice':case 'Text::of_code_point':case 'Text::escape_debug':case 'Text::of_utf8':case 'I64::of_i32':case 'I64::of_u64':case 'I32::of_i64':case 'Nat::of_u64':case 'U64::of_i64':case 'U64::of_u32':case 'U64::of_u8':case 'U64::of_uhost':case 'UHost::succ_below':case 'UHost::pred_nz':case 'UHost::add_within':case 'UHost::sub':case 'UHost::of_u64_below':case 'U64::of_nat':case 'U32::of_u64':case 'U8::of_u64':case 'U32::and':case 'U32::or':case 'U32::xor':case 'U32::shl':case 'U32::shr':case 'U32::rotl':case 'U32::rotr':case 'U64::and':case 'U64::or':case 'U64::xor':case 'U64::shl':case 'U64::shr':case 'U64::rotl':case 'U64::rotr':case 'U64::wrapping_add':case 'U64::wrapping_sub':case 'U64::wrapping_mul':return done(pureBuiltin(name,vs));
            case 'Float::of_i64':case 'I64::of_float':case 'Float::of_text':case 'Text::of_float':case 'Float::bits':case 'Float::of_bits':case 'Float::is_nan':case 'Float::abs':case 'Float::floor':case 'Float::ceil':case 'Float::trunc':case 'Float::round':case 'Float::sqrt':case 'Float::cbrt':case 'Float::exp':case 'Float::ln':case 'Float::log2':case 'Float::log10':case 'Float::pow':case 'Float::sin':case 'Float::cos':case 'Float::tan':case 'Float::asin':case 'Float::acos':case 'Float::atan':case 'Float::atan2':case 'Float::sinh':case 'Float::cosh':case 'Float::tanh':return done(floatBuiltin(name,vs));
            case 'Float32::of_float':case 'Float::of_float32':case 'Float32::bits':case 'Float32::of_bits':case 'Float32::is_nan':case 'Float32::abs':case 'Float32::floor':case 'Float32::ceil':case 'Float32::trunc':case 'Float32::round':case 'Float32::sqrt':case 'Float32::cbrt':case 'Float32::exp':case 'Float32::ln':case 'Float32::log2':case 'Float32::log10':case 'Float32::pow':case 'Float32::sin':case 'Float32::cos':case 'Float32::tan':case 'Float32::asin':case 'Float32::acos':case 'Float32::atan':case 'Float32::atan2':case 'Float32::sinh':case 'Float32::cosh':case 'Float32::tanh':return done(pureBuiltin(name,vs));
            case 'words':return done(list(a.split(/\p{White_Space}+/u).filter(Boolean)));
            case 'Ref::new':return done(retainedLeaf({kind:'Ref',shared:true,value:a}));
            case 'Ref::get':return done(copyValue(a.value));
            case 'Ref::set':a.value=vs[1];return done(null);
            case 'Weak::of':return done(retainedLeaf({kind:'Weak',shared:true,target:new WeakRef(a)}));
            case 'Weak::get':{const r=a.target.deref();return done(r===undefined?none():some(r));}
            case 'Atomic::new':return done(retainedLeaf({kind:'Atomic',shared:true,value:a}));
            case 'Atomic::load':return done(a.value);
            case 'Atomic::store':a.value=b;return done(null);
            case 'Atomic::fetch_add':{const old=a.value;a.value=BigInt.asUintN(64,old+b);return done(old);}
            case 'Mutex::new':return done(retainedLeaf({kind:'Mutex',shared:true,value:a,full:true,waiting:[]}));
            // A place in the mutex's line: its signal is raised when the content is handed to it.
            case 'Mutex::claim':{checkPoisoned(a);const s=signal();if(a.full&&!a.waiting.length){a.full=false;s.handed=a.value;a.value=undefined;raise(s);}else a.waiting.push(s);return done(s);}
            case 'Mutex::take_claimed':{checkPoisoned(a);const v=b.handed;b.handed=undefined;tookMutex(a);return done(v);}
            case 'Mutex::withdraw':{checkPoisoned(a);const i=a.waiting.indexOf(b);if(i>=0)a.waiting.splice(i,1);const v=b.handed;const had='handed' in b&&v!==undefined;b.handed=undefined;if(had)tookMutex(a);return done(had?some(v):none());}
            case 'Mutex::put':a.taker=null;if(a.waiting.length){const s=a.waiting.shift();s.handed=b;raise(s);}else{a.value=b;a.full=true;}return done(null);
            // The lock is held by the guard until it is dropped, which gives the content back.
            case 'MutexGuard::claimed':{checkPoisoned(a);const v=b.handed;b.handed=undefined;tookMutex(a);let held=true;const g={kind:'MutexGuard',resource:true,value:v,release(){if(!held)return;held=false;const x=g.value;g.value=undefined;if(a.poisoned)return;a.taker=null;if(a.waiting.length){const s=a.waiting.shift();s.handed=x;raise(s);}else{a.value=x;a.full=true;}}};return done(g);}
            case 'MutexGuard::get':case 'MutexGuard::get_mut':return done(reference(()=>a.value,x=>{a.value=x;}));
            case 'Pending::ready':return done({kind:'Pending',resource:true,value:a});
            // There at once, answering false: the request that follows waits on the event loop.
            case 'Os::tcp_ready':case 'Os::tls_ready':return done({kind:'Pending',resource:true,value:false});
            // Sends all of the bytes as `os_tcp_write` does, answering how many.
            case 'Os::tcp_send':{
                const f=c.host.options.os_tcp_write;if(!f)return done(err('host does not provide os_tcp_write'));
                const v=unref(vs[2]);const bs=unref(vs[1]).bytes.slice();
                return Promise.resolve().then(()=>f(Number(a),bs,v.tag==='Some'?v.fields[0]:null)).then(
                    r=>more(()=>k(c,ok(r===null||r===undefined?none():some(BigInt(bs.length))))),
                    e=>more(()=>k(c,err(e.message??String(e)))));
            }
            // What may take a while runs as a task of its own, whose result the caller waits for.
            case 'Os::offload':
            case 'pending_spawn':{const task={held:new Set()},outer=TASK,start=(d,t)=>a(d,[],t),promise=c.host.instance.tasks?driveIn(start,c.host.instance.tasks,task):drive(start,c.host.show,c.host.externs,c.host.options,task);TASK=outer;const p={kind:'Pending',resource:true,promise,ready:false};const host=c.host;promise.then(()=>{p.ready=true;},e=>{p.ready=true;reportTaskFailure(host,e);});return done(p);}
            // A task still running gets a turn before the answer, so a loop that polls lets it go on.
            case 'Pending::is_ready':if(!a.promise||a.ready)return done(true);return new Promise(resolve=>setTimeout(()=>resolve(more(()=>k(c,a.ready))),0));
            case 'Signal::listen':return done(a);
            case 'Signal::fresh':return done(signal());
            case 'Signal::raise':raise(a);return done(null);
            case 'Signal::is_raised':return done(a.raised);
            case 'Signal::either':{
                const inputs=[...new Set([...(a.inputs??[a]),...(b.inputs??[b])])];
                return done({kind:'Signal',shared:true,inputs,get raised(){return inputs.some(s=>s.raised);}});
            }
            case 'Pending::signal':{const s=signal();if(!a.promise||a.ready)raise(s);else a.promise.then(()=>raise(s),()=>raise(s));return done(s);}
            case 'Pending::take':return a.promise?a.promise.then(v=>more(()=>k(c,v))):done(a.value);
            case 'budget_value':return done({answer:'value',value:a});
            case 'info_more':return done({answer:'more',steps:b});
            case 'info_unbounded':return done({answer:'more',steps:null});
            case 'Os::args':return done(list(c.host.options.args??[]));
            case 'Os::entry':return done(list(entryCall(c.host.options,String(a),listItems(vs[1]).map(String))));
            case 'Os::print':case 'Os::eprint':{
                const f=c.host.options['os_'+name.slice(4)];if(!f)throw new Error('host does not provide os_'+name.slice(4));
                forgetStableData();try{f(a);}finally{forgetStableData();}return done(null);
            }
            case 'Os::read_file':case 'Os::write_file':case 'Os::read_bytes':case 'Os::write_bytes':case 'Os::read_under':case 'Os::read_bytes_under':case 'Os::create_dir':{
                const f=c.host.options['os_'+name.slice(4)];if(!f)throw new Error('host does not provide os_'+name.slice(4));
                // Bytes cross as a Uint8Array of their own: the host may keep or change it.
                const bytes=name==='Os::read_bytes'||name==='Os::read_bytes_under',args=name==='Os::write_bytes'?[unref(vs[0]),unref(vs[1]).bytes.slice()]:vs.map(unref);
                const back=v=>bytes?bytesValue(new Uint8Array(v??[])):(v??null);
                try {
                    forgetStableData();let value;try{value=f(...args);}finally{forgetStableData();}
                    if(value&&typeof value.then==='function'){
                        if(c.direct){Promise.resolve(value).catch(()=>{});throw new Error('a direct handler cannot await '+name);}
                        return Promise.resolve(value).then(v=>{forgetStableData();return more(()=>k(c,ok(back(v))));},e=>{forgetStableData();return more(()=>k(c,err(e.message??String(e))));});
                    }
                    return done(ok(back(value)));
                }catch(e){return done(err(e.message??String(e)));}
            }
            case 'Os::list_dir':case 'Os::remove':case 'Os::stat':case 'Os::read_link':case 'Os::write_new':case 'Os::move_path':case 'Os::set_mode':case 'Os::lock':case 'Os::copy_file':case 'Os::canonicalize':case 'Os::temp_dir':case 'Os::run':{
                const f=c.host.options['os_'+name.slice(4)];if(!f)return done(err('host does not provide os_'+name.slice(4)));
                let call;
                if(name==='Os::run'){const flat=listItems(vs[3]).map(String);const env=[];for(let i=0;i+1<flat.length;i+=2)env.push([flat[i],flat[i+1]]);call=()=>f(unref(vs[0]),listItems(vs[1]).map(String),unref(vs[2]),env,unref(vs[4]).bytes.slice());}
                else call=()=>f(...vs.map(unref));
                // The exit status (`null` when a signal ended it), standard output and standard error.
                const back=r=>{
                    if(name==='Os::list_dir')return list([...r].map(String).sort((x,y)=>x<y?-1:x>y?1:0));
                    if(name==='Os::stat')return list(r===null||r===undefined?[]:[String(r.kind),String(r.size??0),String(r.modified_ms??0),r.executable?'1':'0']);
                    if(name==='Os::read_link')return list(r===null||r===undefined?[]:[String(r)]);
                    if(name==='Os::lock')return BigInt(r);
                    if(name==='Os::canonicalize')return String(r);
                    if(name==='Os::temp_dir'){const dir=String(r);permissionGrantDir(c.host.options,dir);return dir;}
                    if(name==='Os::run')return pair(bytesValue(new Uint8Array(r.stdout??[])),list([r.status===null||r.status===undefined?'':String(r.status),String(r.stderr??'')]));
                    return null;
                };
                try{
                    forgetStableData();let value;try{value=call();}finally{forgetStableData();}
                    if(value&&typeof value.then==='function'){
                        if(c.direct){Promise.resolve(value).catch(()=>{});throw new Error('a direct handler cannot await '+name);}
                        return Promise.resolve(value).then(v=>{forgetStableData();return more(()=>k(c,ok(back(v))));},e=>{forgetStableData();return more(()=>k(c,err(e.message??String(e))));});
                    }
                    return done(ok(back(value)));
                }catch(e){return done(err(e.message??String(e)));}
            }
            case 'Os::read_stdin':{
                const f=c.host.options.os_read_stdin;if(!f)throw new Error('host does not provide os_read_stdin');
                return done(bytesValue(new Uint8Array(f(Number(unref(vs[0])))??[])));
            }
            case 'Os::on_shutdown':{const f=c.host.options.os_on_shutdown;if(f)f(()=>raise(a));return done(null);}
            case 'Os::flush':{const f=c.host.options.os_flush;if(f)f();return done(null);}
            case 'Os::read_line':{
                const f=c.host.options.os_read_line;if(!f)throw new Error('host does not provide os_read_line');
                const line=f();return done(line===null||line===undefined?none():some(String(line)));
            }
            case 'Os::env_names':return done(list(Object.keys(c.host.options.env??{}).sort()));
            case 'Os::env':{
                const env=c.host.options.env??{};const v=Object.prototype.hasOwnProperty.call(env,a)?env[a]:undefined;
                return done(v===undefined||v===null?none():some(String(v)));
            }
            case 'Os::wall_ms':return done(BigInt(Date.now()));
            case 'Os::monotonic_ns':return done(BigInt(Math.floor(performance.now()*1e6)));
            // `uhost` is the 32-bit word of JavaScript: a result outside it ends the run.
            case 'Os::uhost_add':case 'Os::uhost_sub':case 'Os::uhost_mul':case 'Os::uhost_of_u64':{
                const x=unref(vs[0]),y=vs.length>1?unref(vs[1]):0n;
                const r=name==='Os::uhost_add'?x+y:name==='Os::uhost_sub'?x-y:name==='Os::uhost_mul'?x*y:x;
                if(r<0n||r>0xFFFFFFFFn)throw new Error('the number is too large for a word of 32 bits ('+name.slice(4)+')');
                return done(r);
            }
            case 'Os::host_bits':return done(32n);
            // One seed for the whole run, new for each run.
            case 'Os::hash_seed_k0':case 'Os::hash_seed_k1':{
                const h=c.host;if(!h.hashSeed){const w=new BigUint64Array(2);globalThis.crypto.getRandomValues(w);h.hashSeed=w;}
                return done(h.hashSeed[name==='Os::hash_seed_k0'?0:1]);
            }
            case 'Os::sleep_pending':{const promise=new Promise(resolve=>setTimeout(()=>resolve(null),Number(a)));const p={kind:'Pending',resource:true,promise,ready:false};promise.then(()=>{p.ready=true;});return done(p);}
            // A host without file locks gives no `os_lock`, and so none is held to let go of.
            case 'Os::unlock':{const f=c.host.options.os_unlock;if(f)f(Number(unref(vs[0])));return done(null);}
            case 'Os::random':{const w=new BigUint64Array(1);globalThis.crypto.getRandomValues(w);return done(w[0]>>1n);}
            case 'Os::secure_random':{
                // getRandomValues fills at most 65536 bytes a call.
                try{const b=new Uint8Array(Number(a));for(let i=0;i<b.length;i+=65536)globalThis.crypto.getRandomValues(b.subarray(i,i+65536));return done(ok(bytesValue(b)));}
                catch(e){return done(err(e.message??String(e)));}
            }
            case 'Os::status':return done(/^[0-9]+$/.test(a)?BigInt(a):0n);
            case 'Os::check':{const t=permissionCheck(c.host.options,a,b);return done(t===null?none():some(t));}
            // With an address (not empty) the host gives `options.os_fetch_at(url,init,address)`:
            // the status, the body, then header names and values, or a Promise of them.
            case 'Os::fetch':{
                const address=unref(vs[2]);
                const flat=listItems(vs[3]).map(String);const headers=[];
                for(let i=0;i+1<flat.length;i+=2)headers.push([flat[i],flat[i+1]]);
                const init={method:a,headers,redirect:'manual'};const body=unref(vs[4]).bytes;if(body.length>0&&a!=='GET'&&a!=='HEAD')init.body=body.slice();
                if(address!==''){
                    const g=c.host.options.os_fetch_at;if(!g)return done(err('host does not provide os_fetch_at'));
                    return Promise.resolve().then(()=>g(b,init,address)).then(
                        ([items,got])=>more(()=>k(c,ok(pair(bytesValue(got),list(items.map(String)))))),
                        e=>more(()=>k(c,err(e.message??String(e)))));
                }
                const f=c.host.options.fetch??globalThis.fetch;if(!f)return done(err('host does not provide fetch'));
                return Promise.resolve().then(()=>f(b,init)).then(async r=>{
                    const out=[String(r.status)];let bad=null;
                    r.headers.forEach((v,n)=>{const t=headerText(v);if(t===null)bad??=n;else out.push(n,t);});
                    if(bad!==null)return more(()=>k(c,err('the value of the response header '+bad+' is not UTF-8')));
                    const got=new Uint8Array(await r.arrayBuffer());
                    return more(()=>k(c,ok(pair(bytesValue(got),list(out)))));
                },e=>more(()=>k(c,err(e.message??String(e)))));
            }
            // HTTP whose bodies go a piece at a time, over `options.fetch` (default
            // `globalThis.fetch`): a request body is a ReadableStream the writes fill
            // (`duplex: 'half'`); GET and HEAD send none, so they go at `http_finish`. The
            // response body is read with its reader. A body that breaks off is an error, and
            // closing a request before it is finished errors its stream, so the peer never
            // takes a cut body for a whole one. A connection to a fixed address needs
            // `options.os_fetch_at`, which answers whole bodies, so it is refused here.
            case 'Os::http_open':case 'Os::http_write':case 'Os::http_finish':case 'Os::http_read':case 'Os::http_close':{
                let t=HTTP.get(c.host.options);if(!t){t={next:0,m:new Map()};HTTP.set(c.host.options,t);}
                const deadline=v=>{v=unref(v);return v.tag==='Some'?v.fields[0]:null;};
                const back=p=>p.then(r=>more(()=>k(c,r)),e=>more(()=>k(c,err(e.message??String(e)))));
                // Waits for `p` until `d` (a bigint of `monotonic_clock`, or null): null when
                // it passed first.
                const until=(p,d)=>{if(d===null)return p;const ms=Number(d-BigInt(Math.floor(performance.now()*1e6)))/1e6;
                    return Promise.race([p,new Promise(r=>setTimeout(()=>r(null),Math.max(0,ms)))]);};
                if(name==='Os::http_open'){
                    if(unref(vs[2])!=='')return done(err('this host cannot stream an exchange to a fixed address'));
                    const f=c.host.options.fetch??globalThis.fetch;if(!f)return done(err('host does not provide fetch'));
                    const flat=listItems(vs[3]).map(String);const headers=[];
                    for(let i=0;i+1<flat.length;i+=2)headers.push([flat[i],flat[i+1]]);
                    const e={kind:'req',method:a,url:b,headers,f,ctl:null,res:null};
                    const init={method:a,headers,redirect:'manual'};
                    e.start=()=>Promise.resolve().then(()=>f(b,init));
                    if(a!=='GET'&&a!=='HEAD'){
                        init.body=new ReadableStream({start(ctl){e.ctl=ctl;}},{highWaterMark:1});init.duplex='half';
                        e.res=e.start();e.res.catch(()=>{});
                    }
                    const id=++t.next;t.m.set(id,e);return done(ok(BigInt(id)));
                }
                const id=Number(a);const e=t.m.get(id);
                if(name==='Os::http_close'){
                    t.m.delete(id);
                    if(e?.kind==='req'&&e.ctl){try{e.ctl.error(new Error('the request was closed before it was finished'));}catch{}}
                    if(e?.kind==='res'){try{e.reader.cancel();}catch{}}
                    return done(null);
                }
                if(name==='Os::http_write'){
                    if(e?.kind!=='req')return done(err('no such request'));
                    const bytes=unref(vs[1]).bytes.slice();
                    if(e.finished)return done(err('the request is finished'));
                    if(bytes.length===0)return done(ok(some(null)));
                    if(!e.ctl)return done(err('a '+e.method+' request has no body'));
                    try{e.ctl.enqueue(bytes);}catch(x){return done(err(x.message??String(x)));}
                    return done(ok(some(null)));
                }
                if(name==='Os::http_finish'){
                    if(e?.kind!=='req')return done(err('no such request'));
                    // A finish whose deadline passes leaves the request going, for the next
                    // to wait for again.
                    if(!e.finished){e.finished=true;if(e.ctl){try{e.ctl.close();}catch{}}e.res??=e.start();e.res.catch(()=>{});}
                    return back(until(e.res.then(r=>({r}),x=>({x})),deadline(vs[1])).then(got=>{
                        if(got===null)return ok(none());
                        t.m.delete(id);
                        if(got.x!==undefined)throw got.x;
                        const r=got.r;
                        const out=[];let bad=null;
                        r.headers.forEach((v,n)=>{const h=headerText(v);if(h===null)bad??=n;else out.push(n,h);});
                        if(bad!==null){try{r.body?.cancel();}catch{}return err('the value of the response header '+bad+' is not UTF-8');}
                        const body=++t.next;
                        t.m.set(body,{kind:'res',reader:r.body?r.body.getReader():null,rest:new Uint8Array(0),pend:null,done:null});
                        return ok(some(list([String(body),String(r.status),...out])));
                    }));
                }
                // Os::http_read
                if(e?.kind!=='res')return done(err('no such response'));
                const max=Math.min(Number(b),1<<20);
                const take=()=>{const n=Math.min(max,e.rest.length);const got=e.rest.slice(0,n);e.rest=e.rest.subarray(n);return ok(some(bytesValue(got)));};
                if(e.rest.length>0)return done(take());
                if(e.done!==null)return done(e.done===true?ok(some(bytesValue(new Uint8Array(0)))):err(e.done));
                if(max===0||!e.reader){if(!e.reader)e.done=true;return done(ok(some(bytesValue(new Uint8Array(0)))));}
                e.pend??=e.reader.read().then(r=>({r}),x=>({x}));
                return back(until(e.pend,deadline(vs[2])).then(got=>{
                    if(got===null)return ok(none());
                    e.pend=null;
                    if(got.x!==undefined){e.done='the response body broke off: '+(got.x?.message??String(got.x));return err(e.done);}
                    if(got.r.done){e.done=true;return ok(some(bytesValue(new Uint8Array(0))));}
                    e.rest=new Uint8Array(got.r.value);return take();
                }));
            }
            // The host gives `options.os_resolve(host)`: the addresses, a list or a Promise of one.
            case 'Os::resolve':{
                const f=c.host.options.os_resolve;if(!f)return done(err('host does not provide os_resolve'));
                const u=parseUrl(a);if(!u)return done(err('cannot resolve '+a));
                return Promise.resolve().then(()=>f(u.host.replace(/^\[|\]$/g,''))).then(
                    r=>more(()=>k(c,ok(list([...new Set(r.map(String))])))),
                    e=>more(()=>k(c,err(e.message??String(e)))));
            }
            // Byte streams: the host gives `options.os_tcp_listen(address)` ([number, address
            // bound]), `os_tcp_accept(listener, deadline)` and `os_tcp_connect(address, deadline)`
            // ([number, local, peer]), `os_tcp_read(stream, max, deadline)` (a Uint8Array, empty
            // at the end), `os_tcp_write(stream, bytes, deadline)`, `os_tcp_shutdown(stream, how)`
            // (0 read, 1 write, 2 both), `os_tcp_close(stream)` and `os_tcp_unlisten(listener)`,
            // each a value or a Promise. A deadline is a bigint of `monotonic_clock` or null;
            // a wait whose deadline passed answers null.
            case 'Os::tcp_close':case 'Os::tcp_unlisten':{
                const f=c.host.options['os_'+name.slice(4)];if(!f)return done(null);
                return Promise.resolve().then(()=>f(Number(a))).then(()=>more(()=>k(c,null)),()=>more(()=>k(c,null)));
            }
            case 'Os::tcp_listen':case 'Os::tcp_accept':case 'Os::tcp_connect':case 'Os::tcp_read':case 'Os::tcp_write':case 'Os::tcp_shutdown':{
                const f=c.host.options['os_'+name.slice(4)];if(!f)return done(err('host does not provide os_'+name.slice(4)));
                const deadline=v=>{v=unref(v);return v.tag==='Some'?v.fields[0]:null;};
                let call,back;
                const timed=g=>r=>r===null||r===undefined?none():some(g(r));
                if(name==='Os::tcp_listen'){call=()=>f(String(a));back=r=>list(r.map(String));}
                else if(name==='Os::tcp_accept'){call=()=>f(Number(a),deadline(vs[1]));back=timed(r=>list(r.map(String)));}
                else if(name==='Os::tcp_connect'){call=()=>f(String(a),deadline(vs[1]));back=timed(r=>list(r.map(String)));}
                else if(name==='Os::tcp_read'){call=()=>f(Number(a),Number(b),deadline(vs[2]));back=timed(r=>bytesValue(new Uint8Array(r)));}
                else if(name==='Os::tcp_write'){call=()=>f(Number(a),unref(vs[1]).bytes.slice(),deadline(vs[2]));back=timed(()=>null);}
                else{call=()=>f(Number(a),Number(b));back=()=>null;}
                return Promise.resolve().then(call).then(
                    r=>more(()=>k(c,ok(back(r)))),
                    e=>more(()=>k(c,err(e.message??String(e)))));
            }
            // Programs that run on: the host gives `options.os_child_spawn(program, args, dir, env,
            // stdin, modes)` (`[number]`; `env` is [name, value] pairs, `modes` 0 a pipe and 1 the
            // run's own), `os_child_read(child, which, max, deadline)` (a Uint8Array, empty at the
            // end), `os_child_write(child, bytes)`, `os_child_close_stdin(child)`,
            // `os_child_wait(child, deadline)` (the exit status as `[code]`, `[]` when a signal
            // ended it) and `os_child_close(child)`, each a value or a Promise. A wait whose
            // deadline passed answers null.
            case 'Os::child_close':{
                const f=c.host.options.os_child_close;if(!f)return done(null);
                return Promise.resolve().then(()=>f(Number(a))).then(()=>more(()=>k(c,null)),()=>more(()=>k(c,null)));
            }
            case 'Os::child_spawn':case 'Os::child_read':case 'Os::child_write':case 'Os::child_close_stdin':case 'Os::child_wait':{
                const f=c.host.options['os_'+name.slice(4)];if(!f)return done(err('host does not provide os_'+name.slice(4)));
                const deadline=v=>{v=unref(v);return v.tag==='Some'?v.fields[0]:null;};
                const timed=g=>r=>r===null||r===undefined?none():some(g(r));
                let call,back;
                if(name==='Os::child_spawn'){
                    call=()=>{const flat=listItems(vs[3]).map(String);const env=[];for(let i=0;i+1<flat.length;i+=2)env.push([flat[i],flat[i+1]]);
                        return f(String(a),listItems(vs[1]).map(String),String(unref(vs[2])),env,unref(vs[4]).bytes.slice(),listItems(vs[5]).map(x=>Number(String(x))));};
                    back=r=>list(r.map(String));
                }
                else if(name==='Os::child_read'){call=()=>f(Number(a),Number(b),Number(unref(vs[2])),deadline(vs[3]));back=timed(r=>bytesValue(new Uint8Array(r)));}
                else if(name==='Os::child_write'){call=()=>f(Number(a),unref(vs[1]).bytes.slice());back=()=>null;}
                else if(name==='Os::child_wait'){call=()=>f(Number(a),deadline(vs[1]));back=timed(r=>list(r.map(String)));}
                else{call=()=>f(Number(a));back=()=>null;}
                return Promise.resolve().then(call).then(
                    r=>more(()=>k(c,ok(back(r)))),
                    e=>more(()=>k(c,err(e.message??String(e)))));
            }
            // TLS: the JavaScript host has none yet. A program that needs it here answers
            // `tls_*` with a handler of its own.
            case 'Os::tls_close':return done(null);
            case 'Os::tls_accept':case 'Os::tls_connect':case 'Os::tls_read':case 'Os::tls_write':case 'Os::tls_send':case 'Os::tls_shutdown':
                return done(err('the JavaScript host has no TLS'));
            case 'Os::stop':throw new Error(String(a));
            case 'Os::exit':{checked(a,0n,255n);throw Object.assign(new Error('program exited'),{exitCode:Number(a)});}
            default:throw new Error('unknown builtin '+name);
        }
    });
}
// The cells made so far: a BigInt, and a count not yet added to it, kept as
// a number while it is far below the safe integers.
let budgetCells=0n,budgetPending=0;
function charge(n){budgetPending+=n;if(budgetPending>=1073741824)cellsMade();}
function cellsMade(){if(budgetPending){budgetCells+=BigInt(budgetPending);budgetPending=0;}return budgetCells;}
function budgetRefill(budget,n){return budget.memory&&n!==null?cellsMade()+n:n;}
function tickBudget(c,k) {
    let any=false,empty=null;
    const out=b=>b.memory?b.left!==null&&cellsMade()>b.left:b.left===0n;
    for(let h=c.h;h;h=h.outer)if(h.budget){any=true;if(out(h.budget)&&!empty)empty=h.budget;}
    if(!any){tick(c.host);return more(()=>k(c,null));}
    if(!empty){for(let h=c.h;h;h=h.outer)if(h.budget&&!h.budget.memory&&h.budget.left!==null)h.budget.left--;return more(()=>k(c,null));}
    return route(c,'exceeded','optional',[{kind:'Info',resource:true}],(d,answer)=>{
        if(answer.answer==='more'){empty.left=budgetRefill(empty,answer.steps);return more(()=>k(d,null));}
        for(let h=d.h;h;h=h.outer)if(h.budget===empty)return more(()=>h.target({...d,h:h.outer},answer.value));
        throw new Error('budget frame is missing');
    },empty);
}

function temporaryRef(v,immutable=false){if(v?.ref)return v;const ref=reference(()=>v,x=>{v=x;});let owners=1;ref.temporary=true;ref.retain=()=>{owners++;};ref.release=()=>{if(--owners!==0)return;const value=v;v=undefined;dropValue(value);};if(immutable&&stableAggregate(v)){const value=v;trackStableReference(ref,stableState(()=>v===value&&stableAggregate(value)));}return ref;}
// What a run may ask of the host (`docs/design/host-effects.md`):
// `options.permissions` is `{read, write, env, net, run}`, each `true` (all) or a
// list of what it covers; a kind left out is denied.
function permissionGrant(options,kind){
    const g=options.permissions?.[kind];
    if(g===true)return true;
    if(Array.isArray(g)&&g.length>0)return g.map(String);
    return null;
}
function plainPath(options,path){
    if(options.resolvePath){const p=options.resolvePath(path);return p===null||p===undefined?null:String(p);}
    const parts=[];
    const whole=path.startsWith('/')?path:(options.cwd??'/')+'/'+path;
    for(const p of whole.split('/')){if(p===''||p==='.')continue;if(p==='..')parts.pop();else parts.push(p);}
    return '/'+parts.join('/');
}
function underPath(path,dir){return dir==='/'||path===dir||path.startsWith(dir.endsWith('/')?dir:dir+'/');}
// The URL as `fetch` reads it, with its host and port.
function parseUrl(url){
    let u;try{u=new URL(url);}catch(e){return null;}
    if(u.protocol!=='http:'&&u.protocol!=='https:')return null;
    const port=u.port===''?(u.protocol==='https:'?443:80):Number(u.port);
    return {href:u.href,host:u.hostname.toLowerCase(),port};
}
function netMatches(item,host,port){
    const at=parseUrl('http://'+item+'/');if(!at)return false;
    return /:\d+$/.test(item)?at.host===host&&at.port===port:at.host===host;
}
// What the host acts on when the permission covers `target`, `null` when
// it does not: the checked path or URL, not the spelling the program gave.
// A socket's address, `HOST:PORT` (an IPv6 host in brackets) or `unix:PATH`,
// with the host in lower case; `null` when it is neither.
function parseSocket(text){
    if(text.startsWith('unix:'))return text.length>5?{unix:text.slice(5)}:null;
    const m=/^(\[[0-9A-Fa-f:.]+\]|[A-Za-z0-9.-]+):([0-9]+)$/.exec(text);
    if(!m||Number(m[2])>65535)return null;
    return {host:m[1].toLowerCase(),port:Number(m[2])};
}
function socketText(a){return a.unix!==undefined?'unix:'+a.unix:a.host+':'+a.port;}
// `--allow-net` covers sockets too: `example.com` every port of the host,
// `example.com:8080` one, `unix:DIR` the sockets at or under DIR.
function socketCheck(options,g,target){
    const a=parseSocket(target);if(a===null)return null;
    if(a.unix!==undefined){
        const p=plainPath(options,a.unix);if(p===null)return null;
        return g.some(i=>{if(!i.startsWith('unix:'))return false;const dir=plainPath(options,i.slice(5));return dir!==null&&underPath(p,dir);})?'unix:'+p:null;
    }
    const covered=g.some(i=>{const b=parseSocket(i);if(b)return b.host===a.host&&b.port===a.port;const h=parseSocket(i+':0');return h!==null&&h.unix===undefined&&h.host===a.host;});
    return covered?socketText(a):null;
}
// A directory the host made for the run (`fs_temp_dir`): the run may read and
// write under it from now on, as the host picked it, not the program.
function permissionGrantDir(options,dir){
    options.permissions=options.permissions??{};
    for(const kind of ['read','write']){
        const g=options.permissions[kind];
        if(g===true)continue;
        options.permissions[kind]=[...(Array.isArray(g)?g:[]),dir];
    }
}
function permissionCheck(options,kind,target){
    if(kind==='socket'){
        const g=permissionGrant(options,'net');
        if(g===null)return null;
        if(g===true)return target;
        return socketCheck(options,g,target);
    }
    const g=permissionGrant(options,kind);
    if(g===null)return null;
    if(g===true)return target;
    switch(kind){
        case 'read':case 'write':{
            const p=plainPath(options,target);if(p===null)return null;
            return g.some(d=>{const dir=plainPath(options,d);return dir!==null&&underPath(p,dir);})?p:null;
        }
        case 'env':case 'run':return g.includes(target)?target:null;
        case 'net':{const u=parseUrl(target);return u!==null&&g.some(i=>netMatches(i.toLowerCase(),u.host,u.port))?u.href:null;}
        default:return null;
    }
}
const declarationRefs=Array.from({length:0},()=>Symbol());
const hostSignatures={};
const hostWaits=new Set([]);

const shownNames=new Map([]);

function d0(){for(;;){{return null;}}}
function f0(c,args,k){return direct(d0,g0,c,args,k,[]);}

function g0(c,args,k){return more(()=>k(c,d0()));}

const b1 = callFunction(pure(f3),[readLocal(1,false,false,true)],false);
function f1(c,args,k){return enterFunction(b1,[1],null,c,args,k,false,false,[true],false);}

const b2 = matchValue(readLocal(2,false,false,true),[[['ctor',"None",[],"Option"],pure(true),pure("2")],[['ctor',"Some",[['bind',4,false,true]],"Option"],pure(true),matchValue(callFunction(pure(f4),[borrowPlace(4,[],false),readLocal(3,false,false,true)],false),[[['ctor',"Ok",[['bind',5,false,true]],"Result"],pure(true),callFunction(pure(f5),[values([pure("0"),callFunction(pure(f6),[readLocal(5,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false)],[['ctor',"Err",[['bind',6,false,true]],"Result"],pure(true),callFunction(pure(f5),[values([pure("1"),callFunction(pure(f6),[readLocal(6,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false)]],false)]],true);
function f2(c,args,k){return enterFunction(b2,[2,3],null,c,args,k,false,false,[true,true],false);}

const b3 = matchValue(callFunction(pure(f7),[values([builtin("Nat::of_u64",[values([readLocal(7,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))]),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(7,false,false,true),pure(0n)],false),[[['ctor',"None",[],"Option"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Some",[['bind',8,false,true]],"Option"],pure(true),matchValue(callFunction(pure(f8),[values([readLocal(8,false,false,true),pure(true)],(c,vs,k)=>more(()=>k(c,construct("WS",["tokens","ok"],vs,[0,1],true,"WS",true))))],false),[[['ctor',"Pair",[['bind',9,false,true],['bind',10,false,true]],"Pair"],pure(true),matchValue(readLocal(10,false,false,true),[[['ctor',"WS",[['bind',11,false,true],['bind',12,false,true]],"WS"],pure(true),matchValue(readLocal(11,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),branch(readLocal(12,false,true,false),readLocal(9,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))))],[['wild'],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))]],true)]],true)]],false)]],false);
function f3(c,args,k){return enterFunction(b3,[7],null,c,args,k,false,false,[true],false);}

const b4 = callFunction(pure(f9),[borrowPlace(13,[],true),readLocal(14,false,true,false),mapValue(callFunction(pure(f10),[borrowPlace(13,["scan"],true),readLocal(14,false,false,true)],false),v=>temporaryRef(v,true))],false);
function f4(c,args,k){return enterFunction(b4,[13,14],null,c,args,k,false,false,[false,true],false);}

function d5(l15){for(;;){{let l16=bufOf('');d11(l16,l15);return l16.text;}}}
function f5(c,args,k){return direct(d5,g5,c,args,k,[0]);}

const b5 = sequence([defineLocal(16,false,builtin("Buf::new",[]),false),callFunction(pure(f11),[borrowPlace(16,[],false),readLocal(15,false,false,true)],false),builtin("Text::of",[readLocal(16,false,false,true)])]);
function g5(c,args,k){return enterFunction(b5,[15],null,c,args,k,false,false,[true],false);}

function d6(l17,l18){for(;;){t2:{const t1=unref(l17);requireDataOwner(t1);if(t1.tag==="VData"&&t1.owner==="SynVal"){let l19=small(t1.fields[0]);let l20=t1.fields[1];return dcons("Cons",[null,null],[" 0 ",dcons("Cons",[null,null],[String(l19),dcons("Cons",[null,null],[" ",dcons("Cons",[null,null],[String(d12(l20)),d13(l20,l18)],false,"List",true)],false,"List",true)],false,"List",true)],false,"List",true);break t2;}if(t1.tag==="VNat"&&t1.owner==="SynVal"){let l21=small(t1.fields[0]);return dcons("Cons",[null,null],[" 1 ",dcons("Cons",[null,null],[String(l21),l18],false,"List",true)],false,"List",true);break t2;}if(t1.tag==="VText"&&t1.owner==="SynVal"){let l22=t1.fields[0];return dcons("Cons",[null,null],[" 2 t",dcons("Cons",[null,null],[String(small(pureBuiltin("Nat::of_u64",[big(textBytes(l22).length)]))),dcons("Cons",[null,null],[" ",dcons("Cons",[null,null],[l22,l18],false,"List",true)],false,"List",true)],false,"List",true)],false,"List",true);break t2;}if(t1.tag==="VList"&&t1.owner==="SynVal"){let l23=t1.fields[0];return dcons("Cons",[null,null],[" 3 ",dcons("Cons",[null,null],[String(d12(l23)),d13(l23,l18)],false,"List",true)],false,"List",true);break t2;}if(t1.tag==="VOpt"&&t1.owner==="SynVal"){let l24=t1.fields[0];return d14(l24,l18);break t2;}throw new Error('no arm of the match fits');}}}
function f6(c,args,k){return direct(d6,g6,c,args,k,[0,0]);}

const b6 = matchValue(readLocal(17,false,false,true),[[['ctor',"VData",[['bind',19,false,true],['bind',20,false,true]],"SynVal"],pure(true),values([pure(" 0 "),values([values([readLocal(19,false,false,true)],(c,vs,k)=>more(()=>k(c,String(vs[0])))),values([pure(" "),values([values([callFunction(pure(f12),[borrowPlace(20,[],false)],false)],(c,vs,k)=>more(()=>k(c,String(vs[0])))),callFunction(pure(f13),[borrowPlace(20,[],false),readLocal(18,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],[['ctor',"VNat",[['bind',21,false,true]],"SynVal"],pure(true),values([pure(" 1 "),values([values([readLocal(21,false,false,true)],(c,vs,k)=>more(()=>k(c,String(vs[0])))),readLocal(18,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],[['ctor',"VText",[['bind',22,false,true]],"SynVal"],pure(true),values([pure(" 2 t"),values([values([builtin("Nat::of_u64",[values([readLocal(22,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],(c,vs,k)=>more(()=>k(c,String(vs[0])))),values([pure(" "),values([readLocal(22,false,false,true),readLocal(18,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],[['ctor',"VList",[['bind',23,false,true]],"SynVal"],pure(true),values([pure(" 3 "),values([values([callFunction(pure(f12),[borrowPlace(23,[],false)],false)],(c,vs,k)=>more(()=>k(c,String(vs[0])))),callFunction(pure(f13),[borrowPlace(23,[],false),readLocal(18,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],[['ctor',"VOpt",[['bind',24,false,true]],"SynVal"],pure(true),callFunction(pure(f14),[readLocal(24,false,false,true),readLocal(18,false,false,true)],false)]],true);
function g6(c,args,k){return enterFunction(b6,[17,18],null,c,args,k,false,false,[true,true],false);}

function d7(l25,l26,l27){l25=small(l25);l27=small(l27);for(;;){return d15(l25,l26,l27,dcons("Nil",[],[],false,"List",true));}}
function f7(c,args,k){return direct(d7,g7,c,args,k,[0,0,0]);}

const b7 = callFunction(pure(f15),[readLocal(25,false,false,true),readLocal(26,false,false,true),readLocal(27,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false);
function g7(c,args,k){return enterFunction(b7,[25,26,27],null,c,args,k,false,false,[true,true,true],false);}

const b8 = matchValue(callFunction(pure(f16),[readLocal(28,false,false,true)],false),[[['ctor',"Pair",[['bind',29,false,true],['bind',30,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f17),[pure(5n),readLocal(30,false,false,true)],false),[[['ctor',"Pair",[['bind',31,false,true],['bind',32,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f18),[readLocal(32,false,false,true)],false),[[['ctor',"Pair",[['bind',33,false,true],['bind',34,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f17),[readLocal(33,false,false,true),readLocal(34,false,false,true)],false),[[['ctor',"Pair",[['bind',35,false,true],['bind',36,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f19),[readLocal(36,false,false,true)],false),[[['ctor',"Pair",[['bind',37,false,true],['bind',38,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f18),[readLocal(38,false,false,true)],false),[[['ctor',"Pair",[['bind',39,false,true],['bind',40,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f20),[readLocal(40,false,false,true)],false),[[['ctor',"Pair",[['bind',41,false,true],['bind',42,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f21),[readLocal(41,false,true,false),readLocal(42,false,false,true)],false),[[['ctor',"WSynTables",[['bind',43,false,true],['bind',44,false,true],['bind',45,false,true]],"WSynTables"],pure(true),matchValue(callFunction(pure(f18),[readLocal(45,false,false,true)],false),[[['ctor',"Pair",[['bind',46,false,true],['bind',47,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f22),[readLocal(46,false,false,true),readLocal(47,false,false,true)],false),[[['ctor',"Pair",[['bind',48,false,true],['bind',49,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f23),[pure(5n),readLocal(49,false,false,true)],false),[[['ctor',"Pair",[['bind',50,false,true],['bind',51,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f24),[callFunction(pure(f25),[readLocal(31,false,true,false),pure(0n)],false),callFunction(pure(f25),[readLocal(31,false,true,false),pure(1n)],false),callFunction(pure(f25),[readLocal(31,false,true,false),pure(2n)],false),callFunction(pure(f25),[readLocal(31,false,true,false),pure(3n)],false),callFunction(pure(f25),[readLocal(31,false,false,true),pure(4n)],false)],false),[[['ctor',"None",[],"Option"],pure(true),values([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))),callFunction(pure(f26),[borrowPlace(51,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],[['ctor',"Some",[['bind',52,false,true]],"Option"],pure(true),values([values([values([readLocal(29,false,false,true),readLocal(52,false,false,true),builtin("Array::of_list",[readLocal(35,false,false,true)]),builtin("Array::of_list",[readLocal(37,false,false,true)]),readLocal(39,false,false,true),readLocal(41,false,true,false),builtin("Array::of_list",[readLocal(43,false,false,true)]),builtin("Array::of_list",[readLocal(44,false,false,true)]),builtin("Array::of_list",[readLocal(48,false,false,true)]),callFunction(pure(f27),[readLocal(50,false,true,false),pure(0n)],false),callFunction(pure(f27),[readLocal(50,false,true,false),pure(1n)],false),callFunction(pure(f27),[readLocal(50,false,true,false),pure(2n)],false),callFunction(pure(f27),[readLocal(50,false,true,false),pure(3n)],false),callFunction(pure(f27),[readLocal(50,false,false,true),pure(4n)],false)],(c,vs,k)=>more(()=>k(c,construct("SynParser",["name","scan","terminals","skipped","start","lr","lookahead","states","productions","span","ctx","token","diag","arg"],vs,[0,1,2,3,4,5,6,7,8,9,10,11,12,13],true,"SynParser",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),readLocal(51,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]],false)]],false)]],false)]],false)]],false)]],false)]],false)]],false)]],false)]],false);
function f8(c,args,k){return enterFunction(b8,[28],null,c,args,k,false,false,[true],false);}

const b9 = matchValue(callFunction(pure(f28),[readLocal(55,false,false,false),pure(0n),builtin("Nat::of_u64",[values([readLocal(54,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],false),[[['ctor',"Some",[['bind',56,false,true]],"Option"],pure(true),values([callFunction(pure(f29),[borrowPlace(53,[],true),readLocal(54,false,false,true),mapValue(values([readLocal(56,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SfLex",[null],vs,[0],false,"SynFail",true)))),v=>temporaryRef(v,true))],false)],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"None",[],"Option"],pure(true),sequence([defineLocal(57,false,builtin("Array::of_list",[callFunction(pure(f30),[borrowPlace(53,[],true),readLocal(55,false,false,false)],false)]),true),defineLocal(58,false,values([values([values([values([builtin("Nat::of_u64",[builtin("Array::len",[readLocal(57,false,true,false)])]),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([callFunction(pure(f31),[mapValue(builtin("Array::to_list",[mapValue(readLocal(53,false,false,false),v=>field(v,"productions",null))]),v=>temporaryRef(v,true))],false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),true),defineLocal(59,false,branch(mapValue(readLocal(53,false,false,false),v=>field(v,"lr",null)),callFunction(pure(f32),[readLocal(58,false,false,true),borrowPlace(53,[],true),readLocal(54,false,true,false),readLocal(57,false,false,true),values([pure(0n),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),pure(0n),pure(0n),pure(0n)],false),callFunction(pure(f33),[readLocal(58,false,false,true),borrowPlace(53,[],true),readLocal(54,false,true,false),readLocal(57,false,false,true),values([values([values([mapValue(readLocal(53,false,false,false),v=>field(v,"start",null))],(c,vs,k)=>more(()=>k(c,construct("SynN",[null],vs,[0],false,"SynSym",true))))],(c,vs,k)=>more(()=>k(c,construct("SiSym",[null],vs,[0],false,"SynItem",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),pure(1n),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),pure(0n),pure(0n),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],false)),true),matchValue(readLocal(59,false,false,true),[[['ctor',"Err",[['bind',60,false,true]],"Result"],pure(true),values([callFunction(pure(f29),[borrowPlace(53,[],true),readLocal(54,false,false,true),borrowPlace(60,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Ok",[['bind',61,false,true]],"Result"],pure(true),values([callFunction(pure(f34),[mapValue(readLocal(53,false,false,false),v=>field(v,"lr",null)),borrowPlace(61,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))]],true)])]],false);
function f9(c,args,k){return enterFunction(b9,[53,54,55],null,c,args,k,false,false,[false,true,false],false);}

const b10 = callFunction(pure(f35),[builtin("Nat::of_u64",[values([readLocal(63,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))]),borrowPlace(62,[],true),readLocal(63,false,true,false),builtin("Nat::of_u64",[values([readLocal(63,false,false,true)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))]),pure(0n),values([pure(0n),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("ScanMode",["current","pushed"],vs,[0,1],true,"ScanMode",true)))),callFunction(pure(f36),[callFunction(pure(f12),[mapValue(mapValue(readLocal(62,false,false,false),v=>field(v,"dyn_states",null)),v=>temporaryRef(v,true))],false)],false),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false);
function f10(c,args,k){return enterFunction(b10,[62,63],null,c,args,k,false,false,[false,true],false);}

function d11(l64,l65){for(;;){t2:{const t1=unref(l65);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return null;break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l66=t1.fields[0];let l67=t1.fields[1];{bufPush(l64,l66);const t3=l64;const t4=l67;l64=t3;l65=t4;continue;}break t2;}throw new Error('no arm of the match fits');}}}
function f11(c,args,k){return direct(d11,g11,c,args,k,[2,0]);}

const b11 = matchValue(readLocal(65,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),pure(null)],[['ctor',"Cons",[['bind',66,false,true],['bind',67,false,true]],"List"],pure(true),sequence([builtin("Buf::push",[borrowPlace(64,[],true),borrowPlace(66,[],false)]),tailSelfCall(pure(f11),[borrowPlace(64,[],true),readLocal(67,false,false,true)])])]],true);
function g11(c,args,k){return enterFunction(b11,[64,65],null,c,args,k,false,false,[false,true],true);}

function d12(l68){for(;;){return d167(l68,(0));}}
function f12(c,args,k){return g12(c,args,k);}

const b12 = callFunction(pure(f167),[readLocal(68,false,false,false),pure(0n)],false);
function g12(c,args,k){return enterFunction(b12,[68],null,c,args,k,false,false,[false],false);}

function d13(l71,l72){for(;;){t2:{const t1=unref(l71);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return l72;break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l73=t1.fields[0];let l74=t1.fields[1];return d6(copyValue(l73),d13(l74,l72));break t2;}throw new Error('no arm of the match fits');}}}
function f13(c,args,k){return direct(d13,g13,c,args,k,[1,0]);}

const b13 = matchValue(borrowPlace(71,[],true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(72,false,false,true)],[['ctor',"Cons",[['bind',73,true,false],['bind',74,true,false]],"List"],pure(true),callFunction(pure(f6),[readLocal(73,true,true,false),callFunction(pure(f13),[readLocal(74,false,false,false),readLocal(72,false,false,true)],false)],false)]],false);
function g13(c,args,k){return enterFunction(b13,[71,72],null,c,args,k,false,false,[false,true],false);}

function d14(l75,l76){for(;;){t2:{const t1=unref(l75);requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return dcons("Cons",[null,null],[" 4 0",l76],false,"List",true);break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l77=t1.fields[0];return dcons("Cons",[null,null],[" 4 1",d6(l77,l76)],false,"List",true);break t2;}throw new Error('no arm of the match fits');}}}
function f14(c,args,k){return direct(d14,g14,c,args,k,[0,0]);}

const b14 = matchValue(readLocal(75,false,false,true),[[['ctor',"None",[],"Option"],pure(true),values([pure(" 4 0"),readLocal(76,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],[['ctor',"Some",[['bind',77,false,true]],"Option"],pure(true),values([pure(" 4 1"),callFunction(pure(f6),[readLocal(77,false,false,true),readLocal(76,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]],true);
function g14(c,args,k){return enterFunction(b14,[75,76],null,c,args,k,false,false,[true,true],false);}

function d15(l78,l79,l80,l81){l78=small(l78);l80=small(l80);for(;;){{let l82=l78;if((l82==(0))){{return dcons("None",[],[],false,"Option",true);}}else{{let l83=isub(l82,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d37(l79,l80));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return dcons("Some",[null],[d38(l81)],false,"Option",true);break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l84=small(t1.fields[0]);if(d39(l84)){const t3=l83;const t4=l79;const t5=iadd(l80,(1),0,9007199254740991,0n,Infinity);const t6=l81;l78=t3;l79=t4;l80=t5;l81=t6;continue;}else{if((l84==(116))){t8:{const t7=unref(d40(small(pureBuiltin("Nat::of_u64",[big(textBytes(l79).length)])),l79,iadd(l80,(1),0,9007199254740991,0n,Infinity),(0),false));requireDataOwner(t7);if(t7.tag==="None"&&t7.owner==="Option"){return dcons("None",[],[],false,"Option",true);break t8;}if(t7.tag==="Some"&&t7.owner==="Option"){let l85=t7.fields[0];t10:{const t9=unref(l85);requireDataOwner(t9);if(t9.tag==="Pair"&&t9.owner==="Pair"){let l86=small(t9.fields[0]);let l87=small(t9.fields[1]);if((iadd(l87,l86,0,9007199254740991,0n,Infinity)<=small(pureBuiltin("Nat::of_u64",[big(textBytes(l79).length)])))){const t11=l83;const t12=l79;const t13=iadd(l87,l86,0,9007199254740991,0n,Infinity);const t14=dcons("Cons",[null,null],[dcons("WtText",[null],[d41(l79,l87,iadd(l87,l86,0,9007199254740991,0n,Infinity))],false,"WTok",true),l81],false,"List",true);l78=t11;l79=t12;l80=t13;l81=t14;continue;}else{return dcons("None",[],[],false,"Option",true);}break t10;}throw new Error('no arm of the match fits');}break t8;}throw new Error('no arm of the match fits');}}else{t16:{const t15=unref(d40(small(pureBuiltin("Nat::of_u64",[big(textBytes(l79).length)])),l79,l80,(0),false));requireDataOwner(t15);if(t15.tag==="None"&&t15.owner==="Option"){return dcons("None",[],[],false,"Option",true);break t16;}if(t15.tag==="Some"&&t15.owner==="Option"){let l88=t15.fields[0];t18:{const t17=unref(l88);requireDataOwner(t17);if(t17.tag==="Pair"&&t17.owner==="Pair"){let l89=small(t17.fields[0]);let l90=small(t17.fields[1]);const t19=l83;const t20=l79;const t21=l90;const t22=dcons("Cons",[null,null],[dcons("WtNum",[null],[big(l89)],false,"WTok",true),l81],false,"List",true);l78=t19;l79=t20;l80=t21;l81=t22;continue;break t18;}throw new Error('no arm of the match fits');}break t16;}throw new Error('no arm of the match fits');}}}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f15(c,args,k){return direct(d15,g15,c,args,k,[0,0,0,0]);}

const b15 = sequence([defineLocal(82,false,readLocal(78,false,false,true),true),branch(values([readLocal(82,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))]),sequence([defineLocal(83,false,values([readLocal(82,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f37),[readLocal(79,false,true,false),readLocal(80,false,true,false)],false),[[['ctor',"None",[],"Option"],pure(true),values([callFunction(pure(f38),[readLocal(81,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['ctor',"Some",[['bind',84,false,true]],"Option"],pure(true),branch(callFunction(pure(f39),[readLocal(84,false,true,false)],false),tailSelfCall(pure(f15),[readLocal(83,false,false,true),readLocal(79,false,false,true),values([readLocal(80,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(81,false,false,true)]),branch(values([readLocal(84,false,false,true),pure(116n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),matchValue(callFunction(pure(f40),[builtin("Nat::of_u64",[values([readLocal(79,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))]),readLocal(79,false,true,false),values([readLocal(80,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n),pure(false)],false),[[['ctor',"None",[],"Option"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Some",[['bind',85,false,true]],"Option"],pure(true),matchValue(readLocal(85,false,false,true),[[['ctor',"Pair",[['bind',86,false,true],['bind',87,false,true]],"Pair"],pure(true),branch(values([values([readLocal(87,false,true,false),readLocal(86,false,true,false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),builtin("Nat::of_u64",[values([readLocal(79,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),tailSelfCall(pure(f15),[readLocal(83,false,false,true),readLocal(79,false,true,false),values([readLocal(87,false,true,false),readLocal(86,false,true,false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([values([callFunction(pure(f41),[readLocal(79,false,true,false),readLocal(87,false,true,false),values([readLocal(87,false,false,true),readLocal(86,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false)],(c,vs,k)=>more(()=>k(c,construct("WtText",[null],vs,[0],false,"WTok",true)))),readLocal(81,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))))]],true)]],false),matchValue(callFunction(pure(f40),[builtin("Nat::of_u64",[values([readLocal(79,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))]),readLocal(79,false,true,false),readLocal(80,false,false,true),pure(0n),pure(false)],false),[[['ctor',"None",[],"Option"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Some",[['bind',88,false,true]],"Option"],pure(true),matchValue(readLocal(88,false,false,true),[[['ctor',"Pair",[['bind',89,false,true],['bind',90,false,true]],"Pair"],pure(true),tailSelfCall(pure(f15),[readLocal(83,false,false,true),readLocal(79,false,false,true),readLocal(90,false,false,true),values([values([readLocal(89,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("WtNum",[null],vs,[0],false,"WTok",true)))),readLocal(81,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])]],true)]],false)))]],false)]))]);
function g15(c,args,k){return enterFunction(b15,[78,79,80,81],null,c,args,k,false,false,[true,true,true,true],true);}

function d16(l91){for(;;){t2:{const t1=unref(copyValue(l91));requireDataOwner(t1);if(t1.tag==="WS"&&t1.owner==="WS"){let l92=t1.fields[0];let l93=t1.fields[1];t4:{const t3=unref(l92);requireDataOwner(t3);if(t3.tag==="Cons"&&t3.owner==="List"){let l94=t3.fields[0];let l95=t3.fields[1];t6:{const t5=unref(l94);requireDataOwner(t5);if(t5.tag==="WtText"&&t5.owner==="WTok"){let l96=t5.fields[0];return dcons("Pair",["fst","snd"],[l96,dcons("WS",["tokens","ok"],[l95,l93],true,"WS",true)],true,"Pair",true);break t6;}if(true){return dcons("Pair",["fst","snd"],["",d26(l91)],true,"Pair",true);break t6;}throw new Error('no arm of the match fits');}break t4;}if(t3.tag==="Nil"&&t3.owner==="List"){return dcons("Pair",["fst","snd"],["",d26(l91)],true,"Pair",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f16(c,args,k){return direct(d16,g16,c,args,k,[0]);}

const b16 = matchValue(readLocal(91,false,true,false),[[['ctor',"WS",[['bind',92,false,true],['bind',93,false,true]],"WS"],pure(true),matchValue(readLocal(92,false,false,true),[[['ctor',"Cons",[['bind',94,false,true],['bind',95,false,true]],"List"],pure(true),matchValue(readLocal(94,false,false,true),[[['ctor',"WtText",[['bind',96,false,true]],"WTok"],pure(true),values([readLocal(96,false,false,true),values([readLocal(95,false,false,true),readLocal(93,false,true,false)],(c,vs,k)=>more(()=>k(c,construct("WS",["tokens","ok"],vs,[0,1],true,"WS",true))))],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],[['wild'],pure(true),values([pure(""),callFunction(pure(f26),[borrowPlace(91,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],true)],[['ctor',"Nil",[],"List"],pure(true),values([pure(""),callFunction(pure(f26),[borrowPlace(91,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],true)]],true);
function g16(c,args,k){return enterFunction(b16,[91],null,c,args,k,false,false,[true],false);}

function d17(l97,l98){l97=small(l97);for(;;){{let l99=l97;if((l99==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l98],true,"Pair",true);}}else{{let l100=isub(l99,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d16(l98));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l101=t1.fields[0];let l102=t1.fields[1];t4:{const t3=unref(d17(l100,l102));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l103=t3.fields[0];let l104=t3.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[l101,l103],false,"List",true),l104],true,"Pair",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f17(c,args,k){return direct(d17,g17,c,args,k,[0,0]);}

const b17 = sequence([defineLocal(99,false,readLocal(97,false,false,true),true),branch(values([readLocal(99,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(98,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(100,false,values([readLocal(99,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f16),[readLocal(98,false,false,true)],false),[[['ctor',"Pair",[['bind',101,false,true],['bind',102,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f17),[readLocal(100,false,false,true),readLocal(102,false,false,true)],false),[[['ctor',"Pair",[['bind',103,false,true],['bind',104,false,true]],"Pair"],pure(true),values([values([readLocal(101,false,false,true),readLocal(103,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(104,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]))]);
function g17(c,args,k){return enterFunction(b17,[97,98],null,c,args,k,false,false,[true,true],false);}

function d18(l105){for(;;){t2:{const t1=unref(copyValue(l105));requireDataOwner(t1);if(t1.tag==="WS"&&t1.owner==="WS"){let l106=t1.fields[0];let l107=t1.fields[1];t4:{const t3=unref(l106);requireDataOwner(t3);if(t3.tag==="Cons"&&t3.owner==="List"){let l108=t3.fields[0];let l109=t3.fields[1];t6:{const t5=unref(l108);requireDataOwner(t5);if(t5.tag==="WtNum"&&t5.owner==="WTok"){let l110=small(t5.fields[0]);return dcons("Pair",["fst","snd"],[big(l110),dcons("WS",["tokens","ok"],[l109,l107],true,"WS",true)],true,"Pair",true);break t6;}if(true){return dcons("Pair",["fst","snd"],[big((0)),d26(l105)],true,"Pair",true);break t6;}throw new Error('no arm of the match fits');}break t4;}if(t3.tag==="Nil"&&t3.owner==="List"){return dcons("Pair",["fst","snd"],[big((0)),d26(l105)],true,"Pair",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f18(c,args,k){return direct(d18,g18,c,args,k,[0]);}

const b18 = matchValue(readLocal(105,false,true,false),[[['ctor',"WS",[['bind',106,false,true],['bind',107,false,true]],"WS"],pure(true),matchValue(readLocal(106,false,false,true),[[['ctor',"Cons",[['bind',108,false,true],['bind',109,false,true]],"List"],pure(true),matchValue(readLocal(108,false,false,true),[[['ctor',"WtNum",[['bind',110,false,true]],"WTok"],pure(true),values([readLocal(110,false,false,true),values([readLocal(109,false,false,true),readLocal(107,false,true,false)],(c,vs,k)=>more(()=>k(c,construct("WS",["tokens","ok"],vs,[0,1],true,"WS",true))))],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],[['wild'],pure(true),values([pure(0n),callFunction(pure(f26),[borrowPlace(105,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],true)],[['ctor',"Nil",[],"List"],pure(true),values([pure(0n),callFunction(pure(f26),[borrowPlace(105,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],true)]],true);
function g18(c,args,k){return enterFunction(b18,[105],null,c,args,k,false,false,[true],false);}

function d19(l111){for(;;){t2:{const t1=unref(d18(l111));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l112=small(t1.fields[0]);let l113=t1.fields[1];return d42(l112,l113);break t2;}throw new Error('no arm of the match fits');}}}
function f19(c,args,k){return direct(d19,g19,c,args,k,[0]);}

const b19 = matchValue(callFunction(pure(f18),[readLocal(111,false,false,true)],false),[[['ctor',"Pair",[['bind',112,false,true],['bind',113,false,true]],"Pair"],pure(true),callFunction(pure(f42),[readLocal(112,false,false,true),readLocal(113,false,false,true)],false)]],false);
function g19(c,args,k){return enterFunction(b19,[111],null,c,args,k,false,false,[true],false);}

function d20(l114){for(;;){t2:{const t1=unref(d18(l114));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l115=small(t1.fields[0]);let l116=t1.fields[1];return dcons("Pair",["fst","snd"],[d43((l115==(0))),l116],true,"Pair",true);break t2;}throw new Error('no arm of the match fits');}}}
function f20(c,args,k){return direct(d20,g20,c,args,k,[0]);}

const b20 = matchValue(callFunction(pure(f18),[readLocal(114,false,false,true)],false),[[['ctor',"Pair",[['bind',115,false,true],['bind',116,false,true]],"Pair"],pure(true),values([callFunction(pure(f43),[values([readLocal(115,false,false,true),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1]))))],false),readLocal(116,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false);
function g20(c,args,k){return enterFunction(b20,[114],null,c,args,k,false,false,[true],false);}

function d21(l117,l118){for(;;){t2:{const t1=unref(d18(l118));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l119=small(t1.fields[0]);let l120=t1.fields[1];if(l117){t4:{const t3=unref(d44(l119,l120));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l121=t3.fields[0];let l122=t3.fields[1];return dcons("WSynTables",["looks","states","rest"],[dcons("Nil",[],[],false,"List",true),l121,l122],true,"WSynTables",true);break t4;}throw new Error('no arm of the match fits');}}else{t6:{const t5=unref(d45(l119,l120));requireDataOwner(t5);if(t5.tag==="Pair"&&t5.owner==="Pair"){let l123=t5.fields[0];let l124=t5.fields[1];return dcons("WSynTables",["looks","states","rest"],[l123,dcons("Nil",[],[],false,"List",true),l124],true,"WSynTables",true);break t6;}throw new Error('no arm of the match fits');}}break t2;}throw new Error('no arm of the match fits');}}}
function f21(c,args,k){return direct(d21,g21,c,args,k,[0,0]);}

const b21 = matchValue(callFunction(pure(f18),[readLocal(118,false,false,true)],false),[[['ctor',"Pair",[['bind',119,false,true],['bind',120,false,true]],"Pair"],pure(true),branch(readLocal(117,false,true,false),matchValue(callFunction(pure(f44),[readLocal(119,false,false,true),readLocal(120,false,false,true)],false),[[['ctor',"Pair",[['bind',121,false,true],['bind',122,false,true]],"Pair"],pure(true),values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(121,false,false,true),readLocal(122,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("WSynTables",["looks","states","rest"],vs,[0,1,2],true,"WSynTables",true))))]],false),matchValue(callFunction(pure(f45),[readLocal(119,false,false,true),readLocal(120,false,false,true)],false),[[['ctor',"Pair",[['bind',123,false,true],['bind',124,false,true]],"Pair"],pure(true),values([readLocal(123,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(124,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("WSynTables",["looks","states","rest"],vs,[0,1,2],true,"WSynTables",true))))]],false))]],false);
function g21(c,args,k){return enterFunction(b21,[117,118],null,c,args,k,false,false,[true,true],false);}

function d22(l125,l126){l125=small(l125);for(;;){{let l127=l125;if((l127==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l126],true,"Pair",true);}}else{{let l128=isub(l127,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d18(l126));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l129=small(t1.fields[0]);let l130=t1.fields[1];t4:{const t3=unref(d18(l130));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l131=small(t3.fields[0]);let l132=t3.fields[1];t6:{const t5=unref(d46(l131,l132));requireDataOwner(t5);if(t5.tag==="Pair"&&t5.owner==="Pair"){let l133=t5.fields[0];let l134=t5.fields[1];t8:{const t7=unref(d47(l134));requireDataOwner(t7);if(t7.tag==="Pair"&&t7.owner==="Pair"){let l135=t7.fields[0];let l136=t7.fields[1];t10:{const t9=unref(d22(l128,l136));requireDataOwner(t9);if(t9.tag==="Pair"&&t9.owner==="Pair"){let l137=t9.fields[0];let l138=t9.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[dcons("SynProd",["lhs","rhs","shape"],[big(l129),l133,l135],true,"SynProd",true),l137],false,"List",true),l138],true,"Pair",true);break t10;}throw new Error('no arm of the match fits');}break t8;}throw new Error('no arm of the match fits');}break t6;}throw new Error('no arm of the match fits');}break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f22(c,args,k){return direct(d22,g22,c,args,k,[0,0]);}

const b22 = sequence([defineLocal(127,false,readLocal(125,false,false,true),true),branch(values([readLocal(127,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(126,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(128,false,values([readLocal(127,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f18),[readLocal(126,false,false,true)],false),[[['ctor',"Pair",[['bind',129,false,true],['bind',130,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f18),[readLocal(130,false,false,true)],false),[[['ctor',"Pair",[['bind',131,false,true],['bind',132,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f46),[readLocal(131,false,false,true),readLocal(132,false,false,true)],false),[[['ctor',"Pair",[['bind',133,false,true],['bind',134,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f47),[readLocal(134,false,false,true)],false),[[['ctor',"Pair",[['bind',135,false,true],['bind',136,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f22),[readLocal(128,false,false,true),readLocal(136,false,false,true)],false),[[['ctor',"Pair",[['bind',137,false,true],['bind',138,false,true]],"Pair"],pure(true),values([values([values([readLocal(129,false,false,true),readLocal(133,false,false,true),readLocal(135,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SynProd",["lhs","rhs","shape"],vs,[0,1,2],true,"SynProd",true)))),readLocal(137,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(138,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]],false)]],false)]],false)]))]);
function g22(c,args,k){return enterFunction(b22,[125,126],null,c,args,k,false,false,[true,true],false);}

function d23(l139,l140){l139=small(l139);for(;;){{let l141=l139;if((l141==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l140],true,"Pair",true);}}else{{let l142=isub(l141,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d18(l140));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l143=small(t1.fields[0]);let l144=t1.fields[1];t4:{const t3=unref(d23(l142,l144));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l145=t3.fields[0];let l146=t3.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[big(l143),l145],false,"List",true),l146],true,"Pair",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f23(c,args,k){return direct(d23,g23,c,args,k,[0,0]);}

const b23 = sequence([defineLocal(141,false,readLocal(139,false,false,true),true),branch(values([readLocal(141,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(140,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(142,false,values([readLocal(141,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f18),[readLocal(140,false,false,true)],false),[[['ctor',"Pair",[['bind',143,false,true],['bind',144,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f23),[readLocal(142,false,false,true),readLocal(144,false,false,true)],false),[[['ctor',"Pair",[['bind',145,false,true],['bind',146,false,true]],"Pair"],pure(true),values([values([readLocal(143,false,false,true),readLocal(145,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(146,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]))]);
function g23(c,args,k){return enterFunction(b23,[139,140],null,c,args,k,false,false,[true,true],false);}

const b24 = callFunction(pure(f48),[builtin("Array::of_list",[callFunction(pure(f49),[readLocal(147,false,false,true)],false)]),builtin("Array::of_list",[callFunction(pure(f49),[readLocal(148,false,false,true)],false)]),builtin("Array::of_list",[callFunction(pure(f49),[readLocal(149,false,false,true)],false)]),builtin("Array::of_list",[callFunction(pure(f49),[readLocal(150,false,false,true)],false)]),builtin("Array::of_list",[callFunction(pure(f49),[readLocal(151,false,false,true)],false)])],false);
function f24(c,args,k){return enterFunction(b24,[147,148,149,150,151],null,c,args,k,false,false,[true,true,true,true,true],false);}

function d25(l152,l153){l153=small(l153);for(;;){t2:{const t1=unref(d50(l152,l153));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return "";break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l154=t1.fields[0];return l154;break t2;}throw new Error('no arm of the match fits');}}}
function f25(c,args,k){return direct(d25,g25,c,args,k,[0,0]);}

const b25 = matchValue(callFunction(pure(f50),[readLocal(152,false,false,true),readLocal(153,false,false,true)],false),[[['ctor',"None",[],"Option"],pure(true),pure("")],[['ctor',"Some",[['bind',154,false,true]],"Option"],pure(true),readLocal(154,false,false,true)]],false);
function g25(c,args,k){return enterFunction(b25,[152,153],null,c,args,k,false,false,[true,true],false);}

function d26(l155){for(;;){t2:{const t1=unref(l155);requireDataOwner(t1);if(t1.tag==="WS"&&t1.owner==="WS"){let l156=t1.fields[0];let l157=t1.fields[1];return dcons("WS",["tokens","ok"],[dcons("Nil",[],[],false,"List",true),false],true,"WS",true);break t2;}throw new Error('no arm of the match fits');}}}
function f26(c,args,k){return direct(d26,g26,c,args,k,[1]);}

const b26 = matchValue(borrowPlace(155,[],true),[[['ctor',"WS",[['bind',156,true,false],['bind',157,true,false]],"WS"],pure(true),values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),pure(false)],(c,vs,k)=>more(()=>k(c,construct("WS",["tokens","ok"],vs,[0,1],true,"WS",true))))]],false);
function g26(c,args,k){return enterFunction(b26,[155],null,c,args,k,false,false,[false],false);}

function d27(l158,l159){l159=small(l159);for(;;){t2:{const t1=unref(d50(l158,l159));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return (0);break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l160=small(t1.fields[0]);return l160;break t2;}throw new Error('no arm of the match fits');}}}
function f27(c,args,k){return direct((...a)=>big(d27(...a)),g27,c,args,k,[0,0]);}

const b27 = matchValue(callFunction(pure(f50),[readLocal(158,false,false,true),readLocal(159,false,false,true)],false),[[['ctor',"None",[],"Option"],pure(true),pure(0n)],[['ctor',"Some",[['bind',160,false,true]],"Option"],pure(true),readLocal(160,false,false,true)]],false);
function g27(c,args,k){return enterFunction(b27,[158,159],null,c,args,k,false,false,[true,true],false);}

function d28(l161,l162,l163){l162=small(l162);l163=small(l163);for(;;){t2:{const t1=unref(l161);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){if((l162<l163)){return dcons("Some",[null],[big(l162)],false,"Option",true);}else{return dcons("None",[],[],false,"Option",true);}break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l164=t1.fields[0];let l165=t1.fields[1];if((small(l164.fields[1])==l162)){const t3=l165;const t4=small(l164.fields[2]);const t5=l163;l161=t3;l162=t4;l163=t5;continue;}else{return dcons("Some",[null],[big(l162)],false,"Option",true);}break t2;}throw new Error('no arm of the match fits');}}}
function f28(c,args,k){return direct(d28,g28,c,args,k,[1,0,0]);}

const b28 = matchValue(borrowPlace(161,[],true),[[['ctor',"Nil",[],"List"],pure(true),branch(values([readLocal(162,false,true,false),readLocal(163,false,false,true)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),values([readLocal(162,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))))],[['ctor',"Cons",[['bind',164,true,false],['bind',165,true,false]],"List"],pure(true),branch(values([mapValue(readLocal(164,false,false,false),v=>field(v,"start",null)),readLocal(162,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),tailSelfCall(pure(f28),[readLocal(165,false,false,false),mapValue(readLocal(164,false,false,false),v=>field(v,"end",null)),readLocal(163,false,false,true)]),values([readLocal(162,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))))]],false);
function g28(c,args,k){return enterFunction(b28,[161,162,163],null,c,args,k,false,false,[false,true,true],true);}

const b29 = sequence([defineLocal(169,false,callFunction(pure(f51),[borrowPlace(166,[],true),pure("syntax"),mapValue(readLocal(166,false,false,false),v=>field(v,"name",null))],false),true),matchValue(borrowPlace(168,[],true),[[['ctor',"SfLex",[['bind',170,true,false]],"SynFail"],pure(true),callFunction(pure(f52),[borrowPlace(166,[],true),pure("macro-syntax-not-a-token"),readLocal(170,true,true,false),mapValue(values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),v=>temporaryRef(v,true)),values([readLocal(169,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false)],[['ctor',"SfSyntax",[['bind',171,true,false],['bind',172,true,false]],"SynFail"],pure(true),sequence([defineLocal(173,false,callFunction(pure(f53),[borrowPlace(166,[],true),readLocal(172,false,false,false)],false),true),defineLocal(175,false,matchValue(borrowPlace(171,[],true),[[['ctor',"None",[],"Option"],pure(true),builtin("Nat::of_u64",[values([readLocal(167,false,false,true)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],[['ctor',"Some",[['bind',174,true,false]],"Option"],pure(true),mapValue(readLocal(174,false,false,false),v=>field(v,"start",null))]],false),true),defineLocal(177,false,matchValue(borrowPlace(171,[],true),[[['ctor',"None",[],"Option"],pure(true),pure(false)],[['ctor',"Some",[['bind',176,true,false]],"Option"],pure(true),values([callFunction(pure(f54),[borrowPlace(166,[],true),mapValue(readLocal(176,false,false,false),v=>field(v,"token_type",null))],false),pure("Error")],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1]))))]],false),true),branch(readLocal(177,false,true,false),callFunction(pure(f52),[borrowPlace(166,[],true),pure("macro-syntax-not-a-token"),readLocal(175,false,false,true),mapValue(values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),v=>temporaryRef(v,true)),values([readLocal(169,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false),matchValue(borrowPlace(171,[],true),[[['ctor',"None",[],"Option"],pure(true),callFunction(pure(f52),[borrowPlace(166,[],true),pure("macro-syntax-expected-end"),readLocal(175,false,false,true),mapValue(readLocal(173,false,true,false),v=>temporaryRef(v,true)),values([readLocal(169,false,false,true),callFunction(pure(f55),[borrowPlace(166,[],true),borrowPlace(173,[],false),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false)],[['ctor',"Some",[['bind',178,true,false]],"Option"],pure(true),callFunction(pure(f52),[borrowPlace(166,[],true),pure("macro-syntax-expected-found"),readLocal(175,false,false,true),mapValue(readLocal(173,false,true,false),v=>temporaryRef(v,true)),values([readLocal(169,false,false,true),callFunction(pure(f55),[borrowPlace(166,[],true),borrowPlace(173,[],false),values([callFunction(pure(f51),[borrowPlace(166,[],true),pure("found"),callFunction(pure(f54),[borrowPlace(166,[],true),mapValue(readLocal(178,false,false,false),v=>field(v,"token_type",null))],false)],false),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false)]],false))])],[['ctor',"SfLimit",[['bind',179,true,false]],"SynFail"],pure(true),callFunction(pure(f52),[borrowPlace(166,[],true),pure("macro-syntax-limit"),pure(0n),mapValue(values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),v=>temporaryRef(v,true)),values([readLocal(169,false,false,true),values([callFunction(pure(f51),[borrowPlace(166,[],true),pure("detail"),readLocal(179,true,true,false)],false),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false)],[['ctor',"SfSchema",[['bind',180,true,false]],"SynFail"],pure(true),callFunction(pure(f52),[borrowPlace(166,[],true),pure("macro-syntax-schema"),pure(0n),mapValue(values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),v=>temporaryRef(v,true)),values([callFunction(pure(f51),[borrowPlace(166,[],true),pure("detail"),readLocal(180,true,true,false)],false),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false)]],false)]);
function f29(c,args,k){return enterFunction(b29,[166,167,168],null,c,args,k,false,false,[false,true,false],false);}

const b30 = matchValue(borrowPlace(182,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',183,true,false],['bind',184,true,false]],"List"],pure(true),matchValue(builtin("Array::get",[mapValue(readLocal(181,false,false,false),v=>field(v,"skipped",null)),builtin("U64::of_nat",[mapValue(readLocal(183,false,false,false),v=>field(v,"token_type",null))])]),[[['ctor',"Some",[['bind',185,false,true]],"Option"],pure(true),branch(readLocal(185,false,true,false),tailSelfCall(pure(f30),[borrowPlace(181,[],true),readLocal(184,false,false,false)]),values([readLocal(183,true,true,false),callFunction(pure(f30),[borrowPlace(181,[],true),readLocal(184,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))))],[['ctor',"None",[],"Option"],pure(true),values([readLocal(183,true,true,false),callFunction(pure(f30),[borrowPlace(181,[],true),readLocal(184,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]],false)]],false);
function f30(c,args,k){return enterFunction(b30,[181,182],null,c,args,k,false,false,[false,false],true);}

function d31(l186){for(;;){t2:{const t1=unref(l186);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return (0);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l187=t1.fields[0];let l188=t1.fields[1];return iadd(iadd(d12(copyValue(l187.fields[1])),(1),0,9007199254740991,0n,Infinity),d31(l188),0,9007199254740991,0n,Infinity);break t2;}throw new Error('no arm of the match fits');}}}
function f31(c,args,k){return direct((...a)=>big(d31(...a)),g31,c,args,k,[1]);}

const b31 = matchValue(borrowPlace(186,[],true),[[['ctor',"Nil",[],"List"],pure(true),pure(0n)],[['ctor',"Cons",[['bind',187,true,false],['bind',188,true,false]],"List"],pure(true),values([values([callFunction(pure(f12),[mapValue(mapValue(readLocal(187,false,false,false),v=>field(v,"rhs",null)),v=>temporaryRef(v,true))],false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),callFunction(pure(f31),[readLocal(188,false,false,false)],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))]],false);
function g31(c,args,k){return enterFunction(b31,[186],null,c,args,k,false,false,[false],false);}

const b32 = sequence([defineLocal(198,false,readLocal(189,false,false,true),true),branch(values([readLocal(198,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([pure("the parse takes more steps than the limit")],(c,vs,k)=>more(()=>k(c,construct("SfLimit",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]),sequence([defineLocal(199,false,values([readLocal(198,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(200,false,callFunction(pure(f56),[borrowPlace(190,[],true),callFunction(pure(f57),[borrowPlace(193,[],false)],false)],false),true),matchValue(callFunction(pure(f58),[borrowPlace(200,["actions"],false),callFunction(pure(f59),[readLocal(192,false,true,false),readLocal(196,false,true,false)],false)],false),[[['ctor',"None",[],"Option"],pure(true),values([values([builtin("Array::get",[readLocal(192,false,false,true),builtin("U64::of_nat",[readLocal(196,false,false,true)])]),callFunction(pure(f60),[mapValue(callFunction(pure(f61),[borrowPlace(200,["actions"],false)],false),v=>temporaryRef(v,true))],false)],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',201,false,true]],"Option"],pure(true),branch(values([mapValue(readLocal(201,false,false,false),v=>field(v,"kind",null)),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),matchValue(builtin("Array::get",[readLocal(192,false,true,false),builtin("U64::of_nat",[readLocal(196,false,true,false)])]),[[['ctor',"None",[],"Option"],pure(true),values([values([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',202,false,true]],"Option"],pure(true),tailSelfCall(pure(f32),[readLocal(199,false,false,true),borrowPlace(190,[],true),readLocal(191,false,true,false),readLocal(192,false,false,true),values([mapValue(readLocal(201,false,false,false),v=>field(v,"arg",null)),readLocal(193,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),values([callFunction(pure(f62),[borrowPlace(190,[],true),readLocal(191,false,true,false),readLocal(202,false,true,false)],false),readLocal(194,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),values([readLocal(195,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([readLocal(196,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),mapValue(readLocal(202,false,false,false),v=>field(v,"end",null))])]],false),matchValue(builtin("Array::get",[mapValue(readLocal(190,false,false,false),v=>field(v,"productions",null)),builtin("U64::of_nat",[mapValue(readLocal(201,false,false,false),v=>field(v,"arg",null))])]),[[['ctor',"None",[],"Option"],pure(true),values([values([builtin("Array::get",[readLocal(192,false,false,true),builtin("U64::of_nat",[readLocal(196,false,false,true)])]),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',203,false,true]],"Option"],pure(true),sequence([defineLocal(204,false,callFunction(pure(f12),[borrowPlace(203,["rhs"],false)],false),true),branch(values([readLocal(195,false,true,false),readLocal(204,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),values([values([builtin("Array::get",[readLocal(192,false,false,true),builtin("U64::of_nat",[readLocal(196,false,false,true)])]),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true)))),sequence([defineLocal(205,false,callFunction(pure(f38),[callFunction(pure(f63),[readLocal(204,false,true,false),readLocal(194,false,true,false)],false)],false),true),branch(values([mapValue(readLocal(201,false,false,false),v=>field(v,"kind",null)),pure(1n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([defineLocal(206,false,callFunction(pure(f64),[readLocal(204,false,true,false),readLocal(193,false,false,true)],false),true),matchValue(callFunction(pure(f65),[mapValue(mapValue(callFunction(pure(f56),[borrowPlace(190,[],true),callFunction(pure(f57),[borrowPlace(206,[],false)],false)],false),v=>field(v,"gotos",null)),v=>temporaryRef(v,true)),mapValue(readLocal(203,false,false,false),v=>field(v,"lhs",null))],false),[[['ctor',"None",[],"Option"],pure(true),values([values([builtin("Array::get",[readLocal(192,false,false,true),builtin("U64::of_nat",[readLocal(196,false,false,true)])]),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',207,false,true]],"Option"],pure(true),matchValue(callFunction(pure(f66),[borrowPlace(190,[],true),mapValue(readLocal(201,false,false,false),v=>field(v,"arg",null)),borrowPlace(205,[],false),readLocal(197,false,true,false)],false),[[['ctor',"Err",[['bind',208,false,true]],"Result"],pure(true),values([readLocal(208,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Ok",[['bind',209,false,true]],"Result"],pure(true),tailSelfCall(pure(f32),[readLocal(199,false,false,true),borrowPlace(190,[],true),readLocal(191,false,false,true),readLocal(192,false,false,true),values([mapValue(readLocal(207,false,false,false),v=>field(v,"state",null)),readLocal(206,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),values([readLocal(209,false,false,true),callFunction(pure(f64),[readLocal(204,false,true,false),readLocal(194,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),values([callFunction(pure(f67),[readLocal(195,false,false,true),readLocal(204,false,false,true)],false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(196,false,false,true),readLocal(197,false,false,true)])]],false)]],false)]),branch(values([readLocal(195,false,false,true),readLocal(204,false,false,true)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),callFunction(pure(f66),[borrowPlace(190,[],true),mapValue(readLocal(201,false,false,false),v=>field(v,"arg",null)),borrowPlace(205,[],false),readLocal(197,false,false,true)],false),values([values([builtin("Array::get",[readLocal(192,false,false,true),builtin("U64::of_nat",[readLocal(196,false,false,true)])]),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))))]))])]],false))]],false)])]))]);
function f32(c,args,k){return enterFunction(b32,[189,190,191,192,193,194,195,196,197],null,c,args,k,false,false,[true,false,true,true,true,true,true,true,true],true);}

const b33 = sequence([defineLocal(220,false,readLocal(210,false,false,true),true),branch(values([readLocal(220,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([pure("the parse takes more steps than the limit")],(c,vs,k)=>more(()=>k(c,construct("SfLimit",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]),sequence([defineLocal(221,false,values([readLocal(220,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(readLocal(214,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),branch(values([readLocal(217,false,true,false),builtin("Nat::of_u64",[builtin("Array::len",[readLocal(213,false,true,false)])])],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),values([values([builtin("Array::get",[readLocal(213,false,false,true),builtin("U64::of_nat",[readLocal(217,false,false,true)])]),values([pure(0n),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true)))),matchValue(readLocal(219,false,false,true),[[['ctor',"None",[],"Option"],pure(true),values([values([pure("no events")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',222,false,true]],"Option"],pure(true),values([readLocal(222,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))]],true))],[['ctor',"Cons",[['bind',223,false,true],['bind',224,false,true]],"List"],pure(true),matchValue(readLocal(223,false,false,true),[[['ctor',"SiClose",[],"SynItem"],pure(true),matchValue(readLocal(216,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),values([values([pure("a close without an open")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Cons",[['bind',225,false,true],['bind',226,false,true]],"List"],pure(true),matchValue(callFunction(pure(f66),[borrowPlace(211,[],true),mapValue(readLocal(225,false,false,false),v=>field(v,"production",null)),mapValue(callFunction(pure(f38),[mapValue(readLocal(225,false,false,false),v=>field(v,"values",null))],false),v=>temporaryRef(v,true)),mapValue(readLocal(225,false,false,false),v=>field(v,"open_end",null))],false),[[['ctor',"Err",[['bind',227,false,true]],"Result"],pure(true),values([readLocal(227,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Ok",[['bind',228,false,true]],"Result"],pure(true),matchValue(readLocal(226,false,true,false),[[['ctor',"Nil",[],"List"],pure(true),tailSelfCall(pure(f33),[readLocal(221,false,false,true),borrowPlace(211,[],true),readLocal(212,false,false,true),readLocal(213,false,false,true),readLocal(224,false,false,true),callFunction(pure(f67),[readLocal(215,false,false,true),pure(1n)],false),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(217,false,false,true),readLocal(218,false,false,true),values([readLocal(228,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))])],[['ctor',"Cons",[['bind',229,false,true],['bind',230,false,true]],"List"],pure(true),matchValue(callFunction(pure(f68),[readLocal(226,false,false,true),readLocal(228,false,false,true)],false),[[['ctor',"None",[],"Option"],pure(true),values([values([pure("a close without an open")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',231,false,true]],"Option"],pure(true),tailSelfCall(pure(f33),[readLocal(221,false,false,true),borrowPlace(211,[],true),readLocal(212,false,false,true),readLocal(213,false,false,true),readLocal(224,false,false,true),callFunction(pure(f67),[readLocal(215,false,false,true),pure(1n)],false),readLocal(231,false,false,true),readLocal(217,false,false,true),readLocal(218,false,false,true),readLocal(219,false,false,true)])]],false)]],true)]],false)]],true)],[['ctor',"SiSym",[['bind',232,false,true]],"SynItem"],pure(true),matchValue(readLocal(232,false,false,true),[[['ctor',"SynN",[['bind',233,false,true]],"SynSym"],pure(true),matchValue(callFunction(pure(f69),[borrowPlace(211,[],true),readLocal(213,false,true,false),readLocal(233,false,false,true),readLocal(217,false,true,false)],false),[[['ctor',"Err",[['bind',234,false,true]],"Result"],pure(true),values([readLocal(234,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Ok",[['bind',235,false,true]],"Result"],pure(true),matchValue(builtin("Array::get",[mapValue(readLocal(211,false,false,false),v=>field(v,"productions",null)),builtin("U64::of_nat",[readLocal(235,false,true,false)])]),[[['ctor',"None",[],"Option"],pure(true),values([values([pure("an event names a production of another non-terminal")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',236,false,true]],"Option"],pure(true),sequence([defineLocal(237,false,callFunction(pure(f12),[borrowPlace(236,["rhs"],false)],false),true),tailSelfCall(pure(f33),[readLocal(221,false,false,true),borrowPlace(211,[],true),readLocal(212,false,false,true),readLocal(213,false,false,true),callFunction(pure(f70),[borrowPlace(236,["rhs"],false),values([values([],(c,vs,k)=>more(()=>k(c,construct("SiClose",[],vs,[],false,"SynItem",true)))),readLocal(224,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false),values([readLocal(215,false,false,true),readLocal(237,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([values([readLocal(235,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(218,false,true,false)],(c,vs,k)=>more(()=>k(c,construct("SynFrame",["production","values","open_end"],vs,[0,1,2],true,"SynFrame",true)))),readLocal(216,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(217,false,false,true),readLocal(218,false,false,true),readLocal(219,false,false,true)])])]],false)]],false)],[['ctor',"SynT",[['bind',238,false,true]],"SynSym"],pure(true),matchValue(builtin("Array::get",[readLocal(213,false,true,false),builtin("U64::of_nat",[readLocal(217,false,true,false)])]),[[['ctor',"None",[],"Option"],pure(true),values([values([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))),values([readLocal(238,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',239,false,true]],"Option"],pure(true),branch(values([mapValue(readLocal(239,false,false,false),v=>field(v,"token_type",null)),readLocal(238,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),matchValue(callFunction(pure(f68),[readLocal(216,false,false,true),callFunction(pure(f62),[borrowPlace(211,[],true),readLocal(212,false,true,false),readLocal(239,false,true,false)],false)],false),[[['ctor',"None",[],"Option"],pure(true),values([values([pure("a token outside a node")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',240,false,true]],"Option"],pure(true),tailSelfCall(pure(f33),[readLocal(221,false,false,true),borrowPlace(211,[],true),readLocal(212,false,false,true),readLocal(213,false,false,true),readLocal(224,false,false,true),callFunction(pure(f67),[readLocal(215,false,false,true),pure(1n)],false),readLocal(240,false,false,true),values([readLocal(217,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),mapValue(readLocal(239,false,false,false),v=>field(v,"end",null)),readLocal(219,false,false,true)])]],false),values([values([values([readLocal(239,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),values([readLocal(238,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true)))))]],false)]],true)]],true)]],true)]))]);
function f33(c,args,k){return enterFunction(b33,[210,211,212,213,214,215,216,217,218,219],null,c,args,k,false,false,[true,false,true,true,true,true,true,true,true,true],true);}

function d34(l241,l242){for(;;){t2:{const t1=unref(l242);requireDataOwner(t1);if(t1.tag==="SvOne"&&t1.owner==="SynV"){let l243=t1.fields[0];let l244=small(t1.fields[1]);let l245=small(t1.fields[2]);return copyValue(l243);break t2;}if(t1.tag==="SvOpt"&&t1.owner==="SynV"){let l246=t1.fields[0];let l247=small(t1.fields[1]);let l248=small(t1.fields[2]);return dcons("VOpt",[null],[copyValue(l246)],false,"SynVal",true);break t2;}if(t1.tag==="SvList"&&t1.owner==="SynV"){let l249=t1.fields[0];let l250=small(t1.fields[1]);let l251=small(t1.fields[2]);return dcons("VList",[null],[(l241?d38(copyValue(l249)):copyValue(l249))],false,"SynVal",true);break t2;}throw new Error('no arm of the match fits');}}}
function f34(c,args,k){return direct(d34,g34,c,args,k,[0,1]);}

const b34 = matchValue(borrowPlace(242,[],true),[[['ctor',"SvOne",[['bind',243,true,false],['bind',244,true,false],['bind',245,true,false]],"SynV"],pure(true),readLocal(243,true,true,false)],[['ctor',"SvOpt",[['bind',246,true,false],['bind',247,true,false],['bind',248,true,false]],"SynV"],pure(true),values([readLocal(246,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("VOpt",[null],vs,[0],false,"SynVal",true))))],[['ctor',"SvList",[['bind',249,true,false],['bind',250,true,false],['bind',251,true,false]],"SynV"],pure(true),values([branch(readLocal(241,false,true,false),callFunction(pure(f38),[readLocal(249,true,true,false)],false),readLocal(249,true,true,false))],(c,vs,k)=>more(()=>k(c,construct("VList",[null],vs,[0],false,"SynVal",true))))]],false);
function g34(c,args,k){return enterFunction(b34,[241,242],null,c,args,k,false,false,[true,false],false);}

const b35 = sequence([defineLocal(260,false,readLocal(252,false,false,true),true),branch(values([readLocal(260,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([callFunction(pure(f38),[readLocal(259,false,false,true)],false)]),sequence([defineLocal(261,false,values([readLocal(260,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([readLocal(256,false,true,false),readLocal(255,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',false],pure(true),callFunction(pure(f38),[readLocal(259,false,false,true)],false)],[['literal',true],pure(true),matchValue(callFunction(pure(f71),[mapValue(callFunction(pure(f72),[borrowPlace(253,[],true),readLocal(258,false,true,false),readLocal(256,false,true,false)],false),v=>temporaryRef(v,true)),readLocal(254,false,true,false),mapValue(readLocal(257,false,false,false),v=>field(v,"current",null)),readLocal(256,false,true,false),readLocal(255,false,true,false)],false),[[['ctor',"None",[],"Option"],pure(true),tailSelfCall(pure(f35),[readLocal(261,false,false,true),borrowPlace(253,[],true),readLocal(254,false,true,false),readLocal(255,false,false,true),values([readLocal(256,false,true,false),callFunction(pure(f73),[callFunction(pure(f74),[readLocal(254,false,true,false),readLocal(256,false,false,true)],false)],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(257,false,false,true),readLocal(258,false,false,true),readLocal(259,false,false,true)])],[['ctor',"Some",[['bind',262,false,true]],"Option"],pure(true),tailSelfCall(pure(f35),[readLocal(261,false,false,true),borrowPlace(253,[],true),readLocal(254,false,true,false),readLocal(255,false,false,true),mapValue(readLocal(262,false,false,false),v=>field(v,"fst",0)),callFunction(pure(f75),[borrowPlace(253,[],true),readLocal(257,false,true,false),mapValue(readLocal(262,false,false,false),v=>field(v,"snd",1))],false),callFunction(pure(f76),[mapValue(callFunction(pure(f72),[borrowPlace(253,[],true),readLocal(258,false,false,true),readLocal(256,false,true,false)],false),v=>temporaryRef(v,true)),readLocal(254,false,true,false),mapValue(readLocal(262,false,false,false),v=>field(v,"snd",1)),readLocal(256,false,true,false),mapValue(readLocal(262,false,false,false),v=>field(v,"fst",0))],false),values([values([mapValue(readLocal(262,false,false,false),v=>field(v,"snd",1)),readLocal(256,false,false,true),mapValue(readLocal(262,false,false,false),v=>field(v,"fst",0)),mapValue(readLocal(257,false,false,false),v=>field(v,"current",null))],(c,vs,k)=>more(()=>k(c,construct("ScanToken",["token_type","start","end","mode"],vs,[0,1,2,3],true,"ScanToken",true)))),readLocal(259,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])]],false)]],false)]))]);
function f35(c,args,k){return enterFunction(b35,[252,253,254,255,256,257,258,259],null,c,args,k,false,false,[true,false,true,true,true,true,true,true],true);}

function d36(l263){l263=small(l263);for(;;){{let l264=l263;if((l264==(0))){{return dcons("Nil",[],[],false,"List",true);}}else{{let l265=isub(l264,(1),0,9007199254740991,0n,Infinity);return dcons("Cons",[null,null],[dcons("ScanHeldNone",[],[],false,"ScanHeld",true),d36(l265)],false,"List",true);}}}}}
function f36(c,args,k){return direct(d36,g36,c,args,k,[0]);}

const b36 = sequence([defineLocal(264,false,readLocal(263,false,false,true),true),branch(values([readLocal(264,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))]),sequence([defineLocal(265,false,values([readLocal(264,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),values([values([],(c,vs,k)=>more(()=>k(c,construct("ScanHeldNone",[],vs,[],false,"ScanHeld",true)))),callFunction(pure(f36),[readLocal(265,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]))]);
function g36(c,args,k){return enterFunction(b36,[263],null,c,args,k,false,false,[true],false);}

function d37(l266,l267){l267=small(l267);for(;;){t2:{const t1=unref(pureBuiltin("Text::byte",[l266,big(small(pureBuiltin("U64::of_nat",[big(l267)])))]));requireDataOwner(t1);if(t1.tag==="Some"&&t1.owner==="Option"){let l268=small(t1.fields[0]);return dcons("Some",[null],[big(small(pureBuiltin("Nat::of_u64",[big(small(pureBuiltin("U64::of_u8",[big(l268)])))])))],false,"Option",true);break t2;}if(t1.tag==="None"&&t1.owner==="Option"){return dcons("None",[],[],false,"Option",true);break t2;}throw new Error('no arm of the match fits');}}}
function f37(c,args,k){return direct(d37,g37,c,args,k,[0,0]);}

const b37 = matchValue(builtin("Text::byte",[readLocal(266,false,false,true),builtin("U64::of_nat",[readLocal(267,false,false,true)])]),[[['ctor',"Some",[['bind',268,false,true]],"Option"],pure(true),values([builtin("Nat::of_u64",[builtin("U64::of_u8",[readLocal(268,false,true,false)])])],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['ctor',"None",[],"Option"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))]],false);
function g37(c,args,k){return enterFunction(b37,[266,267],null,c,args,k,false,false,[true,true],false);}

function d38(l269){for(;;){return d77(l269,dcons("Nil",[],[],false,"List",true));}}
function f38(c,args,k){return g38(c,args,k);}

const b38 = callFunction(pure(f77),[readLocal(269,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false);
function g38(c,args,k){return enterFunction(b38,[269],null,c,args,k,false,true,[true],false);}

function d39(l270){l270=small(l270);for(;;){return ((l270==(32))||(l270==(10)));}}
function f39(c,args,k){return direct(d39,g39,c,args,k,[0]);}

const b39 = branch(values([readLocal(270,false,true,false),pure(32n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),pure(true),values([readLocal(270,false,false,true),pure(10n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))));
function g39(c,args,k){return enterFunction(b39,[270],null,c,args,k,false,false,[true],false);}

function d40(l271,l272,l273,l274,l275){l271=small(l271);l273=small(l273);l274=small(l274);for(;;){{let l276=l271;if((l276==(0))){{return dcons("None",[],[],false,"Option",true);}}else{{let l277=isub(l276,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d37(l272,l273));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){if(l275){return dcons("Some",[null],[dcons("Pair",["fst","snd"],[big(l274),big(l273)],true,"Pair",true)],false,"Option",true);}else{return dcons("None",[],[],false,"Option",true);}break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l278=small(t1.fields[0]);if(d78(l278)){const t3=l277;const t4=l272;const t5=iadd(l273,(1),0,9007199254740991,0n,Infinity);const t6=iadd(imul(l274,(10),0,9007199254740991,0n,Infinity),d67(l278,(48)),0,9007199254740991,0n,Infinity);const t7=true;l271=t3;l272=t4;l273=t5;l274=t6;l275=t7;continue;}else{if((l275&&d39(l278))){return dcons("Some",[null],[dcons("Pair",["fst","snd"],[big(l274),big(iadd(l273,(1),0,9007199254740991,0n,Infinity))],true,"Pair",true)],false,"Option",true);}else{return dcons("None",[],[],false,"Option",true);}}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f40(c,args,k){return direct(d40,g40,c,args,k,[0,0,0,0,0]);}

const b40 = sequence([defineLocal(276,false,readLocal(271,false,false,true),true),branch(values([readLocal(276,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))]),sequence([defineLocal(277,false,values([readLocal(276,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f37),[readLocal(272,false,true,false),readLocal(273,false,true,false)],false),[[['ctor',"None",[],"Option"],pure(true),branch(readLocal(275,false,true,false),values([values([readLocal(274,false,false,true),readLocal(273,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))))],[['ctor',"Some",[['bind',278,false,true]],"Option"],pure(true),branch(callFunction(pure(f78),[readLocal(278,false,true,false)],false),tailSelfCall(pure(f40),[readLocal(277,false,false,true),readLocal(272,false,false,true),values([readLocal(273,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([values([readLocal(274,false,false,true),pure(10n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),callFunction(pure(f67),[readLocal(278,false,false,true),pure(48n)],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(true)]),branch(branch(readLocal(275,false,true,false),callFunction(pure(f39),[readLocal(278,false,false,true)],false),pure(false)),values([values([readLocal(274,false,false,true),values([readLocal(273,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))))]],false)]))]);
function g40(c,args,k){return enterFunction(b40,[271,272,273,274,275],null,c,args,k,false,false,[true,true,true,true,true],true);}

function d41(l279,l280,l281){l280=small(l280);l281=small(l281);for(;;){t2:{const t1=unref(pureBuiltin("Text::slice",[l279,big(small(pureBuiltin("U64::of_nat",[big(l280)]))),big(small(pureBuiltin("U64::of_nat",[big(l281)])))]));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return "";break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l282=t1.fields[0];return l282;break t2;}throw new Error('no arm of the match fits');}}}
function f41(c,args,k){return direct(d41,g41,c,args,k,[0,0,0]);}

const b41 = matchValue(builtin("Text::slice",[readLocal(279,false,false,true),builtin("U64::of_nat",[readLocal(280,false,false,true)]),builtin("U64::of_nat",[readLocal(281,false,false,true)])]),[[['ctor',"None",[],"Option"],pure(true),pure("")],[['ctor',"Some",[['bind',282,false,true]],"Option"],pure(true),readLocal(282,false,false,true)]],false);
function g41(c,args,k){return enterFunction(b41,[279,280,281],null,c,args,k,false,false,[true,true,true],false);}

function d42(l283,l284){l283=small(l283);for(;;){{let l285=l283;if((l285==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l284],true,"Pair",true);}}else{{let l286=isub(l285,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d20(l284));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l287=t1.fields[0];let l288=t1.fields[1];t4:{const t3=unref(d42(l286,l288));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l289=t3.fields[0];let l290=t3.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[l287,l289],false,"List",true),l290],true,"Pair",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f42(c,args,k){return direct(d42,g42,c,args,k,[0,0]);}

const b42 = sequence([defineLocal(285,false,readLocal(283,false,false,true),true),branch(values([readLocal(285,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(284,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(286,false,values([readLocal(285,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f20),[readLocal(284,false,false,true)],false),[[['ctor',"Pair",[['bind',287,false,true],['bind',288,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f42),[readLocal(286,false,false,true),readLocal(288,false,false,true)],false),[[['ctor',"Pair",[['bind',289,false,true],['bind',290,false,true]],"Pair"],pure(true),values([values([readLocal(287,false,true,false),readLocal(289,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(290,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]))]);
function g42(c,args,k){return enterFunction(b42,[283,284],null,c,args,k,false,false,[true,true],false);}

function d43(l291){for(;;){if(l291){return false;}else{return true;}}}
function f43(c,args,k){return direct(d43,g43,c,args,k,[0]);}

const b43 = branch(readLocal(291,false,true,false),pure(false),pure(true));
function g43(c,args,k){return enterFunction(b43,[291],null,c,args,k,false,false,[true],false);}

function d44(l292,l293){l292=small(l292);for(;;){{let l294=l292;if((l294==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l293],true,"Pair",true);}}else{{let l295=isub(l294,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d18(l293));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l296=small(t1.fields[0]);let l297=t1.fields[1];t4:{const t3=unref(d79(l296,l297));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l298=t3.fields[0];let l299=t3.fields[1];t6:{const t5=unref(d18(l299));requireDataOwner(t5);if(t5.tag==="Pair"&&t5.owner==="Pair"){let l300=small(t5.fields[0]);let l301=t5.fields[1];t8:{const t7=unref(d80(l300,l301));requireDataOwner(t7);if(t7.tag==="Pair"&&t7.owner==="Pair"){let l302=t7.fields[0];let l303=t7.fields[1];t10:{const t9=unref(d44(l295,l303));requireDataOwner(t9);if(t9.tag==="Pair"&&t9.owner==="Pair"){let l304=t9.fields[0];let l305=t9.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[dcons("SynState",["actions","gotos"],[l298,l302],true,"SynState",true),l304],false,"List",true),l305],true,"Pair",true);break t10;}throw new Error('no arm of the match fits');}break t8;}throw new Error('no arm of the match fits');}break t6;}throw new Error('no arm of the match fits');}break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f44(c,args,k){return direct(d44,g44,c,args,k,[0,0]);}

const b44 = sequence([defineLocal(294,false,readLocal(292,false,false,true),true),branch(values([readLocal(294,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(293,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(295,false,values([readLocal(294,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f18),[readLocal(293,false,false,true)],false),[[['ctor',"Pair",[['bind',296,false,true],['bind',297,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f79),[readLocal(296,false,false,true),readLocal(297,false,false,true)],false),[[['ctor',"Pair",[['bind',298,false,true],['bind',299,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f18),[readLocal(299,false,false,true)],false),[[['ctor',"Pair",[['bind',300,false,true],['bind',301,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f80),[readLocal(300,false,false,true),readLocal(301,false,false,true)],false),[[['ctor',"Pair",[['bind',302,false,true],['bind',303,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f44),[readLocal(295,false,false,true),readLocal(303,false,false,true)],false),[[['ctor',"Pair",[['bind',304,false,true],['bind',305,false,true]],"Pair"],pure(true),values([values([values([readLocal(298,false,false,true),readLocal(302,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SynState",["actions","gotos"],vs,[0,1],true,"SynState",true)))),readLocal(304,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(305,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]],false)]],false)]],false)]))]);
function g44(c,args,k){return enterFunction(b44,[292,293],null,c,args,k,false,false,[true,true],false);}

function d45(l306,l307){l306=small(l306);for(;;){{let l308=l306;if((l308==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l307],true,"Pair",true);}}else{{let l309=isub(l308,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d20(l307));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l310=t1.fields[0];let l311=t1.fields[1];if(l310){t4:{const t3=unref(d23((3),l311));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l312=t3.fields[0];let l313=t3.fields[1];t6:{const t5=unref(d81(d27(copyValue(l312),(2)),l313));requireDataOwner(t5);if(t5.tag==="Pair"&&t5.owner==="Pair"){let l314=t5.fields[0];let l315=t5.fields[1];t8:{const t7=unref(d45(l309,l315));requireDataOwner(t7);if(t7.tag==="Pair"&&t7.owner==="Pair"){let l316=t7.fields[0];let l317=t7.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[dcons("Some",[null],[dcons("SynLook",["prod0","k","transitions"],[big(d27(copyValue(l312),(0))),big(d27(l312,(1))),l314],true,"SynLook",true)],false,"Option",true),l316],false,"List",true),l317],true,"Pair",true);break t8;}throw new Error('no arm of the match fits');}break t6;}throw new Error('no arm of the match fits');}break t4;}throw new Error('no arm of the match fits');}}else{t10:{const t9=unref(d45(l309,l311));requireDataOwner(t9);if(t9.tag==="Pair"&&t9.owner==="Pair"){let l318=t9.fields[0];let l319=t9.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[dcons("None",[],[],false,"Option",true),l318],false,"List",true),l319],true,"Pair",true);break t10;}throw new Error('no arm of the match fits');}}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f45(c,args,k){return direct(d45,g45,c,args,k,[0,0]);}

const b45 = sequence([defineLocal(308,false,readLocal(306,false,false,true),true),branch(values([readLocal(308,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(307,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(309,false,values([readLocal(308,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f20),[readLocal(307,false,false,true)],false),[[['ctor',"Pair",[['bind',310,false,true],['bind',311,false,true]],"Pair"],pure(true),branch(readLocal(310,false,true,false),matchValue(callFunction(pure(f23),[pure(3n),readLocal(311,false,false,true)],false),[[['ctor',"Pair",[['bind',312,false,true],['bind',313,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f81),[callFunction(pure(f27),[readLocal(312,false,true,false),pure(2n)],false),readLocal(313,false,false,true)],false),[[['ctor',"Pair",[['bind',314,false,true],['bind',315,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f45),[readLocal(309,false,false,true),readLocal(315,false,false,true)],false),[[['ctor',"Pair",[['bind',316,false,true],['bind',317,false,true]],"Pair"],pure(true),values([values([values([values([callFunction(pure(f27),[readLocal(312,false,true,false),pure(0n)],false),callFunction(pure(f27),[readLocal(312,false,false,true),pure(1n)],false),readLocal(314,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SynLook",["prod0","k","transitions"],vs,[0,1,2],true,"SynLook",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),readLocal(316,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(317,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]],false),matchValue(callFunction(pure(f45),[readLocal(309,false,false,true),readLocal(311,false,false,true)],false),[[['ctor',"Pair",[['bind',318,false,true],['bind',319,false,true]],"Pair"],pure(true),values([values([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))),readLocal(318,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(319,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false))]],false)]))]);
function g45(c,args,k){return enterFunction(b45,[306,307],null,c,args,k,false,false,[true,true],false);}

function d46(l320,l321){l320=small(l320);for(;;){{let l322=l320;if((l322==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l321],true,"Pair",true);}}else{{let l323=isub(l322,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d20(l321));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l324=t1.fields[0];let l325=t1.fields[1];t4:{const t3=unref(d18(l325));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l326=small(t3.fields[0]);let l327=t3.fields[1];t6:{const t5=unref(d46(l323,l327));requireDataOwner(t5);if(t5.tag==="Pair"&&t5.owner==="Pair"){let l328=t5.fields[0];let l329=t5.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[(l324?dcons("SynT",[null],[big(l326)],false,"SynSym",true):dcons("SynN",[null],[big(l326)],false,"SynSym",true)),l328],false,"List",true),l329],true,"Pair",true);break t6;}throw new Error('no arm of the match fits');}break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f46(c,args,k){return direct(d46,g46,c,args,k,[0,0]);}

const b46 = sequence([defineLocal(322,false,readLocal(320,false,false,true),true),branch(values([readLocal(322,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(321,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(323,false,values([readLocal(322,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f20),[readLocal(321,false,false,true)],false),[[['ctor',"Pair",[['bind',324,false,true],['bind',325,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f18),[readLocal(325,false,false,true)],false),[[['ctor',"Pair",[['bind',326,false,true],['bind',327,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f46),[readLocal(323,false,false,true),readLocal(327,false,false,true)],false),[[['ctor',"Pair",[['bind',328,false,true],['bind',329,false,true]],"Pair"],pure(true),values([values([branch(readLocal(324,false,true,false),values([readLocal(326,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SynT",[null],vs,[0],false,"SynSym",true)))),values([readLocal(326,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SynN",[null],vs,[0],false,"SynSym",true))))),readLocal(328,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(329,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]],false)]))]);
function g46(c,args,k){return enterFunction(b46,[320,321],null,c,args,k,false,false,[true,true],false);}

function d47(l330){for(;;){t2:{const t1=unref(d18(l330));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l331=small(t1.fields[0]);let l332=t1.fields[1];if((l331==(0))){t4:{const t3=unref(d82(l332));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l333=t3.fields[0];let l334=t3.fields[1];t6:{const t5=unref(l333);requireDataOwner(t5);if(t5.tag==="SeNode"&&t5.owner==="SynElem"){let l335=small(t5.fields[0]);let l336=t5.fields[1];let l337=t5.fields[2];return dcons("Pair",["fst","snd"],[dcons("ShNode",[null,null,null],[big(l335),l336,l337],false,"SynShape",true),l334],true,"Pair",true);break t6;}if(t5.tag==="SeItem"&&t5.owner==="SynElem"){return dcons("Pair",["fst","snd"],[dcons("ShPass",[],[],false,"SynShape",true),d26(l334)],true,"Pair",true);break t6;}throw new Error('no arm of the match fits');}break t4;}throw new Error('no arm of the match fits');}}else{if((l331==(1))){return dcons("Pair",["fst","snd"],[dcons("ShPass",[],[],false,"SynShape",true),l332],true,"Pair",true);}else{if((l331==(2))){t8:{const t7=unref(d83(l332));requireDataOwner(t7);if(t7.tag==="Pair"&&t7.owner==="Pair"){let l338=t7.fields[0];let l339=t7.fields[1];return dcons("Pair",["fst","snd"],[dcons("ShSome",[null],[l338],false,"SynShape",true),l339],true,"Pair",true);break t8;}throw new Error('no arm of the match fits');}}else{if((l331==(3))){return dcons("Pair",["fst","snd"],[dcons("ShNone",[],[],false,"SynShape",true),l332],true,"Pair",true);}else{if((l331==(4))){return dcons("Pair",["fst","snd"],[dcons("ShEmpty",[],[],false,"SynShape",true),l332],true,"Pair",true);}else{if((l331==(5))){t10:{const t9=unref(d83(l332));requireDataOwner(t9);if(t9.tag==="Pair"&&t9.owner==="Pair"){let l340=t9.fields[0];let l341=t9.fields[1];return dcons("Pair",["fst","snd"],[dcons("ShMore",[null],[l340],false,"SynShape",true),l341],true,"Pair",true);break t10;}throw new Error('no arm of the match fits');}}else{if((l331==(6))){t12:{const t11=unref(d16(l332));requireDataOwner(t11);if(t11.tag==="Pair"&&t11.owner==="Pair"){let l342=t11.fields[0];let l343=t11.fields[1];return dcons("Pair",["fst","snd"],[dcons("ShBad",[null],[l342],false,"SynShape",true),l343],true,"Pair",true);break t12;}throw new Error('no arm of the match fits');}}else{return dcons("Pair",["fst","snd"],[dcons("ShPass",[],[],false,"SynShape",true),d26(l332)],true,"Pair",true);}}}}}}}break t2;}throw new Error('no arm of the match fits');}}}
function f47(c,args,k){return direct(d47,g47,c,args,k,[0]);}

const b47 = matchValue(callFunction(pure(f18),[readLocal(330,false,false,true)],false),[[['ctor',"Pair",[['bind',331,false,true],['bind',332,false,true]],"Pair"],pure(true),branch(values([readLocal(331,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),matchValue(callFunction(pure(f82),[readLocal(332,false,false,true)],false),[[['ctor',"Pair",[['bind',333,false,true],['bind',334,false,true]],"Pair"],pure(true),matchValue(readLocal(333,false,false,true),[[['ctor',"SeNode",[['bind',335,false,true],['bind',336,false,true],['bind',337,false,true]],"SynElem"],pure(true),values([values([readLocal(335,false,false,true),readLocal(336,false,true,false),readLocal(337,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("ShNode",[null,null,null],vs,[0,1,2],false,"SynShape",true)))),readLocal(334,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],[['ctor',"SeItem",[],"SynElem"],pure(true),values([values([],(c,vs,k)=>more(()=>k(c,construct("ShPass",[],vs,[],false,"SynShape",true)))),callFunction(pure(f26),[borrowPlace(334,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],true)]],false),branch(values([readLocal(331,false,true,false),pure(1n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),values([values([],(c,vs,k)=>more(()=>k(c,construct("ShPass",[],vs,[],false,"SynShape",true)))),readLocal(332,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true)))),branch(values([readLocal(331,false,true,false),pure(2n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),matchValue(callFunction(pure(f83),[readLocal(332,false,false,true)],false),[[['ctor',"Pair",[['bind',338,false,true],['bind',339,false,true]],"Pair"],pure(true),values([values([readLocal(338,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("ShSome",[null],vs,[0],false,"SynShape",true)))),readLocal(339,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false),branch(values([readLocal(331,false,true,false),pure(3n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),values([values([],(c,vs,k)=>more(()=>k(c,construct("ShNone",[],vs,[],false,"SynShape",true)))),readLocal(332,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true)))),branch(values([readLocal(331,false,true,false),pure(4n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),values([values([],(c,vs,k)=>more(()=>k(c,construct("ShEmpty",[],vs,[],false,"SynShape",true)))),readLocal(332,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true)))),branch(values([readLocal(331,false,true,false),pure(5n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),matchValue(callFunction(pure(f83),[readLocal(332,false,false,true)],false),[[['ctor',"Pair",[['bind',340,false,true],['bind',341,false,true]],"Pair"],pure(true),values([values([readLocal(340,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("ShMore",[null],vs,[0],false,"SynShape",true)))),readLocal(341,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false),branch(values([readLocal(331,false,false,true),pure(6n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),matchValue(callFunction(pure(f16),[readLocal(332,false,false,true)],false),[[['ctor',"Pair",[['bind',342,false,true],['bind',343,false,true]],"Pair"],pure(true),values([values([readLocal(342,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("ShBad",[null],vs,[0],false,"SynShape",true)))),readLocal(343,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false),values([values([],(c,vs,k)=>more(()=>k(c,construct("ShPass",[],vs,[],false,"SynShape",true)))),callFunction(pure(f26),[borrowPlace(332,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true)))))))))))]],false);
function g47(c,args,k){return enterFunction(b47,[330],null,c,args,k,false,false,[true],false);}

const b48 = sequence([defineLocal(349,false,callFunction(pure(f84),[readLocal(344,false,true,false),pure(0n)],false),true),defineLocal(350,false,callFunction(pure(f84),[readLocal(345,false,true,false),pure(0n)],false),true),defineLocal(351,false,builtin("Array::of_list",[callFunction(pure(f85),[readLocal(350,false,true,false),readLocal(345,false,true,false),pure(1n),pure(3n)],false)]),true),defineLocal(352,false,builtin("Array::of_list",[callFunction(pure(f85),[readLocal(350,false,true,false),readLocal(345,false,true,false),pure(2n),pure(3n)],false)]),true),defineLocal(353,false,builtin("Array::of_list",[callFunction(pure(f85),[readLocal(350,false,true,false),readLocal(345,false,true,false),pure(3n),pure(3n)],false)]),true),defineLocal(354,false,callFunction(pure(f86),[callFunction(pure(f84),[readLocal(344,false,true,false),pure(1n)],false),readLocal(344,false,true,false),pure(3n),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false),true),defineLocal(355,false,callFunction(pure(f87),[callFunction(pure(f84),[readLocal(344,false,true,false),pure(2n)],false),readLocal(349,false,true,false),readLocal(346,false,true,false),readLocal(347,false,true,false),values([pure(0n),pure(0n),pure(0n),pure(0n),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],vs,[0,1,2,3,4,5,6,7,8,9],true,"ScanBuild",true))))],false),true),defineLocal(356,false,callFunction(pure(f84),[readLocal(348,false,true,false),pure(0n)],false),true),defineLocal(357,false,callFunction(pure(f88),[readLocal(356,false,true,false),readLocal(348,false,true,false),pure(1n),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false),true),defineLocal(358,false,callFunction(pure(f89),[callFunction(pure(f84),[readLocal(348,false,true,false),values([pure(1n),values([readLocal(356,false,true,false),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),readLocal(348,false,true,false),values([pure(2n),values([readLocal(356,false,false,true),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false),true),defineLocal(361,false,sequence([defineLocal(359,false,builtin("Nat::of_u64",[builtin("Array::len",[readLocal(348,false,true,false)])]),true),branch(values([readLocal(359,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([pure(0n)]),sequence([defineLocal(360,false,values([readLocal(359,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),mapValue(readLocal(358,false,false,false),v=>field(v,"snd",1))]))]),true),matchValue(branch(branch(branch(branch(callFunction(pure(f90),[mapValue(readLocal(354,false,false,false),v=>field(v,"snd",1)),readLocal(344,false,false,true)],false),callFunction(pure(f90),[values([pure(1n),values([readLocal(350,false,false,true),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(345,false,false,true)],false),pure(false)),callFunction(pure(f90),[mapValue(readLocal(355,false,false,false),v=>field(v,"sp",null)),readLocal(346,false,false,true)],false),pure(false)),callFunction(pure(f90),[mapValue(readLocal(355,false,false,false),v=>field(v,"rp",null)),readLocal(347,false,false,true)],false),pure(false)),callFunction(pure(f90),[readLocal(361,false,false,true),readLocal(348,false,false,true)],false),pure(false)),[[['literal',false],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['literal',true],pure(true),values([values([readLocal(349,false,false,true),builtin("Array::of_list",[callFunction(pure(f91),[pure(128n),readLocal(351,false,true,false),readLocal(352,false,true,false),readLocal(353,false,true,false),pure(0n)],false)]),readLocal(351,false,false,true),readLocal(352,false,false,true),readLocal(353,false,false,true),callFunction(pure(f92),[mapValue(readLocal(355,false,false,false),v=>field(v,"built_dfa_first",null))],false),callFunction(pure(f92),[values([mapValue(readLocal(355,false,false,false),v=>field(v,"accepts",null)),mapValue(readLocal(355,false,false,false),v=>field(v,"built_accept_first",null))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false),callFunction(pure(f92),[mapValue(readLocal(355,false,false,false),v=>field(v,"built_accept_token",null))],false),callFunction(pure(f92),[mapValue(readLocal(355,false,false,false),v=>field(v,"built_accept_kind",null))],false),callFunction(pure(f92),[mapValue(readLocal(355,false,false,false),v=>field(v,"built_accept_dfa",null))],false),callFunction(pure(f92),[mapValue(readLocal(355,false,false,false),v=>field(v,"built_rows",null))],false),builtin("Array::of_list",[callFunction(pure(f38),[mapValue(readLocal(354,false,false,false),v=>field(v,"fst",0))],false)]),readLocal(357,false,false,true),mapValue(readLocal(358,false,false,false),v=>field(v,"fst",0)),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),pure(0n)],(c,vs,k)=>more(()=>k(c,construct("ScanTables",["classes","ascii","run_start","run_end","run_class","dfa_first","accept_first","accept_token","accept_kind","accept_dfa","rows","mode_changes","dyn_states","dyns","held","start"],vs,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],true,"ScanTables",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))]],false)]);
function f48(c,args,k){return enterFunction(b48,[344,345,346,347,348],null,c,args,k,false,false,[true,true,true,true,true],false);}

function d49(l362){for(;;){return d93(small(pureBuiltin("Nat::of_u64",[big(textBytes(l362).length)])),l362,(0),(0),false,dcons("Nil",[],[],false,"List",true));}}
function f49(c,args,k){return direct(d49,g49,c,args,k,[0]);}

const b49 = callFunction(pure(f93),[builtin("Nat::of_u64",[values([readLocal(362,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))]),readLocal(362,false,false,true),pure(0n),pure(0n),pure(false),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false);
function g49(c,args,k){return enterFunction(b49,[362],null,c,args,k,false,false,[true],false);}

function d50(l363,l364){l364=small(l364);for(;;){t2:{const t1=unref(l363);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("None",[],[],false,"Option",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l365=t1.fields[0];let l366=t1.fields[1];{let l367=l364;if((l367==(0))){{return dcons("Some",[null],[l365],false,"Option",true);}}else{{let l368=isub(l367,(1),0,9007199254740991,0n,Infinity);const t3=l366;const t4=l368;l363=t3;l364=t4;continue;}}}break t2;}throw new Error('no arm of the match fits');}}}
function f50(c,args,k){return g50(c,args,k);}

const b50 = matchValue(readLocal(363,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Cons",[['bind',365,false,true],['bind',366,false,true]],"List"],pure(true),sequence([defineLocal(367,false,readLocal(364,false,false,true),true),branch(values([readLocal(367,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([readLocal(365,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))]),sequence([defineLocal(368,false,values([readLocal(367,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f50),[readLocal(366,false,false,true),readLocal(368,false,false,true)])]))])]],true);
function g50(c,args,k){return enterFunction(b50,[363,364],null,c,args,k,false,true,[true,true],true);}

const b51 = values([mapValue(readLocal(369,false,false,false),v=>field(v,"arg",null)),values([values([readLocal(370,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("VText",[null],vs,[0],false,"SynVal",true)))),values([values([readLocal(371,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("VText",[null],vs,[0],false,"SynVal",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("VData",[null,null],vs,[0,1],false,"SynVal",true))));
function f51(c,args,k){return enterFunction(b51,[369,370,371],null,c,args,k,false,false,[false,true,true],false);}

const b52 = values([mapValue(readLocal(372,false,false,false),v=>field(v,"diag",null)),values([values([readLocal(373,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("VText",[null],vs,[0],false,"SynVal",true)))),values([values([readLocal(374,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("VNat",[null],vs,[0],false,"SynVal",true)))),values([values([callFunction(pure(f94),[readLocal(375,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("VList",[null],vs,[0],false,"SynVal",true)))),values([values([pure("macro.syntax_error")],(c,vs,k)=>more(()=>k(c,construct("VText",[null],vs,[0],false,"SynVal",true)))),values([values([readLocal(376,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("VList",[null],vs,[0],false,"SynVal",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("VData",[null,null],vs,[0,1],false,"SynVal",true))));
function f52(c,args,k){return enterFunction(b52,[372,373,374,375,376],null,c,args,k,false,false,[false,true,true,false,true],false);}

const b53 = matchValue(borrowPlace(378,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',379,true,false],['bind',380,true,false]],"List"],pure(true),values([callFunction(pure(f54),[borrowPlace(377,[],true),readLocal(379,true,true,false)],false),callFunction(pure(f53),[borrowPlace(377,[],true),readLocal(380,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]],false);
function f53(c,args,k){return enterFunction(b53,[377,378],null,c,args,k,false,false,[false,false],false);}

const b54 = matchValue(builtin("Array::get",[mapValue(readLocal(381,false,false,false),v=>field(v,"terminals",null)),builtin("U64::of_nat",[readLocal(382,false,false,true)])]),[[['ctor',"None",[],"Option"],pure(true),pure("")],[['ctor',"Some",[['bind',383,false,true]],"Option"],pure(true),readLocal(383,false,false,true)]],false);
function f54(c,args,k){return enterFunction(b54,[381,382],null,c,args,k,false,false,[false,true],false);}

const b55 = matchValue(borrowPlace(385,[],true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(386,false,false,true)],[['ctor',"Cons",[['bind',387,true,false],['bind',388,true,false]],"List"],pure(true),values([callFunction(pure(f51),[borrowPlace(384,[],true),pure("expected"),readLocal(387,true,true,false)],false),callFunction(pure(f55),[borrowPlace(384,[],true),readLocal(388,false,false,false),readLocal(386,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]],false);
function f55(c,args,k){return enterFunction(b55,[384,385,386],null,c,args,k,false,false,[false,false,true],false);}

const b56 = matchValue(builtin("Array::get",[mapValue(readLocal(389,false,false,false),v=>field(v,"states",null)),builtin("U64::of_nat",[readLocal(390,false,false,true)])]),[[['ctor',"None",[],"Option"],pure(true),values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SynState",["actions","gotos"],vs,[0,1],true,"SynState",true))))],[['ctor',"Some",[['bind',391,false,true]],"Option"],pure(true),readLocal(391,false,false,true)]],false);
function f56(c,args,k){return enterFunction(b56,[389,390],null,c,args,k,false,false,[false,true],false);}

function d57(l392){for(;;){t2:{const t1=unref(l392);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return (0);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l393=small(t1.fields[0]);let l394=t1.fields[1];return l393;break t2;}throw new Error('no arm of the match fits');}}}
function f57(c,args,k){return direct((...a)=>big(d57(...a)),g57,c,args,k,[1]);}

const b57 = matchValue(borrowPlace(392,[],true),[[['ctor',"Nil",[],"List"],pure(true),pure(0n)],[['ctor',"Cons",[['bind',393,true,false],['bind',394,true,false]],"List"],pure(true),readLocal(393,true,true,false)]],false);
function g57(c,args,k){return enterFunction(b57,[392],null,c,args,k,false,false,[false],false);}

function d58(l395,l396){l396=small(l396);for(;;){t2:{const t1=unref(l395);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("None",[],[],false,"Option",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l397=t1.fields[0];let l398=t1.fields[1];if((small(l397.fields[0])==l396)){return dcons("Some",[null],[copyValue(l397)],false,"Option",true);}else{const t3=l398;const t4=l396;l395=t3;l396=t4;continue;}break t2;}throw new Error('no arm of the match fits');}}}
function f58(c,args,k){return direct(d58,g58,c,args,k,[1,0]);}

const b58 = matchValue(borrowPlace(395,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Cons",[['bind',397,true,false],['bind',398,true,false]],"List"],pure(true),branch(values([mapValue(readLocal(397,false,false,false),v=>field(v,"terminal",null)),readLocal(396,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),values([readLocal(397,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),tailSelfCall(pure(f58),[readLocal(398,false,false,false),readLocal(396,false,false,true)]))]],false);
function g58(c,args,k){return enterFunction(b58,[395,396],null,c,args,k,false,false,[false,true],true);}

function d59(l399,l400){l400=small(l400);for(;;){t2:{const t1=unref(vecGet(l399,small(pureBuiltin("U64::of_nat",[big(l400)]))));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return (0);break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l401=t1.fields[0];return small(l401.fields[0]);break t2;}throw new Error('no arm of the match fits');}}}
function f59(c,args,k){return direct((...a)=>big(d59(...a)),g59,c,args,k,[0,0]);}

const b59 = matchValue(builtin("Array::get",[readLocal(399,false,false,true),builtin("U64::of_nat",[readLocal(400,false,false,true)])]),[[['ctor',"None",[],"Option"],pure(true),pure(0n)],[['ctor',"Some",[['bind',401,false,true]],"Option"],pure(true),mapValue(readLocal(401,false,false,false),v=>field(v,"token_type",null))]],false);
function g59(c,args,k){return enterFunction(b59,[399,400],null,c,args,k,false,false,[true,true],false);}

function d60(l402){for(;;){t2:{const t1=unref(l402);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("Nil",[],[],false,"List",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l403=small(t1.fields[0]);let l404=t1.fields[1];t4:{const t3=unref(l404);requireDataOwner(t3);if(t3.tag==="Nil"&&t3.owner==="List"){return dcons("Cons",[null,null],[big(l403),dcons("Nil",[],[],false,"List",true)],false,"List",true);break t4;}if(t3.tag==="Cons"&&t3.owner==="List"){let l405=small(t3.fields[0]);let l406=t3.fields[1];if((l403==l405)){const t5=l404;l402=t5;continue;}else{return dcons("Cons",[null,null],[big(l403),d60(l404)],false,"List",true);}break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f60(c,args,k){return direct(d60,g60,c,args,k,[1]);}

const b60 = matchValue(borrowPlace(402,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',403,true,false],['bind',404,true,false]],"List"],pure(true),matchValue(borrowPlace(404,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([readLocal(403,true,true,false),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],[['ctor',"Cons",[['bind',405,true,false],['bind',406,true,false]],"List"],pure(true),branch(values([readLocal(403,true,true,false),readLocal(405,true,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),tailSelfCall(pure(f60),[readLocal(404,false,false,false)]),values([readLocal(403,true,true,false),callFunction(pure(f60),[readLocal(404,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))))]],false)]],false);
function g60(c,args,k){return enterFunction(b60,[402],null,c,args,k,false,false,[false],true);}

function d61(l407){for(;;){t2:{const t1=unref(l407);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("Nil",[],[],false,"List",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l408=t1.fields[0];let l409=t1.fields[1];return dcons("Cons",[null,null],[big(small(l408.fields[0])),d61(l409)],false,"List",true);break t2;}throw new Error('no arm of the match fits');}}}
function f61(c,args,k){return direct(d61,g61,c,args,k,[1]);}

const b61 = matchValue(borrowPlace(407,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',408,true,false],['bind',409,true,false]],"List"],pure(true),values([mapValue(readLocal(408,false,false,false),v=>field(v,"terminal",null)),callFunction(pure(f61),[readLocal(409,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]],false);
function g61(c,args,k){return enterFunction(b61,[407],null,c,args,k,false,false,[false],false);}

const b62 = values([values([mapValue(readLocal(410,false,false,false),v=>field(v,"token",null)),values([values([callFunction(pure(f41),[readLocal(411,false,false,true),mapValue(readLocal(412,false,false,false),v=>field(v,"start",null)),mapValue(readLocal(412,false,false,false),v=>field(v,"end",null))],false)],(c,vs,k)=>more(()=>k(c,construct("VText",[null],vs,[0],false,"SynVal",true)))),values([callFunction(pure(f95),[borrowPlace(410,[],true),mapValue(readLocal(412,false,false,false),v=>field(v,"start",null))],false),values([values([mapValue(readLocal(410,false,false,false),v=>field(v,"ctx",null)),values([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("VList",[null],vs,[0],false,"SynVal",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("VData",[null,null],vs,[0,1],false,"SynVal",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("VData",[null,null],vs,[0,1],false,"SynVal",true)))),mapValue(readLocal(412,false,false,false),v=>field(v,"start",null)),mapValue(readLocal(412,false,false,false),v=>field(v,"end",null))],(c,vs,k)=>more(()=>k(c,construct("SvOne",[null,null,null],vs,[0,1,2],false,"SynV",true))));
function f62(c,args,k){return enterFunction(b62,[410,411,412],null,c,args,k,false,false,[false,true,true],false);}

function d63(l413,l414){l413=small(l413);for(;;){{let l415=l413;if((l415==(0))){{return dcons("Nil",[],[],false,"List",true);}}else{{let l416=isub(l415,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(l414);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("Nil",[],[],false,"List",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l417=t1.fields[0];let l418=t1.fields[1];return dcons("Cons",[null,null],[l417,d63(l416,l418)],false,"List",true);break t2;}throw new Error('no arm of the match fits');}}}}}}
function f63(c,args,k){return g63(c,args,k);}

const b63 = sequence([defineLocal(415,false,readLocal(413,false,false,true),true),branch(values([readLocal(415,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))]),sequence([defineLocal(416,false,values([readLocal(415,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(readLocal(414,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',417,false,true],['bind',418,false,true]],"List"],pure(true),values([readLocal(417,false,false,true),callFunction(pure(f63),[readLocal(416,false,false,true),readLocal(418,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]],true)]))]);
function g63(c,args,k){return enterFunction(b63,[413,414],null,c,args,k,false,true,[true,true],false);}

function d64(l419,l420){l419=small(l419);for(;;){{let l421=l419;if((l421==(0))){{return l420;}}else{{let l422=isub(l421,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(l420);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("Nil",[],[],false,"List",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l423=t1.fields[0];let l424=t1.fields[1];const t3=l422;const t4=l424;l419=t3;l420=t4;continue;break t2;}throw new Error('no arm of the match fits');}}}}}}
function f64(c,args,k){return g64(c,args,k);}

const b64 = sequence([defineLocal(421,false,readLocal(419,false,false,true),true),branch(values([readLocal(421,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(420,false,false,true)]),sequence([defineLocal(422,false,values([readLocal(421,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(readLocal(420,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',423,false,true],['bind',424,false,true]],"List"],pure(true),tailSelfCall(pure(f64),[readLocal(422,false,false,true),readLocal(424,false,false,true)])]],true)]))]);
function g64(c,args,k){return enterFunction(b64,[419,420],null,c,args,k,false,true,[true,true],true);}

function d65(l425,l426){l426=small(l426);for(;;){t2:{const t1=unref(l425);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("None",[],[],false,"Option",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l427=t1.fields[0];let l428=t1.fields[1];if((small(l427.fields[0])==l426)){return dcons("Some",[null],[copyValue(l427)],false,"Option",true);}else{const t3=l428;const t4=l426;l425=t3;l426=t4;continue;}break t2;}throw new Error('no arm of the match fits');}}}
function f65(c,args,k){return direct(d65,g65,c,args,k,[1,0]);}

const b65 = matchValue(borrowPlace(425,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Cons",[['bind',427,true,false],['bind',428,true,false]],"List"],pure(true),branch(values([mapValue(readLocal(427,false,false,false),v=>field(v,"non_terminal",null)),readLocal(426,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),values([readLocal(427,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),tailSelfCall(pure(f65),[readLocal(428,false,false,false),readLocal(426,false,false,true)]))]],false);
function g65(c,args,k){return enterFunction(b65,[425,426],null,c,args,k,false,false,[false,true],true);}

const b66 = sequence([defineLocal(433,false,callFunction(pure(f96),[readLocal(431,false,false,false),readLocal(432,false,false,true)],false),true),defineLocal(435,false,matchValue(callFunction(pure(f97),[readLocal(431,false,false,false)],false),[[['ctor',"None",[],"Option"],pure(true),readLocal(433,false,true,false)],[['ctor',"Some",[['bind',434,false,true]],"Option"],pure(true),readLocal(434,false,false,true)]],false),true),matchValue(builtin("Array::get",[mapValue(readLocal(429,false,false,false),v=>field(v,"productions",null)),builtin("U64::of_nat",[readLocal(430,false,false,true)])]),[[['ctor',"None",[],"Option"],pure(true),values([values([pure("an event names a production of another non-terminal")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',436,false,true]],"Option"],pure(true),matchValue(mapValue(readLocal(436,false,false,false),v=>field(v,"shape",null)),[[['ctor',"ShNode",[['bind',437,false,true],['bind',438,false,true],['bind',439,false,true]],"SynShape"],pure(true),values([values([callFunction(pure(f98),[borrowPlace(429,[],true),readLocal(437,false,false,true),readLocal(438,false,true,false),borrowPlace(439,[],false),readLocal(431,false,false,false),readLocal(435,false,true,false)],false),readLocal(435,false,false,true),readLocal(433,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SvOne",[null,null,null],vs,[0,1,2],false,"SynV",true))))],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))],[['ctor',"ShPass",[],"SynShape"],pure(true),matchValue(borrowPlace(431,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([values([pure("a token non-terminal without its token")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Cons",[['bind',440,true,false],['bind',441,true,false]],"List"],pure(true),values([callFunction(pure(f99),[readLocal(440,false,false,false),readLocal(435,false,false,true),readLocal(433,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))]],false)],[['ctor',"ShSome",[['bind',442,false,true]],"SynShape"],pure(true),matchValue(callFunction(pure(f100),[borrowPlace(429,[],true),borrowPlace(442,[],false),readLocal(431,false,false,false),readLocal(435,false,true,false)],false),[[['ctor',"Err",[['bind',443,false,true]],"Result"],pure(true),values([readLocal(443,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Ok",[['bind',444,false,true]],"Result"],pure(true),values([values([values([readLocal(444,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),readLocal(435,false,false,true),readLocal(433,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SvOpt",[null,null,null],vs,[0,1,2],false,"SynV",true))))],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))]],false)],[['ctor',"ShNone",[],"SynShape"],pure(true),values([values([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))),readLocal(435,false,false,true),readLocal(433,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SvOpt",[null,null,null],vs,[0,1,2],false,"SynV",true))))],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))],[['ctor',"ShEmpty",[],"SynShape"],pure(true),values([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(435,false,false,true),readLocal(433,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SvList",[null,null,null],vs,[0,1,2],false,"SynV",true))))],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))],[['ctor',"ShMore",[['bind',445,false,true]],"SynShape"],pure(true),branch(mapValue(readLocal(429,false,false,false),v=>field(v,"lr",null)),matchValue(borrowPlace(431,[],true),[[['ctor',"Cons",[['bind',446,true,false],['bind',447,true,false]],"List"],pure(true),matchValue(borrowPlace(446,[],true),[[['ctor',"SvList",[['bind',448,true,false],['bind',449,true,false],['bind',450,true,false]],"SynV"],pure(true),sequence([defineLocal(452,false,matchValue(callFunction(pure(f97),[readLocal(447,false,false,false)],false),[[['ctor',"None",[],"Option"],pure(true),readLocal(433,false,true,false)],[['ctor',"Some",[['bind',451,false,true]],"Option"],pure(true),readLocal(451,false,false,true)]],false),true),matchValue(callFunction(pure(f100),[borrowPlace(429,[],true),borrowPlace(445,[],false),readLocal(447,false,false,false),readLocal(452,false,false,true)],false),[[['ctor',"Err",[['bind',453,false,true]],"Result"],pure(true),values([readLocal(453,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Ok",[['bind',454,false,true]],"Result"],pure(true),values([values([values([readLocal(454,false,false,true),readLocal(448,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(435,false,false,true),readLocal(433,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SvList",[null,null,null],vs,[0,1,2],false,"SynV",true))))],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))]],false)])],[['wild'],pure(true),values([values([pure("a repetition does not start with itself")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]],false)],[['ctor',"Nil",[],"List"],pure(true),values([values([pure("a repetition does not start with itself")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]],false),matchValue(callFunction(pure(f101),[readLocal(431,false,false,false)],false),[[['ctor',"None",[],"Option"],pure(true),values([values([pure("a repetition does not end in itself")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Some",[['bind',455,false,true]],"Option"],pure(true),matchValue(mapValue(readLocal(455,false,false,false),v=>field(v,"snd",1)),[[['ctor',"SvList",[['bind',456,false,true],['bind',457,false,true],['bind',458,false,true]],"SynV"],pure(true),matchValue(callFunction(pure(f100),[borrowPlace(429,[],true),borrowPlace(445,[],false),borrowPlace(455,[0],false),readLocal(435,false,true,false)],false),[[['ctor',"Err",[['bind',459,false,true]],"Result"],pure(true),values([readLocal(459,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))],[['ctor',"Ok",[['bind',460,false,true]],"Result"],pure(true),values([values([values([readLocal(460,false,false,true),readLocal(456,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(435,false,false,true),readLocal(433,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SvList",[null,null,null],vs,[0,1,2],false,"SynV",true))))],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))]],false)],[['wild'],pure(true),values([values([pure("a repetition does not end in itself")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]],false)]],false))],[['ctor',"ShBad",[['bind',461,false,true]],"SynShape"],pure(true),values([values([readLocal(461,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]],false)]],false)]);
function f66(c,args,k){return enterFunction(b66,[429,430,431,432],null,c,args,k,false,false,[false,true,false,true],false);}

function d67(l462,l463){l462=small(l462);l463=small(l463);for(;;){if((l462<l463)){return (0);}else{return isub(l462,l463,0,9007199254740991,0n,Infinity);}}}
function f67(c,args,k){return direct((...a)=>big(d67(...a)),g67,c,args,k,[0,0]);}

const b67 = branch(values([readLocal(462,false,true,false),readLocal(463,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),pure(0n),values([readLocal(462,false,false,true),readLocal(463,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))));
function g67(c,args,k){return enterFunction(b67,[462,463],null,c,args,k,false,false,[true,true],false);}

const b68 = matchValue(readLocal(464,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Cons",[['bind',466,false,true],['bind',467,false,true]],"List"],pure(true),values([values([values([mapValue(readLocal(466,false,false,false),v=>field(v,"production",null)),values([readLocal(465,false,false,true),mapValue(readLocal(466,false,false,false),v=>field(v,"values",null))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),mapValue(readLocal(466,false,false,false),v=>field(v,"open_end",null))],(c,vs,k)=>more(()=>k(c,construct("SynFrame",["production","values","open_end"],vs,[0,1,2],true,"SynFrame",true)))),readLocal(467,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))]],true);
function f68(c,args,k){return enterFunction(b68,[464,465],null,c,args,k,false,false,[true,true],false);}

const b69 = matchValue(builtin("Array::get",[mapValue(readLocal(468,false,false,false),v=>field(v,"lookahead",null)),builtin("U64::of_nat",[readLocal(470,false,false,true)])]),[[['ctor',"Some",[['bind',472,false,true]],"Option"],pure(true),matchValue(readLocal(472,false,false,true),[[['ctor',"Some",[['bind',473,false,true]],"Option"],pure(true),callFunction(pure(f102),[mapValue(readLocal(473,false,false,false),v=>field(v,"k",null)),mapValue(readLocal(473,false,true,false),v=>temporaryRef(v,true)),readLocal(469,false,false,true),readLocal(471,false,false,true),pure(0n),pure(0n),mapValue(readLocal(473,false,false,false),v=>field(v,"prod0",null))],false)],[['ctor',"None",[],"Option"],pure(true),values([values([pure("a non-terminal has no lookahead automaton")],(c,vs,k)=>more(()=>k(c,construct("SfLimit",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]],true)],[['ctor',"None",[],"Option"],pure(true),values([values([pure("a non-terminal has no lookahead automaton")],(c,vs,k)=>more(()=>k(c,construct("SfLimit",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]],false);
function f69(c,args,k){return enterFunction(b69,[468,469,470,471],null,c,args,k,false,false,[false,true,true,true],false);}

function d70(l474,l475){for(;;){t2:{const t1=unref(l474);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return l475;break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l476=t1.fields[0];let l477=t1.fields[1];return dcons("Cons",[null,null],[dcons("SiSym",[null],[copyValue(l476)],false,"SynItem",true),d70(l477,l475)],false,"List",true);break t2;}throw new Error('no arm of the match fits');}}}
function f70(c,args,k){return direct(d70,g70,c,args,k,[1,0]);}

const b70 = matchValue(borrowPlace(474,[],true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(475,false,false,true)],[['ctor',"Cons",[['bind',476,true,false],['bind',477,true,false]],"List"],pure(true),values([values([readLocal(476,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("SiSym",[null],vs,[0],false,"SynItem",true)))),callFunction(pure(f70),[readLocal(477,false,false,false),readLocal(475,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]],false);
function g70(c,args,k){return enterFunction(b70,[474,475],null,c,args,k,false,false,[false,true],false);}

const b71 = callFunction(pure(f103),[callFunction(pure(f67),[readLocal(482,false,true,false),readLocal(481,false,true,false)],false),borrowPlace(478,[],true),readLocal(479,false,false,true),callFunction(pure(f84),[mapValue(readLocal(478,false,false,false),v=>field(v,"dfa_first",null)),readLocal(480,false,false,true)],false),readLocal(481,false,false,true),readLocal(482,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],false);
function f71(c,args,k){return enterFunction(b71,[478,479,480,481,482],null,c,args,k,false,false,[false,true,true,true,true],false);}

const b72 = values([mapValue(readLocal(483,false,false,false),v=>field(v,"classes",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"ascii",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"run_start",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"run_end",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"run_class",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"dfa_first",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"accept_first",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"accept_token",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"accept_kind",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"accept_dfa",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"rows",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"mode_changes",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"dyn_states",null)),mapValue(readLocal(483,false,false,false),v=>field(v,"dyns",null)),readLocal(484,false,false,true),readLocal(485,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("ScanTables",["classes","ascii","run_start","run_end","run_class","dfa_first","accept_first","accept_token","accept_kind","accept_dfa","rows","mode_changes","dyn_states","dyns","held","start"],vs,[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],true,"ScanTables",true))));
function f72(c,args,k){return enterFunction(b72,[483,484,485],null,c,args,k,false,false,[false,true,true],false);}

function d73(l486){l486=small(l486);for(;;){t2:{const t1=unref((l486<(128)));requireDataOwner(t1);if(equal(true,t1)){return (1);break t2;}if(equal(false,t1)){t4:{const t3=unref((l486<(224)));requireDataOwner(t3);if(equal(true,t3)){return (2);break t4;}if(equal(false,t3)){t6:{const t5=unref((l486<(240)));requireDataOwner(t5);if(equal(true,t5)){return (3);break t6;}if(equal(false,t5)){return (4);break t6;}throw new Error('no arm of the match fits');}break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f73(c,args,k){return direct((...a)=>big(d73(...a)),g73,c,args,k,[0]);}

const b73 = matchValue(values([readLocal(486,false,true,false),pure(128n)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),pure(1n)],[['literal',false],pure(true),matchValue(values([readLocal(486,false,true,false),pure(224n)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),pure(2n)],[['literal',false],pure(true),matchValue(values([readLocal(486,false,false,true),pure(240n)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),pure(3n)],[['literal',false],pure(true),pure(4n)]],false)]],false)]],false);
function g73(c,args,k){return enterFunction(b73,[486],null,c,args,k,false,false,[true],false);}

function d74(l487,l488){l488=small(l488);for(;;){t2:{const t1=unref(d37(l487,l488));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return (0);break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l489=small(t1.fields[0]);return l489;break t2;}throw new Error('no arm of the match fits');}}}
function f74(c,args,k){return direct((...a)=>big(d74(...a)),g74,c,args,k,[0,0]);}

const b74 = matchValue(callFunction(pure(f37),[readLocal(487,false,false,true),readLocal(488,false,false,true)],false),[[['ctor',"None",[],"Option"],pure(true),pure(0n)],[['ctor',"Some",[['bind',489,false,true]],"Option"],pure(true),readLocal(489,false,false,true)]],false);
function g74(c,args,k){return enterFunction(b74,[487,488],null,c,args,k,false,false,[true,true],false);}

const b75 = callFunction(pure(f104),[mapValue(callFunction(pure(f105),[mapValue(readLocal(490,false,false,false),v=>field(v,"mode_changes",null)),mapValue(readLocal(491,false,false,false),v=>field(v,"current",null)),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false),v=>temporaryRef(v,true)),readLocal(491,false,false,true),readLocal(492,false,false,true)],false);
function f75(c,args,k){return enterFunction(b75,[490,491,492],null,c,args,k,false,false,[false,true,true],false);}

const b76 = matchValue(callFunction(pure(f106),[mapValue(mapValue(readLocal(493,false,false,false),v=>field(v,"dyns",null)),v=>temporaryRef(v,true)),readLocal(495,false,false,true)],false),[[['ctor',"None",[],"Option"],pure(true),mapValue(readLocal(493,false,false,false),v=>field(v,"held",null))],[['ctor',"Some",[['bind',498,false,true]],"Option"],pure(true),sequence([defineLocal(499,false,callFunction(pure(f107),[mapValue(mapValue(readLocal(493,false,false,false),v=>field(v,"dyn_states",null)),v=>temporaryRef(v,true)),mapValue(readLocal(498,false,false,false),v=>field(v,"state",null))],false),true),defineLocal(500,false,callFunction(pure(f108),[borrowPlace(493,[],true),readLocal(494,false,true,false),mapValue(readLocal(498,false,false,false),v=>field(v,"prefix",null)),readLocal(496,false,false,true),readLocal(497,false,true,false)],false),true),sequence([defineLocal(501,false,mapValue(readLocal(498,false,false,false),v=>field(v,"op",null)),true),branch(values([readLocal(501,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([matchValue(callFunction(pure(f109),[borrowPlace(493,[],true),readLocal(494,false,false,true),borrowPlace(498,[],false),borrowPlace(499,[],false),borrowPlace(500,[],false),readLocal(497,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],false),[[['ctor',"None",[],"Option"],pure(true),callFunction(pure(f110),[mapValue(readLocal(493,false,false,false),v=>field(v,"held",null)),mapValue(readLocal(498,false,false,false),v=>field(v,"state",null)),values([],(c,vs,k)=>more(()=>k(c,construct("ScanHeldNone",[],vs,[],false,"ScanHeld",true))))],false)],[['ctor',"Some",[['bind',502,false,true]],"Option"],pure(true),callFunction(pure(f110),[mapValue(readLocal(493,false,false,false),v=>field(v,"held",null)),mapValue(readLocal(498,false,false,false),v=>field(v,"state",null)),values([readLocal(502,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("ScanHeldCount",[null],vs,[0],false,"ScanHeld",true))))],false)]],false)]),sequence([defineLocal(503,false,values([readLocal(501,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(504,false,readLocal(503,false,false,true),true),branch(values([readLocal(504,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([mapValue(readLocal(493,false,false,false),v=>field(v,"held",null))]),sequence([defineLocal(505,false,values([readLocal(504,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(506,false,readLocal(505,false,false,true),true),branch(values([readLocal(506,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([matchValue(callFunction(pure(f111),[borrowPlace(493,[],true),readLocal(494,false,true,false),borrowPlace(498,[],false),borrowPlace(500,[],false),readLocal(497,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],false),[[['ctor',"None",[],"Option"],pure(true),callFunction(pure(f110),[mapValue(readLocal(493,false,false,false),v=>field(v,"held",null)),mapValue(readLocal(498,false,false,false),v=>field(v,"state",null)),values([],(c,vs,k)=>more(()=>k(c,construct("ScanHeldNone",[],vs,[],false,"ScanHeld",true))))],false)],[['ctor',"Some",[['ctor',"Pair",[['bind',507,false,true],['bind',508,false,true]],"Pair"]],"Option"],pure(true),callFunction(pure(f110),[mapValue(readLocal(493,false,false,false),v=>field(v,"held",null)),mapValue(readLocal(498,false,false,false),v=>field(v,"state",null)),values([callFunction(pure(f41),[readLocal(494,false,false,true),readLocal(507,false,false,true),readLocal(508,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("ScanHeldText",[null],vs,[0],false,"ScanHeld",true))))],false)]],false)]),sequence([defineLocal(509,false,values([readLocal(506,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),mapValue(readLocal(493,false,false,false),v=>field(v,"held",null))]))])]))])]))])])]],false);
function f76(c,args,k){return enterFunction(b76,[493,494,495,496,497],null,c,args,k,false,false,[false,true,true,true,true],false);}

function d77(l510,l511){for(;;){t2:{const t1=unref(l510);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return l511;break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l512=t1.fields[0];let l513=t1.fields[1];const t3=l513;const t4=dcons("Cons",[null,null],[l512,l511],false,"List",true);l510=t3;l511=t4;continue;break t2;}throw new Error('no arm of the match fits');}}}
function f77(c,args,k){return g77(c,args,k);}

const b77 = matchValue(readLocal(510,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(511,false,false,true)],[['ctor',"Cons",[['bind',512,false,true],['bind',513,false,true]],"List"],pure(true),tailSelfCall(pure(f77),[readLocal(513,false,false,true),values([readLocal(512,false,false,true),readLocal(511,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])]],true);
function g77(c,args,k){return enterFunction(b77,[510,511],null,c,args,k,false,true,[true,true],true);}

function d78(l514){l514=small(l514);for(;;){return (((48)<=l514)&&(l514<(58)));}}
function f78(c,args,k){return direct(d78,g78,c,args,k,[0]);}

const b78 = branch(values([pure(48n),readLocal(514,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),values([readLocal(514,false,false,true),pure(58n)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),pure(false));
function g78(c,args,k){return enterFunction(b78,[514],null,c,args,k,false,false,[true],false);}

function d79(l515,l516){l515=small(l515);for(;;){{let l517=l515;if((l517==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l516],true,"Pair",true);}}else{{let l518=isub(l517,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d23((3),l516));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l519=t1.fields[0];let l520=t1.fields[1];t4:{const t3=unref(d79(l518,l520));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l521=t3.fields[0];let l522=t3.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[dcons("SynAction",["terminal","kind","arg"],[big(d27(copyValue(l519),(0))),big(d27(copyValue(l519),(1))),big(d27(l519,(2)))],true,"SynAction",true),l521],false,"List",true),l522],true,"Pair",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f79(c,args,k){return direct(d79,g79,c,args,k,[0,0]);}

const b79 = sequence([defineLocal(517,false,readLocal(515,false,false,true),true),branch(values([readLocal(517,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(516,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(518,false,values([readLocal(517,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f23),[pure(3n),readLocal(516,false,false,true)],false),[[['ctor',"Pair",[['bind',519,false,true],['bind',520,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f79),[readLocal(518,false,false,true),readLocal(520,false,false,true)],false),[[['ctor',"Pair",[['bind',521,false,true],['bind',522,false,true]],"Pair"],pure(true),values([values([values([callFunction(pure(f27),[readLocal(519,false,true,false),pure(0n)],false),callFunction(pure(f27),[readLocal(519,false,true,false),pure(1n)],false),callFunction(pure(f27),[readLocal(519,false,false,true),pure(2n)],false)],(c,vs,k)=>more(()=>k(c,construct("SynAction",["terminal","kind","arg"],vs,[0,1,2],true,"SynAction",true)))),readLocal(521,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(522,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]))]);
function g79(c,args,k){return enterFunction(b79,[515,516],null,c,args,k,false,false,[true,true],false);}

function d80(l523,l524){l523=small(l523);for(;;){{let l525=l523;if((l525==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l524],true,"Pair",true);}}else{{let l526=isub(l525,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d23((2),l524));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l527=t1.fields[0];let l528=t1.fields[1];t4:{const t3=unref(d80(l526,l528));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l529=t3.fields[0];let l530=t3.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[dcons("SynGoto",["non_terminal","state"],[big(d27(copyValue(l527),(0))),big(d27(l527,(1)))],true,"SynGoto",true),l529],false,"List",true),l530],true,"Pair",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f80(c,args,k){return direct(d80,g80,c,args,k,[0,0]);}

const b80 = sequence([defineLocal(525,false,readLocal(523,false,false,true),true),branch(values([readLocal(525,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(524,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(526,false,values([readLocal(525,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f23),[pure(2n),readLocal(524,false,false,true)],false),[[['ctor',"Pair",[['bind',527,false,true],['bind',528,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f80),[readLocal(526,false,false,true),readLocal(528,false,false,true)],false),[[['ctor',"Pair",[['bind',529,false,true],['bind',530,false,true]],"Pair"],pure(true),values([values([values([callFunction(pure(f27),[readLocal(527,false,true,false),pure(0n)],false),callFunction(pure(f27),[readLocal(527,false,false,true),pure(1n)],false)],(c,vs,k)=>more(()=>k(c,construct("SynGoto",["non_terminal","state"],vs,[0,1],true,"SynGoto",true)))),readLocal(529,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(530,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]))]);
function g80(c,args,k){return enterFunction(b80,[523,524],null,c,args,k,false,false,[true,true],false);}

function d81(l531,l532){l531=small(l531);for(;;){{let l533=l531;if((l533==(0))){{return dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),l532],true,"Pair",true);}}else{{let l534=isub(l533,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(d23((4),l532));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l535=t1.fields[0];let l536=t1.fields[1];t4:{const t3=unref(d81(l534,l536));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l537=t3.fields[0];let l538=t3.fields[1];return dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[dcons("SynTrans",["state","terminal","to","production"],[big(d27(copyValue(l535),(0))),big(d27(copyValue(l535),(1))),big(d27(copyValue(l535),(2))),big(d27(l535,(3)))],true,"SynTrans",true),l537],false,"List",true),l538],true,"Pair",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f81(c,args,k){return direct(d81,g81,c,args,k,[0,0]);}

const b81 = sequence([defineLocal(533,false,readLocal(531,false,false,true),true),branch(values([readLocal(533,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(532,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(534,false,values([readLocal(533,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f23),[pure(4n),readLocal(532,false,false,true)],false),[[['ctor',"Pair",[['bind',535,false,true],['bind',536,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f81),[readLocal(534,false,false,true),readLocal(536,false,false,true)],false),[[['ctor',"Pair",[['bind',537,false,true],['bind',538,false,true]],"Pair"],pure(true),values([values([values([callFunction(pure(f27),[readLocal(535,false,true,false),pure(0n)],false),callFunction(pure(f27),[readLocal(535,false,true,false),pure(1n)],false),callFunction(pure(f27),[readLocal(535,false,true,false),pure(2n)],false),callFunction(pure(f27),[readLocal(535,false,false,true),pure(3n)],false)],(c,vs,k)=>more(()=>k(c,construct("SynTrans",["state","terminal","to","production"],vs,[0,1,2,3],true,"SynTrans",true)))),readLocal(537,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(538,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]))]);
function g81(c,args,k){return enterFunction(b81,[531,532],null,c,args,k,false,false,[true,true],false);}

function d82(l539){for(;;){t2:{const t1=unref(d18(l539));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l540=small(t1.fields[0]);let l541=t1.fields[1];t4:{const t3=unref(d20(l541));requireDataOwner(t3);if(t3.tag==="Pair"&&t3.owner==="Pair"){let l542=t3.fields[0];let l543=t3.fields[1];t6:{const t5=unref(d19(l543));requireDataOwner(t5);if(t5.tag==="Pair"&&t5.owner==="Pair"){let l544=t5.fields[0];let l545=t5.fields[1];return dcons("Pair",["fst","snd"],[dcons("SeNode",[null,null,null],[big(l540),l542,l544],false,"SynElem",true),l545],true,"Pair",true);break t6;}throw new Error('no arm of the match fits');}break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f82(c,args,k){return direct(d82,g82,c,args,k,[0]);}

const b82 = matchValue(callFunction(pure(f18),[readLocal(539,false,false,true)],false),[[['ctor',"Pair",[['bind',540,false,true],['bind',541,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f20),[readLocal(541,false,false,true)],false),[[['ctor',"Pair",[['bind',542,false,true],['bind',543,false,true]],"Pair"],pure(true),matchValue(callFunction(pure(f19),[readLocal(543,false,false,true)],false),[[['ctor',"Pair",[['bind',544,false,true],['bind',545,false,true]],"Pair"],pure(true),values([values([readLocal(540,false,false,true),readLocal(542,false,true,false),readLocal(544,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SeNode",[null,null,null],vs,[0,1,2],false,"SynElem",true)))),readLocal(545,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]],false)]],false)]],false);
function g82(c,args,k){return enterFunction(b82,[539],null,c,args,k,false,false,[true],false);}

function d83(l546){for(;;){t2:{const t1=unref(d18(l546));requireDataOwner(t1);if(t1.tag==="Pair"&&t1.owner==="Pair"){let l547=small(t1.fields[0]);let l548=t1.fields[1];if((l547==(0))){return dcons("Pair",["fst","snd"],[dcons("SeItem",[],[],false,"SynElem",true),l548],true,"Pair",true);}else{if((l547==(1))){return d82(l548);}else{return dcons("Pair",["fst","snd"],[dcons("SeItem",[],[],false,"SynElem",true),d26(l548)],true,"Pair",true);}}break t2;}throw new Error('no arm of the match fits');}}}
function f83(c,args,k){return direct(d83,g83,c,args,k,[0]);}

const b83 = matchValue(callFunction(pure(f18),[readLocal(546,false,false,true)],false),[[['ctor',"Pair",[['bind',547,false,true],['bind',548,false,true]],"Pair"],pure(true),branch(values([readLocal(547,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),values([values([],(c,vs,k)=>more(()=>k(c,construct("SeItem",[],vs,[],false,"SynElem",true)))),readLocal(548,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true)))),branch(values([readLocal(547,false,false,true),pure(1n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),callFunction(pure(f82),[readLocal(548,false,false,true)],false),values([values([],(c,vs,k)=>more(()=>k(c,construct("SeItem",[],vs,[],false,"SynElem",true)))),callFunction(pure(f26),[borrowPlace(548,[],false)],false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))))]],false);
function g83(c,args,k){return enterFunction(b83,[546],null,c,args,k,false,false,[true],false);}

function d84(l549,l550){l550=small(l550);for(;;){return small(d105(l549,l550,big((0))));}}
function f84(c,args,k){return direct((...a)=>big(d84(...a)),g84,c,args,k,[0,0]);}

const b84 = callFunction(pure(f105),[readLocal(549,false,false,true),readLocal(550,false,false,true),pure(0n)],false);
function g84(c,args,k){return enterFunction(b84,[549,550],null,c,args,k,false,false,[true,true],false);}

function d85(l551,l552,l553,l554){l551=small(l551);l553=small(l553);l554=small(l554);for(;;){{let l555=l551;if((l555==(0))){{return dcons("Nil",[],[],false,"List",true);}}else{{let l556=isub(l555,(1),0,9007199254740991,0n,Infinity);return dcons("Cons",[null,null],[big(d84(copyValue(l552),l553)),d85(l556,l552,iadd(l553,l554,0,9007199254740991,0n,Infinity),l554)],false,"List",true);}}}}}
function f85(c,args,k){return direct(d85,g85,c,args,k,[0,0,0,0]);}

const b85 = sequence([defineLocal(555,false,readLocal(551,false,false,true),true),branch(values([readLocal(555,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))]),sequence([defineLocal(556,false,values([readLocal(555,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),values([callFunction(pure(f84),[readLocal(552,false,true,false),readLocal(553,false,true,false)],false),callFunction(pure(f85),[readLocal(556,false,false,true),readLocal(552,false,false,true),values([readLocal(553,false,false,true),readLocal(554,false,true,false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(554,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]))]);
function g85(c,args,k){return enterFunction(b85,[551,552,553,554],null,c,args,k,false,false,[true,true,true,true],false);}

function d86(l557,l558,l559,l560){l557=small(l557);l559=small(l559);for(;;){{let l561=l557;if((l561==(0))){{return dcons("Pair",["fst","snd"],[l560,big(l559)],true,"Pair",true);}}else{{let l562=isub(l561,(1),0,9007199254740991,0n,Infinity);const t1=l562;const t2=copyValue(l558);const t3=iadd(iadd(l559,(1),0,9007199254740991,0n,Infinity),imul(d84(copyValue(l558),l559),(3),0,9007199254740991,0n,Infinity),0,9007199254740991,0n,Infinity);const t4=dcons("Cons",[null,null],[d112(d84(copyValue(l558),l559),copyValue(l558),iadd(l559,(1),0,9007199254740991,0n,Infinity),dcons("Nil",[],[],false,"List",true)),l560],false,"List",true);l557=t1;l558=t2;l559=t3;l560=t4;continue;}}}}}
function f86(c,args,k){return direct(d86,g86,c,args,k,[0,0,0,0]);}

const b86 = sequence([defineLocal(561,false,readLocal(557,false,false,true),true),branch(values([readLocal(561,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([readLocal(560,false,false,true),readLocal(559,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(562,false,values([readLocal(561,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f86),[readLocal(562,false,false,true),readLocal(558,false,true,false),values([values([readLocal(559,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([callFunction(pure(f84),[readLocal(558,false,true,false),readLocal(559,false,true,false)],false),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([callFunction(pure(f112),[callFunction(pure(f84),[readLocal(558,false,true,false),readLocal(559,false,true,false)],false),readLocal(558,false,true,false),values([readLocal(559,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false),readLocal(560,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])]))]);
function g86(c,args,k){return enterFunction(b86,[557,558,559,560],null,c,args,k,false,false,[true,true,true,true],true);}

function d87(l563,l564,l565,l566,l567){l563=small(l563);l564=small(l564);for(;;){{let l568=l563;if((l568==(0))){{return l567;}}else{{let l569=isub(l568,(1),0,9007199254740991,0n,Infinity);const t1=l569;const t2=l564;const t3=copyValue(l565);const t4=copyValue(l566);const t5=d113(d84(copyValue(l565),small(l567.fields[0])),d114(d84(copyValue(l565),small(l567.fields[0])),l564,copyValue(l565),copyValue(l566),dcons("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],[big(iadd(small(l567.fields[0]),(1),0,9007199254740991,0n,Infinity)),big(small(l567.fields[1])),big(small(l567.fields[2])),big(small(l567.fields[3])),dcons("Cons",[null,null],[big(small(l567.fields[2])),copyValue(l567.fields[4])],false,"List",true),copyValue(l567.fields[5]),copyValue(l567.fields[6]),copyValue(l567.fields[7]),copyValue(l567.fields[8]),copyValue(l567.fields[9])],true,"ScanBuild",true)));l563=t1;l564=t2;l565=t3;l566=t4;l567=t5;continue;}}}}}
function f87(c,args,k){return direct(d87,g87,c,args,k,[0,0,0,0,0]);}

const b87 = sequence([defineLocal(568,false,readLocal(563,false,false,true),true),branch(values([readLocal(568,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(567,false,false,true)]),sequence([defineLocal(569,false,values([readLocal(568,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f87),[readLocal(569,false,false,true),readLocal(564,false,true,false),readLocal(565,false,true,false),readLocal(566,false,true,false),callFunction(pure(f113),[callFunction(pure(f84),[readLocal(565,false,true,false),mapValue(readLocal(567,false,false,false),v=>field(v,"sp",null))],false),callFunction(pure(f114),[callFunction(pure(f84),[readLocal(565,false,true,false),mapValue(readLocal(567,false,false,false),v=>field(v,"sp",null))],false),readLocal(564,false,true,false),readLocal(565,false,true,false),readLocal(566,false,true,false),values([values([mapValue(readLocal(567,false,false,false),v=>field(v,"sp",null)),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),mapValue(readLocal(567,false,false,false),v=>field(v,"rp",null)),mapValue(readLocal(567,false,false,false),v=>field(v,"total",null)),mapValue(readLocal(567,false,false,false),v=>field(v,"accepts",null)),values([mapValue(readLocal(567,false,false,false),v=>field(v,"total",null)),mapValue(readLocal(567,false,false,false),v=>field(v,"built_dfa_first",null))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),mapValue(readLocal(567,false,false,false),v=>field(v,"built_accept_first",null)),mapValue(readLocal(567,false,false,false),v=>field(v,"built_accept_token",null)),mapValue(readLocal(567,false,false,false),v=>field(v,"built_accept_kind",null)),mapValue(readLocal(567,false,false,false),v=>field(v,"built_accept_dfa",null)),mapValue(readLocal(567,false,false,false),v=>field(v,"built_rows",null))],(c,vs,k)=>more(()=>k(c,construct("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],vs,[0,1,2,3,4,5,6,7,8,9],true,"ScanBuild",true))))],false)],false)])]))]);
function g87(c,args,k){return enterFunction(b87,[563,564,565,566,567],null,c,args,k,false,false,[true,true,true,true,true],true);}

function d88(l570,l571,l572,l573){l570=small(l570);l572=small(l572);for(;;){{let l574=l570;if((l574==(0))){{return d38(l573);}}else{{let l575=isub(l574,(1),0,9007199254740991,0n,Infinity);const t1=l575;const t2=copyValue(l571);const t3=iadd(l572,(3),0,9007199254740991,0n,Infinity);const t4=dcons("Cons",[null,null],[dcons("ScanDynState",["kind","min","max"],[big(small(d105(copyValue(l571),l572,big((0))))),big(small(d105(copyValue(l571),iadd(l572,(1),0,9007199254740991,0n,Infinity),big((0))))),big(small(d105(copyValue(l571),iadd(l572,(2),0,9007199254740991,0n,Infinity),big((0)))))],true,"ScanDynState",true),l573],false,"List",true);l570=t1;l571=t2;l572=t3;l573=t4;continue;}}}}}
function f88(c,args,k){return direct(d88,g88,c,args,k,[0,0,0,0]);}

const b88 = sequence([defineLocal(574,false,readLocal(570,false,false,true),true),branch(values([readLocal(574,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([callFunction(pure(f38),[readLocal(573,false,false,true)],false)]),sequence([defineLocal(575,false,values([readLocal(574,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f88),[readLocal(575,false,false,true),readLocal(571,false,true,false),values([readLocal(572,false,true,false),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([values([callFunction(pure(f105),[readLocal(571,false,true,false),readLocal(572,false,true,false),pure(0n)],false),callFunction(pure(f105),[readLocal(571,false,true,false),values([readLocal(572,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false),callFunction(pure(f105),[readLocal(571,false,true,false),values([readLocal(572,false,false,true),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false)],(c,vs,k)=>more(()=>k(c,construct("ScanDynState",["kind","min","max"],vs,[0,1,2],true,"ScanDynState",true)))),readLocal(573,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])]))]);
function g88(c,args,k){return enterFunction(b88,[570,571,572,573],null,c,args,k,false,false,[true,true,true,true],true);}

const b89 = sequence([defineLocal(580,false,readLocal(576,false,false,true),true),branch(values([readLocal(580,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([callFunction(pure(f38),[readLocal(579,false,false,true)],false),readLocal(578,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]),sequence([defineLocal(581,false,values([readLocal(580,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(582,false,callFunction(pure(f115),[readLocal(577,false,true,false),readLocal(578,false,false,true)],false),true),tailSelfCall(pure(f89),[readLocal(581,false,false,true),readLocal(577,false,false,true),mapValue(readLocal(582,false,false,false),v=>field(v,"snd",1)),values([mapValue(readLocal(582,false,false,false),v=>field(v,"fst",0)),readLocal(579,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])])]))]);
function f89(c,args,k){return enterFunction(b89,[576,577,578,579],null,c,args,k,false,false,[true,true,true,true],true);}

function d90(l583,l584){l583=small(l583);for(;;){return (l583<=small(pureBuiltin("Nat::of_u64",[big(l584.items.length)])));}}
function f90(c,args,k){return direct(d90,g90,c,args,k,[0,0]);}

const b90 = values([readLocal(583,false,false,true),builtin("Nat::of_u64",[builtin("Array::len",[readLocal(584,false,false,true)])])],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1])));
function g90(c,args,k){return enterFunction(b90,[583,584],null,c,args,k,false,false,[true,true],false);}

function d91(l585,l586,l587,l588,l589){l585=small(l585);l589=small(l589);for(;;){{let l590=l585;if((l590==(0))){{return dcons("Nil",[],[],false,"List",true);}}else{{let l591=isub(l590,(1),0,9007199254740991,0n,Infinity);return dcons("Cons",[null,null],[big(d116(copyValue(l586),copyValue(l587),copyValue(l588),l589)),d91(l591,l586,l587,l588,iadd(l589,(1),0,9007199254740991,0n,Infinity))],false,"List",true);}}}}}
function f91(c,args,k){return direct(d91,g91,c,args,k,[0,0,0,0,0]);}

const b91 = sequence([defineLocal(590,false,readLocal(585,false,false,true),true),branch(values([readLocal(590,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))]),sequence([defineLocal(591,false,values([readLocal(590,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),values([callFunction(pure(f116),[readLocal(586,false,true,false),readLocal(587,false,true,false),readLocal(588,false,true,false),readLocal(589,false,true,false)],false),callFunction(pure(f91),[readLocal(591,false,false,true),readLocal(586,false,false,true),readLocal(587,false,false,true),readLocal(588,false,false,true),values([readLocal(589,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]))]);
function g91(c,args,k){return enterFunction(b91,[585,586,587,588,589],null,c,args,k,false,false,[true,true,true,true,true],false);}

const b92 = builtin("Array::of_list",[callFunction(pure(f38),[readLocal(592,false,false,true)],false)]);
function f92(c,args,k){return enterFunction(b92,[592],null,c,args,k,false,false,[true],false);}

function d93(l593,l594,l595,l596,l597,l598){l593=small(l593);l595=small(l595);l596=small(l596);for(;;){{let l599=l593;if((l599==(0))){{t2:{const t1=unref(l597);requireDataOwner(t1);if(equal(true,t1)){return d38(dcons("Cons",[null,null],[big(l596),l598],false,"List",true));break t2;}if(equal(false,t1)){return d38(l598);break t2;}throw new Error('no arm of the match fits');}}}else{{let l600=isub(l599,(1),0,9007199254740991,0n,Infinity);t4:{const t3=unref(d117(d74(l594,l595)));requireDataOwner(t3);if(t3.tag==="Some"&&t3.owner==="Option"){let l601=small(t3.fields[0]);const t5=l600;const t6=l594;const t7=iadd(l595,(1),0,9007199254740991,0n,Infinity);const t8=iadd(imul(l596,(10),0,9007199254740991,0n,Infinity),l601,0,9007199254740991,0n,Infinity);const t9=true;const t10=l598;l593=t5;l594=t6;l595=t7;l596=t8;l597=t9;l598=t10;continue;break t4;}if(t3.tag==="None"&&t3.owner==="Option"){t12:{const t11=unref(l597);requireDataOwner(t11);if(equal(true,t11)){const t13=l600;const t14=l594;const t15=iadd(l595,(1),0,9007199254740991,0n,Infinity);const t16=(0);const t17=false;const t18=dcons("Cons",[null,null],[big(l596),l598],false,"List",true);l593=t13;l594=t14;l595=t15;l596=t16;l597=t17;l598=t18;continue;break t12;}if(equal(false,t11)){const t19=l600;const t20=l594;const t21=iadd(l595,(1),0,9007199254740991,0n,Infinity);const t22=(0);const t23=false;const t24=l598;l593=t19;l594=t20;l595=t21;l596=t22;l597=t23;l598=t24;continue;break t12;}throw new Error('no arm of the match fits');}break t4;}throw new Error('no arm of the match fits');}}}}}}
function f93(c,args,k){return direct(d93,g93,c,args,k,[0,0,0,0,0,0]);}

const b93 = sequence([defineLocal(599,false,readLocal(593,false,false,true),true),branch(values([readLocal(599,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([matchValue(readLocal(597,false,true,false),[[['literal',true],pure(true),callFunction(pure(f38),[values([readLocal(596,false,false,true),readLocal(598,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],false)],[['literal',false],pure(true),callFunction(pure(f38),[readLocal(598,false,false,true)],false)]],true)]),sequence([defineLocal(600,false,values([readLocal(599,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f117),[callFunction(pure(f74),[readLocal(594,false,true,false),readLocal(595,false,true,false)],false)],false),[[['ctor',"Some",[['bind',601,false,true]],"Option"],pure(true),tailSelfCall(pure(f93),[readLocal(600,false,false,true),readLocal(594,false,false,true),values([readLocal(595,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([values([readLocal(596,false,false,true),pure(10n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),readLocal(601,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(true),readLocal(598,false,false,true)])],[['ctor',"None",[],"Option"],pure(true),matchValue(readLocal(597,false,true,false),[[['literal',true],pure(true),tailSelfCall(pure(f93),[readLocal(600,false,false,true),readLocal(594,false,false,true),values([readLocal(595,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n),pure(false),values([readLocal(596,false,false,true),readLocal(598,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])],[['literal',false],pure(true),tailSelfCall(pure(f93),[readLocal(600,false,false,true),readLocal(594,false,false,true),values([readLocal(595,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n),pure(false),readLocal(598,false,false,true)])]],true)]],false)]))]);
function g93(c,args,k){return enterFunction(b93,[593,594,595,596,597,598],null,c,args,k,false,false,[true,true,true,true,true,true],true);}

function d94(l602){for(;;){t2:{const t1=unref(l602);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("Nil",[],[],false,"List",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l603=t1.fields[0];let l604=t1.fields[1];return dcons("Cons",[null,null],[dcons("VText",[null],[l603],false,"SynVal",true),d94(l604)],false,"List",true);break t2;}throw new Error('no arm of the match fits');}}}
function f94(c,args,k){return direct(d94,g94,c,args,k,[1]);}

const b94 = matchValue(borrowPlace(602,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',603,true,false],['bind',604,true,false]],"List"],pure(true),values([values([readLocal(603,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("VText",[null],vs,[0],false,"SynVal",true)))),callFunction(pure(f94),[readLocal(604,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]],false);
function g94(c,args,k){return enterFunction(b94,[602],null,c,args,k,false,false,[false],false);}

const b95 = values([mapValue(readLocal(605,false,false,false),v=>field(v,"span",null)),values([values([readLocal(606,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("VNat",[null],vs,[0],false,"SynVal",true)))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("VData",[null,null],vs,[0,1],false,"SynVal",true))));
function f95(c,args,k){return enterFunction(b95,[605,606],null,c,args,k,false,false,[false,true],false);}

function d96(l607,l608){l608=small(l608);for(;;){t2:{const t1=unref(l607);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return l608;break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l609=t1.fields[0];let l610=t1.fields[1];const t3=l610;const t4=d118(l608,d119(l609));l607=t3;l608=t4;continue;break t2;}throw new Error('no arm of the match fits');}}}
function f96(c,args,k){return direct((...a)=>big(d96(...a)),g96,c,args,k,[1,0]);}

const b96 = matchValue(borrowPlace(607,[],true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(608,false,false,true)],[['ctor',"Cons",[['bind',609,true,false],['bind',610,true,false]],"List"],pure(true),tailSelfCall(pure(f96),[readLocal(610,false,false,false),callFunction(pure(f118),[readLocal(608,false,false,true),callFunction(pure(f119),[readLocal(609,false,false,false)],false)],false)])]],false);
function g96(c,args,k){return enterFunction(b96,[607,608],null,c,args,k,false,false,[false,true],true);}

function d97(l611){for(;;){t2:{const t1=unref(l611);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("None",[],[],false,"Option",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l612=t1.fields[0];let l613=t1.fields[1];if(d120(l612)){return dcons("Some",[null],[big(d121(l612))],false,"Option",true);}else{const t3=l613;l611=t3;continue;}break t2;}throw new Error('no arm of the match fits');}}}
function f97(c,args,k){return direct(d97,g97,c,args,k,[1]);}

const b97 = matchValue(borrowPlace(611,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Cons",[['bind',612,true,false],['bind',613,true,false]],"List"],pure(true),branch(callFunction(pure(f120),[readLocal(612,false,false,false)],false),values([callFunction(pure(f121),[readLocal(612,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),tailSelfCall(pure(f97),[readLocal(613,false,false,false)]))]],false);
function g97(c,args,k){return enterFunction(b97,[611],null,c,args,k,false,false,[false],true);}

const b98 = sequence([defineLocal(620,false,callFunction(pure(f122),[mapValue(readLocal(614,false,false,false),v=>field(v,"lr",null)),readLocal(618,false,false,false),readLocal(617,false,false,false)],false),true),values([readLocal(615,false,false,true),branch(readLocal(616,false,true,false),values([callFunction(pure(f95),[borrowPlace(614,[],true),readLocal(619,false,false,true)],false),readLocal(620,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),readLocal(620,false,false,true))],(c,vs,k)=>more(()=>k(c,construct("VData",[null,null],vs,[0,1],false,"SynVal",true))))]);
function f98(c,args,k){return enterFunction(b98,[614,615,616,617,618,619],null,c,args,k,false,false,[false,true,true,false,false,true],false);}

function d99(l621,l622,l623){l622=small(l622);l623=small(l623);for(;;){t2:{const t1=unref(l621);requireDataOwner(t1);if(t1.tag==="SvOne"&&t1.owner==="SynV"){let l624=t1.fields[0];let l625=small(t1.fields[1]);let l626=small(t1.fields[2]);return dcons("SvOne",[null,null,null],[copyValue(l624),big(l622),big(l623)],false,"SynV",true);break t2;}if(t1.tag==="SvOpt"&&t1.owner==="SynV"){let l627=t1.fields[0];let l628=small(t1.fields[1]);let l629=small(t1.fields[2]);return dcons("SvOpt",[null,null,null],[copyValue(l627),big(l622),big(l623)],false,"SynV",true);break t2;}if(t1.tag==="SvList"&&t1.owner==="SynV"){let l630=t1.fields[0];let l631=small(t1.fields[1]);let l632=small(t1.fields[2]);return dcons("SvList",[null,null,null],[copyValue(l630),big(l622),big(l623)],false,"SynV",true);break t2;}throw new Error('no arm of the match fits');}}}
function f99(c,args,k){return direct(d99,g99,c,args,k,[1,0,0]);}

const b99 = matchValue(borrowPlace(621,[],true),[[['ctor',"SvOne",[['bind',624,true,false],['bind',625,true,false],['bind',626,true,false]],"SynV"],pure(true),values([readLocal(624,true,true,false),readLocal(622,false,false,true),readLocal(623,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SvOne",[null,null,null],vs,[0,1,2],false,"SynV",true))))],[['ctor',"SvOpt",[['bind',627,true,false],['bind',628,true,false],['bind',629,true,false]],"SynV"],pure(true),values([readLocal(627,true,true,false),readLocal(622,false,false,true),readLocal(623,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SvOpt",[null,null,null],vs,[0,1,2],false,"SynV",true))))],[['ctor',"SvList",[['bind',630,true,false],['bind',631,true,false],['bind',632,true,false]],"SynV"],pure(true),values([readLocal(630,true,true,false),readLocal(622,false,false,true),readLocal(623,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("SvList",[null,null,null],vs,[0,1,2],false,"SynV",true))))]],false);
function g99(c,args,k){return enterFunction(b99,[621,622,623],null,c,args,k,false,false,[false,true,true],false);}

const b100 = matchValue(borrowPlace(634,[],true),[[['ctor',"SeItem",[],"SynElem"],pure(true),matchValue(borrowPlace(635,[],true),[[['ctor',"Cons",[['bind',637,true,false],['bind',638,true,false]],"List"],pure(true),matchValue(borrowPlace(638,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([callFunction(pure(f34),[mapValue(readLocal(633,false,false,false),v=>field(v,"lr",null)),readLocal(637,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))],[['ctor',"Cons",[['bind',639,true,false],['bind',640,true,false]],"List"],pure(true),values([values([pure("a single-item element does not have one item")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]],false)],[['ctor',"Nil",[],"List"],pure(true),values([values([pure("a single-item element does not have one item")],(c,vs,k)=>more(()=>k(c,construct("SfSchema",[null],vs,[0],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]],false)],[['ctor',"SeNode",[['bind',641,true,false],['bind',642,true,false],['bind',643,true,false]],"SynElem"],pure(true),values([callFunction(pure(f98),[borrowPlace(633,[],true),readLocal(641,true,true,false),readLocal(642,true,true,false),readLocal(643,false,false,false),readLocal(635,false,false,false),readLocal(636,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))]],false);
function f100(c,args,k){return enterFunction(b100,[633,634,635,636],null,c,args,k,false,false,[false,false,false,true],false);}

function d101(l644){for(;;){t2:{const t1=unref(l644);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("None",[],[],false,"Option",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l645=t1.fields[0];let l646=t1.fields[1];t4:{const t3=unref(d101(l646));requireDataOwner(t3);if(t3.tag==="None"&&t3.owner==="Option"){return dcons("Some",[null],[dcons("Pair",["fst","snd"],[dcons("Nil",[],[],false,"List",true),copyValue(l645)],true,"Pair",true)],false,"Option",true);break t4;}if(t3.tag==="Some"&&t3.owner==="Option"){let l647=t3.fields[0];return dcons("Some",[null],[dcons("Pair",["fst","snd"],[dcons("Cons",[null,null],[copyValue(l645),copyValue(l647.fields[0])],false,"List",true),copyValue(l647.fields[1])],true,"Pair",true)],false,"Option",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f101(c,args,k){return direct(d101,g101,c,args,k,[1]);}

const b101 = matchValue(borrowPlace(644,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Cons",[['bind',645,true,false],['bind',646,true,false]],"List"],pure(true),matchValue(callFunction(pure(f101),[readLocal(646,false,false,false)],false),[[['ctor',"None",[],"Option"],pure(true),values([values([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true)))),readLocal(645,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['ctor',"Some",[['bind',647,false,true]],"Option"],pure(true),values([values([values([readLocal(645,true,true,false),mapValue(readLocal(647,false,false,false),v=>field(v,"fst",0))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),mapValue(readLocal(647,false,false,false),v=>field(v,"snd",1))],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))]],false)]],false);
function g101(c,args,k){return enterFunction(b101,[644],null,c,args,k,false,false,[false],false);}

const b102 = sequence([defineLocal(655,false,readLocal(648,false,false,true),true),branch(values([readLocal(655,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([sequence([defineLocal(656,false,readLocal(654,false,false,true),true),branch(values([readLocal(656,false,true,false),pure(1n)],(c,vs,k)=>more(()=>k(c,vs[0] >= vs[1]))),sequence([defineLocal(657,false,values([readLocal(656,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),values([readLocal(657,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))]),sequence([values([values([builtin("Array::get",[readLocal(650,false,false,true),builtin("U64::of_nat",[readLocal(651,false,false,true)])]),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]))])]),sequence([defineLocal(658,false,values([readLocal(655,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(659,false,readLocal(654,false,false,true),true),branch(values([readLocal(659,false,true,false),pure(1n)],(c,vs,k)=>more(()=>k(c,vs[0] >= vs[1]))),sequence([defineLocal(660,false,values([readLocal(659,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),values([readLocal(660,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Ok",[null],vs,[0],false,"Result",true))))]),sequence([matchValue(callFunction(pure(f123),[mapValue(mapValue(readLocal(649,false,false,false),v=>field(v,"transitions",null)),v=>temporaryRef(v,true)),readLocal(653,false,true,false),callFunction(pure(f59),[readLocal(650,false,true,false),values([readLocal(651,false,true,false),readLocal(652,false,true,false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false)],false),[[['ctor',"Some",[['bind',661,false,true]],"Option"],pure(true),tailSelfCall(pure(f102),[readLocal(658,false,false,true),readLocal(649,false,false,false),readLocal(650,false,false,true),readLocal(651,false,false,true),values([readLocal(652,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),mapValue(readLocal(661,false,false,false),v=>field(v,"to",null)),mapValue(readLocal(661,false,false,false),v=>field(v,"production",null))])],[['ctor',"None",[],"Option"],pure(true),values([values([builtin("Array::get",[readLocal(650,false,false,true),builtin("U64::of_nat",[values([readLocal(651,false,false,true),readLocal(652,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))])]),callFunction(pure(f60),[mapValue(callFunction(pure(f124),[mapValue(mapValue(readLocal(649,false,false,false),v=>field(v,"transitions",null)),v=>temporaryRef(v,true)),readLocal(653,false,false,true)],false),v=>temporaryRef(v,true))],false)],(c,vs,k)=>more(()=>k(c,construct("SfSyntax",[null,null],vs,[0,1],false,"SynFail",true))))],(c,vs,k)=>more(()=>k(c,construct("Err",[null],vs,[0],false,"Result",true))))]],false)]))])]))]);
function f102(c,args,k){return enterFunction(b102,[648,649,650,651,652,653,654],null,c,args,k,false,false,[true,false,true,true,true,true,true],true);}

const b103 = sequence([defineLocal(669,false,readLocal(662,false,false,true),true),branch(values([readLocal(669,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(668,false,false,true)]),sequence([defineLocal(670,false,values([readLocal(669,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([readLocal(666,false,true,false),readLocal(667,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',false],pure(true),readLocal(668,false,false,true)],[['literal',true],pure(true),sequence([defineLocal(671,false,callFunction(pure(f125),[borrowPlace(663,[],true),readLocal(664,false,true,false),readLocal(665,false,false,true),readLocal(666,false,true,false)],false),true),branch(values([readLocal(671,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(668,false,false,true)]),sequence([defineLocal(672,false,values([readLocal(671,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f103),[readLocal(670,false,false,true),borrowPlace(663,[],true),readLocal(664,false,true,false),readLocal(672,false,true,false),values([readLocal(666,false,true,false),callFunction(pure(f73),[callFunction(pure(f74),[readLocal(664,false,true,false),readLocal(666,false,true,false)],false)],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(667,false,true,false),matchValue(callFunction(pure(f126),[borrowPlace(663,[],true),readLocal(664,false,true,false),readLocal(672,false,false,true),values([readLocal(666,false,true,false),callFunction(pure(f73),[callFunction(pure(f74),[readLocal(664,false,true,false),readLocal(666,false,true,false)],false)],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(667,false,true,false)],false),[[['ctor',"None",[],"Option"],pure(true),readLocal(668,false,false,true)],[['ctor',"Some",[['bind',673,false,true]],"Option"],pure(true),values([values([values([readLocal(666,false,true,false),callFunction(pure(f73),[callFunction(pure(f74),[readLocal(664,false,true,false),readLocal(666,false,false,true)],false)],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(673,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))]],false)])]))])]],false)]))]);
function f103(c,args,k){return enterFunction(b103,[662,663,664,665,666,667,668],null,c,args,k,false,false,[true,false,true,true,true,true,true],true);}

function d104(l674,l675,l676){l676=small(l676);for(;;){t2:{const t1=unref(l674);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return l675;break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l677=t1.fields[0];let l678=t1.fields[1];t4:{const t3=unref((small(l677.fields[1])==l676));requireDataOwner(t3);if(equal(false,t3)){const t5=l678;const t6=l675;const t7=l676;l674=t5;l675=t6;l676=t7;continue;break t4;}if(equal(true,t3)){{let l679=small(l677.fields[0]);if((l679==(0))){{return dcons("ScanMode",["current","pushed"],[big(small(l677.fields[2])),copyValue(l675.fields[1])],true,"ScanMode",true);}}else{{let l680=isub(l679,(1),0,9007199254740991,0n,Infinity);{let l681=l680;if((l681==(0))){{return dcons("ScanMode",["current","pushed"],[big(small(l677.fields[2])),dcons("Cons",[null,null],[big(small(l675.fields[0])),copyValue(l675.fields[1])],false,"List",true)],true,"ScanMode",true);}}else{{let l682=isub(l681,(1),0,9007199254740991,0n,Infinity);return d127(l675);}}}}}}break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f104(c,args,k){return direct(d104,g104,c,args,k,[1,0,0]);}

const b104 = matchValue(borrowPlace(674,[],true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(675,false,false,true)],[['ctor',"Cons",[['bind',677,true,false],['bind',678,true,false]],"List"],pure(true),matchValue(values([mapValue(readLocal(677,false,false,false),v=>field(v,"token",null)),readLocal(676,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),[[['literal',false],pure(true),tailSelfCall(pure(f104),[readLocal(678,false,false,false),readLocal(675,false,false,true),readLocal(676,false,false,true)])],[['literal',true],pure(true),sequence([defineLocal(679,false,mapValue(readLocal(677,false,false,false),v=>field(v,"kind",null)),true),branch(values([readLocal(679,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([mapValue(readLocal(677,false,false,false),v=>field(v,"target",null)),mapValue(readLocal(675,false,false,false),v=>field(v,"pushed",null))],(c,vs,k)=>more(()=>k(c,construct("ScanMode",["current","pushed"],vs,[0,1],true,"ScanMode",true))))]),sequence([defineLocal(680,false,values([readLocal(679,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(681,false,readLocal(680,false,false,true),true),branch(values([readLocal(681,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([mapValue(readLocal(677,false,false,false),v=>field(v,"target",null)),values([mapValue(readLocal(675,false,false,false),v=>field(v,"current",null)),mapValue(readLocal(675,false,false,false),v=>field(v,"pushed",null))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("ScanMode",["current","pushed"],vs,[0,1],true,"ScanMode",true))))]),sequence([defineLocal(682,false,values([readLocal(681,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),callFunction(pure(f127),[readLocal(675,false,false,true)],false)]))])]))])]],false)]],false);
function g104(c,args,k){return enterFunction(b104,[674,675,676],null,c,args,k,false,false,[false,true,true],true);}

function d105(l683,l684,l685){l684=small(l684);for(;;){t2:{const t1=unref(vecGet(l683,small(pureBuiltin("U64::of_nat",[big(l684)]))));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return l685;break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l686=t1.fields[0];return l686;break t2;}throw new Error('no arm of the match fits');}}}
function f105(c,args,k){return g105(c,args,k);}

const b105 = matchValue(builtin("Array::get",[readLocal(683,false,false,true),builtin("U64::of_nat",[readLocal(684,false,false,true)])]),[[['ctor',"None",[],"Option"],pure(true),readLocal(685,false,false,true)],[['ctor',"Some",[['bind',686,false,true]],"Option"],pure(true),readLocal(686,false,false,true)]],false);
function g105(c,args,k){return enterFunction(b105,[683,684,685],null,c,args,k,false,true,[true,true,true],false);}

const b106 = matchValue(borrowPlace(687,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Cons",[['bind',689,true,false],['bind',690,true,false]],"List"],pure(true),matchValue(values([mapValue(readLocal(689,false,false,false),v=>field(v,"token",null)),readLocal(688,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),[[['literal',true],pure(true),values([readLocal(689,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['literal',false],pure(true),tailSelfCall(pure(f106),[readLocal(690,false,false,false),readLocal(688,false,false,true)])]],false)]],false);
function f106(c,args,k){return enterFunction(b106,[687,688],null,c,args,k,false,false,[false,true],true);}

function d107(l691,l692){l692=small(l692);for(;;){t2:{const t1=unref(l691);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("ScanDynState",["kind","min","max"],[big((0)),big((0)),big((0))],true,"ScanDynState",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l693=t1.fields[0];let l694=t1.fields[1];{let l695=l692;if((l695==(0))){{return copyValue(l693);}}else{{let l696=isub(l695,(1),0,9007199254740991,0n,Infinity);const t3=l694;const t4=l696;l691=t3;l692=t4;continue;}}}break t2;}throw new Error('no arm of the match fits');}}}
function f107(c,args,k){return direct(d107,g107,c,args,k,[1,0]);}

const b107 = matchValue(borrowPlace(691,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([pure(0n),pure(0n),pure(0n)],(c,vs,k)=>more(()=>k(c,construct("ScanDynState",["kind","min","max"],vs,[0,1,2],true,"ScanDynState",true))))],[['ctor',"Cons",[['bind',693,true,false],['bind',694,true,false]],"List"],pure(true),sequence([defineLocal(695,false,readLocal(692,false,false,true),true),branch(values([readLocal(695,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(693,true,true,false)]),sequence([defineLocal(696,false,values([readLocal(695,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f107),[readLocal(694,false,false,false),readLocal(696,false,false,true)])]))])]],false);
function g107(c,args,k){return enterFunction(b107,[691,692],null,c,args,k,false,false,[false,true],true);}

const b108 = callFunction(pure(f38),[callFunction(pure(f128),[callFunction(pure(f67),[readLocal(701,false,true,false),readLocal(700,false,true,false)],false),borrowPlace(697,[],true),readLocal(698,false,false,true),callFunction(pure(f84),[mapValue(readLocal(697,false,false,false),v=>field(v,"dfa_first",null)),readLocal(699,false,true,false)],false),readLocal(700,false,true,false),readLocal(701,false,false,true),matchValue(callFunction(pure(f129),[borrowPlace(697,[],true),callFunction(pure(f84),[mapValue(readLocal(697,false,false,false),v=>field(v,"dfa_first",null)),readLocal(699,false,false,true)],false)],false),[[['literal',true],pure(true),values([readLocal(700,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],[['literal',false],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))]],false)],false)],false);
function f108(c,args,k){return enterFunction(b108,[697,698,699,700,701],null,c,args,k,false,false,[false,true,true,true,true],false);}

const b109 = matchValue(borrowPlace(706,[],true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(708,false,false,true)],[['ctor',"Cons",[['bind',709,true,false],['bind',710,true,false]],"List"],pure(true),sequence([defineLocal(711,false,callFunction(pure(f130),[mapValue(readLocal(705,false,false,false),v=>field(v,"max",null)),readLocal(703,false,true,false),mapValue(readLocal(704,false,false,false),v=>field(v,"unit",null)),readLocal(709,true,true,false),readLocal(707,false,true,false),pure(0n)],false),true),tailSelfCall(pure(f109),[borrowPlace(702,[],true),readLocal(703,false,true,false),readLocal(704,false,false,false),readLocal(705,false,false,false),readLocal(710,false,false,false),readLocal(707,false,true,false),callFunction(pure(f131),[readLocal(708,false,false,true),callFunction(pure(f132),[values([readLocal(711,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),borrowPlace(702,[],true),readLocal(703,false,true,false),readLocal(704,false,false,false),readLocal(709,true,true,false),readLocal(707,false,true,false),mapValue(readLocal(705,false,false,false),v=>field(v,"min",null)),readLocal(711,false,false,true)],false)],false)])])]],false);
function f109(c,args,k){return enterFunction(b109,[702,703,704,705,706,707,708],null,c,args,k,false,false,[false,true,false,false,false,true,true],true);}

function d110(l712,l713,l714){l713=small(l713);for(;;){t2:{const t1=unref(l712);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("Nil",[],[],false,"List",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l715=t1.fields[0];let l716=t1.fields[1];{let l717=l713;if((l717==(0))){{return dcons("Cons",[null,null],[l714,l716],false,"List",true);}}else{{let l718=isub(l717,(1),0,9007199254740991,0n,Infinity);return dcons("Cons",[null,null],[l715,d110(l716,l718,l714)],false,"List",true);}}}break t2;}throw new Error('no arm of the match fits');}}}
function f110(c,args,k){return direct(d110,g110,c,args,k,[0,0,0]);}

const b110 = matchValue(readLocal(712,false,false,true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',715,false,true],['bind',716,false,true]],"List"],pure(true),sequence([defineLocal(717,false,readLocal(713,false,false,true),true),branch(values([readLocal(717,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([readLocal(714,false,false,true),readLocal(716,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]),sequence([defineLocal(718,false,values([readLocal(717,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),values([readLocal(715,false,false,true),callFunction(pure(f110),[readLocal(716,false,false,true),readLocal(718,false,false,true),readLocal(714,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]))])]],true);
function g110(c,args,k){return enterFunction(b110,[712,713,714],null,c,args,k,false,false,[true,true,true],false);}

const b111 = matchValue(borrowPlace(722,[],true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(724,false,false,true)],[['ctor',"Cons",[['bind',725,true,false],['bind',726,true,false]],"List"],pure(true),tailSelfCall(pure(f111),[borrowPlace(719,[],true),readLocal(720,false,true,false),readLocal(721,false,false,false),readLocal(726,false,false,false),readLocal(723,false,true,false),callFunction(pure(f133),[borrowPlace(719,[],true),readLocal(720,false,true,false),readLocal(721,false,false,false),readLocal(725,true,true,false),mapValue(callFunction(pure(f108),[borrowPlace(719,[],true),readLocal(720,false,true,false),callFunction(pure(f67),[mapValue(readLocal(721,false,false,false),v=>field(v,"capture",null)),pure(1n)],false),readLocal(725,true,true,false),readLocal(723,false,true,false)],false),v=>temporaryRef(v,true)),readLocal(723,false,true,false),readLocal(724,false,false,true)],false)])]],false);
function f111(c,args,k){return enterFunction(b111,[719,720,721,722,723,724],null,c,args,k,false,false,[false,true,false,false,true,true],true);}

function d112(l727,l728,l729,l730){l727=small(l727);l729=small(l729);for(;;){{let l731=l727;if((l731==(0))){{return l730;}}else{{let l732=isub(l731,(1),0,9007199254740991,0n,Infinity);const t1=l732;const t2=copyValue(l728);const t3=iadd(l729,(3),0,9007199254740991,0n,Infinity);const t4=dcons("Cons",[null,null],[dcons("ScanModeChange",["kind","token","target"],[big(d84(copyValue(l728),l729)),big(d84(copyValue(l728),iadd(l729,(1),0,9007199254740991,0n,Infinity))),big(d84(copyValue(l728),iadd(l729,(2),0,9007199254740991,0n,Infinity)))],true,"ScanModeChange",true),l730],false,"List",true);l727=t1;l728=t2;l729=t3;l730=t4;continue;}}}}}
function f112(c,args,k){return direct(d112,g112,c,args,k,[0,0,0,0]);}

const b112 = sequence([defineLocal(731,false,readLocal(727,false,false,true),true),branch(values([readLocal(731,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(730,false,false,true)]),sequence([defineLocal(732,false,values([readLocal(731,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f112),[readLocal(732,false,false,true),readLocal(728,false,true,false),values([readLocal(729,false,true,false),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([values([callFunction(pure(f84),[readLocal(728,false,true,false),readLocal(729,false,true,false)],false),callFunction(pure(f84),[readLocal(728,false,true,false),values([readLocal(729,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),callFunction(pure(f84),[readLocal(728,false,true,false),values([readLocal(729,false,false,true),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false)],(c,vs,k)=>more(()=>k(c,construct("ScanModeChange",["kind","token","target"],vs,[0,1,2],true,"ScanModeChange",true)))),readLocal(730,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])]))]);
function g112(c,args,k){return enterFunction(b112,[727,728,729,730],null,c,args,k,false,false,[true,true,true,true],true);}

function d113(l733,l734){l733=small(l733);for(;;){return dcons("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],[big(small(l734.fields[0])),big(small(l734.fields[1])),big(iadd(small(l734.fields[2]),l733,0,9007199254740991,0n,Infinity)),big(small(l734.fields[3])),copyValue(l734.fields[4]),copyValue(l734.fields[5]),copyValue(l734.fields[6]),copyValue(l734.fields[7]),copyValue(l734.fields[8]),copyValue(l734.fields[9])],true,"ScanBuild",true);}}
function f113(c,args,k){return direct(d113,g113,c,args,k,[0,0]);}

const b113 = values([mapValue(readLocal(734,false,false,false),v=>field(v,"sp",null)),mapValue(readLocal(734,false,false,false),v=>field(v,"rp",null)),values([mapValue(readLocal(734,false,false,false),v=>field(v,"total",null)),readLocal(733,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),mapValue(readLocal(734,false,false,false),v=>field(v,"accepts",null)),mapValue(readLocal(734,false,false,false),v=>field(v,"built_dfa_first",null)),mapValue(readLocal(734,false,false,false),v=>field(v,"built_accept_first",null)),mapValue(readLocal(734,false,false,false),v=>field(v,"built_accept_token",null)),mapValue(readLocal(734,false,false,false),v=>field(v,"built_accept_kind",null)),mapValue(readLocal(734,false,false,false),v=>field(v,"built_accept_dfa",null)),mapValue(readLocal(734,false,false,false),v=>field(v,"built_rows",null))],(c,vs,k)=>more(()=>k(c,construct("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],vs,[0,1,2,3,4,5,6,7,8,9],true,"ScanBuild",true))));
function g113(c,args,k){return enterFunction(b113,[733,734],null,c,args,k,false,false,[true,true],false);}

function d114(l735,l736,l737,l738,l739){l735=small(l735);l736=small(l736);for(;;){{let l740=l735;if((l740==(0))){{return l739;}}else{{let l741=isub(l740,(1),0,9007199254740991,0n,Infinity);const t1=l741;const t2=l736;const t3=copyValue(l737);const t4=copyValue(l738);const t5=d134(l736,l736,copyValue(l738),(0),d135(d84(copyValue(l737),small(l739.fields[0])),copyValue(l737),dcons("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],[big(iadd(small(l739.fields[0]),(1),0,9007199254740991,0n,Infinity)),big(small(l739.fields[1])),big(small(l739.fields[2])),big(small(l739.fields[3])),copyValue(l739.fields[4]),dcons("Cons",[null,null],[big(small(l739.fields[3])),copyValue(l739.fields[5])],false,"List",true),copyValue(l739.fields[6]),copyValue(l739.fields[7]),copyValue(l739.fields[8]),copyValue(l739.fields[9])],true,"ScanBuild",true)));l735=t1;l736=t2;l737=t3;l738=t4;l739=t5;continue;}}}}}
function f114(c,args,k){return direct(d114,g114,c,args,k,[0,0,0,0,0]);}

const b114 = sequence([defineLocal(740,false,readLocal(735,false,false,true),true),branch(values([readLocal(740,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(739,false,false,true)]),sequence([defineLocal(741,false,values([readLocal(740,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f114),[readLocal(741,false,false,true),readLocal(736,false,true,false),readLocal(737,false,true,false),readLocal(738,false,true,false),callFunction(pure(f134),[readLocal(736,false,true,false),readLocal(736,false,true,false),readLocal(738,false,true,false),pure(0n),callFunction(pure(f135),[callFunction(pure(f84),[readLocal(737,false,true,false),mapValue(readLocal(739,false,false,false),v=>field(v,"sp",null))],false),readLocal(737,false,true,false),values([values([mapValue(readLocal(739,false,false,false),v=>field(v,"sp",null)),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),mapValue(readLocal(739,false,false,false),v=>field(v,"rp",null)),mapValue(readLocal(739,false,false,false),v=>field(v,"total",null)),mapValue(readLocal(739,false,false,false),v=>field(v,"accepts",null)),mapValue(readLocal(739,false,false,false),v=>field(v,"built_dfa_first",null)),values([mapValue(readLocal(739,false,false,false),v=>field(v,"accepts",null)),mapValue(readLocal(739,false,false,false),v=>field(v,"built_accept_first",null))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),mapValue(readLocal(739,false,false,false),v=>field(v,"built_accept_token",null)),mapValue(readLocal(739,false,false,false),v=>field(v,"built_accept_kind",null)),mapValue(readLocal(739,false,false,false),v=>field(v,"built_accept_dfa",null)),mapValue(readLocal(739,false,false,false),v=>field(v,"built_rows",null))],(c,vs,k)=>more(()=>k(c,construct("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],vs,[0,1,2,3,4,5,6,7,8,9],true,"ScanBuild",true))))],false)],false)])]))]);
function g114(c,args,k){return enterFunction(b114,[735,736,737,738,739],null,c,args,k,false,false,[true,true,true,true,true],true);}

const b115 = sequence([defineLocal(744,false,callFunction(pure(f105),[readLocal(742,false,true,false),values([readLocal(743,false,true,false),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false),true),defineLocal(745,false,values([values([readLocal(743,false,true,false),pure(4n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(744,false,true,false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),true),defineLocal(746,false,callFunction(pure(f105),[readLocal(742,false,true,false),readLocal(745,false,true,false),pure(0n)],false),true),defineLocal(749,false,sequence([defineLocal(747,false,readLocal(746,false,true,false),true),branch(values([readLocal(747,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([readLocal(745,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))]),sequence([defineLocal(748,false,values([readLocal(747,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),values([readLocal(745,false,true,false),pure(11n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))]))]),true),values([values([callFunction(pure(f105),[readLocal(742,false,true,false),readLocal(743,false,true,false),pure(0n)],false),callFunction(pure(f105),[readLocal(742,false,true,false),values([readLocal(743,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false),callFunction(pure(f105),[readLocal(742,false,true,false),values([readLocal(743,false,true,false),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false),callFunction(pure(f5),[callFunction(pure(f136),[readLocal(744,false,false,true),readLocal(742,false,true,false),values([readLocal(743,false,false,true),pure(4n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],false)],false),readLocal(746,false,false,true),builtin("Array::of_list",[callFunction(pure(f137),[pure(10n),readLocal(742,false,true,false),values([readLocal(745,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false)]),callFunction(pure(f105),[readLocal(742,false,true,false),readLocal(749,false,true,false),pure(0n)],false),callFunction(pure(f105),[readLocal(742,false,true,false),values([readLocal(749,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false),callFunction(pure(f105),[readLocal(742,false,false,true),values([readLocal(749,false,true,false),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false)],(c,vs,k)=>more(()=>k(c,construct("ScanDyn",["token","op","state","unit","ranged","bounds","prefix","suffix","capture"],vs,[0,1,2,3,4,5,6,7,8],true,"ScanDyn",true)))),values([readLocal(749,false,false,true),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))]);
function f115(c,args,k){return enterFunction(b115,[742,743],null,c,args,k,false,false,[true,true],false);}

function d116(l750,l751,l752,l753){l753=small(l753);for(;;){{let l754=d138(small(pureBuiltin("Nat::of_u64",[big(copyValue(l750).items.length)])),copyValue(l750),l753,(0),small(pureBuiltin("Nat::of_u64",[big(l750.items.length)])));if((l754==(0))){{return (0);}}else{{let l755=isub(l754,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref((l753<=d84(l751,l755)));requireDataOwner(t1);if(equal(true,t1)){return iadd(d84(l752,l755),(1),0,9007199254740991,0n,Infinity);break t2;}if(equal(false,t1)){return (0);break t2;}throw new Error('no arm of the match fits');}}}}}}
function f116(c,args,k){return direct((...a)=>big(d116(...a)),g116,c,args,k,[0,0,0,0]);}

const b116 = sequence([defineLocal(754,false,callFunction(pure(f138),[builtin("Nat::of_u64",[builtin("Array::len",[readLocal(750,false,true,false)])]),readLocal(750,false,true,false),readLocal(753,false,true,false),pure(0n),builtin("Nat::of_u64",[builtin("Array::len",[readLocal(750,false,false,true)])])],false),true),branch(values([readLocal(754,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([pure(0n)]),sequence([defineLocal(755,false,values([readLocal(754,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([readLocal(753,false,false,true),callFunction(pure(f84),[readLocal(751,false,false,true),readLocal(755,false,true,false)],false)],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),[[['literal',true],pure(true),values([callFunction(pure(f84),[readLocal(752,false,false,true),readLocal(755,false,false,true)],false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],[['literal',false],pure(true),pure(0n)]],false)]))]);
function g116(c,args,k){return enterFunction(b116,[750,751,752,753],null,c,args,k,false,false,[true,true,true,true],false);}

function d117(l756){l756=small(l756);for(;;){t2:{const t1=unref((((48)<=l756)&&(l756<=(57))));requireDataOwner(t1);if(equal(true,t1)){return dcons("Some",[null],[big(d67(l756,(48)))],false,"Option",true);break t2;}if(equal(false,t1)){return dcons("None",[],[],false,"Option",true);break t2;}throw new Error('no arm of the match fits');}}}
function f117(c,args,k){return direct(d117,g117,c,args,k,[0]);}

const b117 = matchValue(branch(values([pure(48n),readLocal(756,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),values([readLocal(756,false,true,false),pure(57n)],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),pure(false)),[[['literal',true],pure(true),values([callFunction(pure(f67),[readLocal(756,false,false,true),pure(48n)],false)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['literal',false],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))]],false);
function g117(c,args,k){return enterFunction(b117,[756],null,c,args,k,false,false,[true],false);}

function d118(l757,l758){l757=small(l757);l758=small(l758);for(;;){if((l757<l758)){return l758;}else{return l757;}}}
function f118(c,args,k){return direct((...a)=>big(d118(...a)),g118,c,args,k,[0,0]);}

const b118 = branch(values([readLocal(757,false,true,false),readLocal(758,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),readLocal(758,false,false,true),readLocal(757,false,false,true));
function g118(c,args,k){return enterFunction(b118,[757,758],null,c,args,k,false,false,[true,true],false);}

function d119(l759){for(;;){t2:{const t1=unref(l759);requireDataOwner(t1);if(t1.tag==="SvOne"&&t1.owner==="SynV"){let l760=t1.fields[0];let l761=small(t1.fields[1]);let l762=small(t1.fields[2]);return l762;break t2;}if(t1.tag==="SvOpt"&&t1.owner==="SynV"){let l763=t1.fields[0];let l764=small(t1.fields[1]);let l765=small(t1.fields[2]);return l765;break t2;}if(t1.tag==="SvList"&&t1.owner==="SynV"){let l766=t1.fields[0];let l767=small(t1.fields[1]);let l768=small(t1.fields[2]);return l768;break t2;}throw new Error('no arm of the match fits');}}}
function f119(c,args,k){return direct((...a)=>big(d119(...a)),g119,c,args,k,[1]);}

const b119 = matchValue(borrowPlace(759,[],true),[[['ctor',"SvOne",[['bind',760,true,false],['bind',761,true,false],['bind',762,true,false]],"SynV"],pure(true),readLocal(762,true,true,false)],[['ctor',"SvOpt",[['bind',763,true,false],['bind',764,true,false],['bind',765,true,false]],"SynV"],pure(true),readLocal(765,true,true,false)],[['ctor',"SvList",[['bind',766,true,false],['bind',767,true,false],['bind',768,true,false]],"SynV"],pure(true),readLocal(768,true,true,false)]],false);
function g119(c,args,k){return enterFunction(b119,[759],null,c,args,k,false,false,[false],false);}

function d120(l769){for(;;){t2:{const t1=unref(l769);requireDataOwner(t1);if(t1.tag==="SvOne"&&t1.owner==="SynV"){let l770=t1.fields[0];let l771=small(t1.fields[1]);let l772=small(t1.fields[2]);return true;break t2;}if(t1.tag==="SvOpt"&&t1.owner==="SynV"){let l773=t1.fields[0];let l774=small(t1.fields[1]);let l775=small(t1.fields[2]);t4:{const t3=unref(l773);requireDataOwner(t3);if(t3.tag==="None"&&t3.owner==="Option"){return false;break t4;}if(t3.tag==="Some"&&t3.owner==="Option"){let l776=t3.fields[0];return true;break t4;}throw new Error('no arm of the match fits');}break t2;}if(t1.tag==="SvList"&&t1.owner==="SynV"){let l777=t1.fields[0];let l778=small(t1.fields[1]);let l779=small(t1.fields[2]);t6:{const t5=unref(l777);requireDataOwner(t5);if(t5.tag==="Nil"&&t5.owner==="List"){return false;break t6;}if(t5.tag==="Cons"&&t5.owner==="List"){let l780=t5.fields[0];let l781=t5.fields[1];return true;break t6;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f120(c,args,k){return direct(d120,g120,c,args,k,[1]);}

const b120 = matchValue(borrowPlace(769,[],true),[[['ctor',"SvOne",[['bind',770,true,false],['bind',771,true,false],['bind',772,true,false]],"SynV"],pure(true),pure(true)],[['ctor',"SvOpt",[['bind',773,true,false],['bind',774,true,false],['bind',775,true,false]],"SynV"],pure(true),matchValue(borrowPlace(773,[],true),[[['ctor',"None",[],"Option"],pure(true),pure(false)],[['ctor',"Some",[['bind',776,true,false]],"Option"],pure(true),pure(true)]],false)],[['ctor',"SvList",[['bind',777,true,false],['bind',778,true,false],['bind',779,true,false]],"SynV"],pure(true),matchValue(borrowPlace(777,[],true),[[['ctor',"Nil",[],"List"],pure(true),pure(false)],[['ctor',"Cons",[['bind',780,true,false],['bind',781,true,false]],"List"],pure(true),pure(true)]],false)]],false);
function g120(c,args,k){return enterFunction(b120,[769],null,c,args,k,false,false,[false],false);}

function d121(l782){for(;;){t2:{const t1=unref(l782);requireDataOwner(t1);if(t1.tag==="SvOne"&&t1.owner==="SynV"){let l783=t1.fields[0];let l784=small(t1.fields[1]);let l785=small(t1.fields[2]);return l784;break t2;}if(t1.tag==="SvOpt"&&t1.owner==="SynV"){let l786=t1.fields[0];let l787=small(t1.fields[1]);let l788=small(t1.fields[2]);return l787;break t2;}if(t1.tag==="SvList"&&t1.owner==="SynV"){let l789=t1.fields[0];let l790=small(t1.fields[1]);let l791=small(t1.fields[2]);return l790;break t2;}throw new Error('no arm of the match fits');}}}
function f121(c,args,k){return direct((...a)=>big(d121(...a)),g121,c,args,k,[1]);}

const b121 = matchValue(borrowPlace(782,[],true),[[['ctor',"SvOne",[['bind',783,true,false],['bind',784,true,false],['bind',785,true,false]],"SynV"],pure(true),readLocal(784,true,true,false)],[['ctor',"SvOpt",[['bind',786,true,false],['bind',787,true,false],['bind',788,true,false]],"SynV"],pure(true),readLocal(787,true,true,false)],[['ctor',"SvList",[['bind',789,true,false],['bind',790,true,false],['bind',791,true,false]],"SynV"],pure(true),readLocal(790,true,true,false)]],false);
function g121(c,args,k){return enterFunction(b121,[782],null,c,args,k,false,false,[false],false);}

function d122(l792,l793,l794){for(;;){t2:{const t1=unref(l793);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("Nil",[],[],false,"List",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l795=t1.fields[0];let l796=t1.fields[1];t4:{const t3=unref(l794);requireDataOwner(t3);if(t3.tag==="Nil"&&t3.owner==="List"){return dcons("Nil",[],[],false,"List",true);break t4;}if(t3.tag==="Cons"&&t3.owner==="List"){let l797=t3.fields[0];let l798=t3.fields[1];if(l797){return dcons("Cons",[null,null],[d34(l792,l795),d122(l792,l796,l798)],false,"List",true);}else{const t5=l792;const t6=l796;const t7=l798;l792=t5;l793=t6;l794=t7;continue;}break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f122(c,args,k){return direct(d122,g122,c,args,k,[0,1,1]);}

const b122 = matchValue(borrowPlace(793,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',795,true,false],['bind',796,true,false]],"List"],pure(true),matchValue(borrowPlace(794,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',797,true,false],['bind',798,true,false]],"List"],pure(true),branch(readLocal(797,true,true,false),values([callFunction(pure(f34),[readLocal(792,false,true,false),readLocal(795,false,false,false)],false),callFunction(pure(f122),[readLocal(792,false,true,false),readLocal(796,false,false,false),readLocal(798,false,false,false)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),tailSelfCall(pure(f122),[readLocal(792,false,true,false),readLocal(796,false,false,false),readLocal(798,false,false,false)]))]],false)]],false);
function g122(c,args,k){return enterFunction(b122,[792,793,794],null,c,args,k,false,false,[true,false,false],true);}

function d123(l799,l800,l801){l800=small(l800);l801=small(l801);for(;;){t2:{const t1=unref(l799);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("None",[],[],false,"Option",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l802=t1.fields[0];let l803=t1.fields[1];if(((small(l802.fields[0])==l800)&&(small(l802.fields[1])==l801))){return dcons("Some",[null],[copyValue(l802)],false,"Option",true);}else{const t3=l803;const t4=l800;const t5=l801;l799=t3;l800=t4;l801=t5;continue;}break t2;}throw new Error('no arm of the match fits');}}}
function f123(c,args,k){return direct(d123,g123,c,args,k,[1,0,0]);}

const b123 = matchValue(borrowPlace(799,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Cons",[['bind',802,true,false],['bind',803,true,false]],"List"],pure(true),branch(branch(values([mapValue(readLocal(802,false,false,false),v=>field(v,"state",null)),readLocal(800,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),values([mapValue(readLocal(802,false,false,false),v=>field(v,"terminal",null)),readLocal(801,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),pure(false)),values([readLocal(802,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true)))),tailSelfCall(pure(f123),[readLocal(803,false,false,false),readLocal(800,false,false,true),readLocal(801,false,false,true)]))]],false);
function g123(c,args,k){return enterFunction(b123,[799,800,801],null,c,args,k,false,false,[false,true,true],true);}

function d124(l804,l805){l805=small(l805);for(;;){t2:{const t1=unref(l804);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("Nil",[],[],false,"List",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l806=t1.fields[0];let l807=t1.fields[1];if((small(l806.fields[0])==l805)){return dcons("Cons",[null,null],[big(small(l806.fields[1])),d124(l807,l805)],false,"List",true);}else{const t3=l807;const t4=l805;l804=t3;l805=t4;continue;}break t2;}throw new Error('no arm of the match fits');}}}
function f124(c,args,k){return direct(d124,g124,c,args,k,[1,0]);}

const b124 = matchValue(borrowPlace(804,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))],[['ctor',"Cons",[['bind',806,true,false],['bind',807,true,false]],"List"],pure(true),branch(values([mapValue(readLocal(806,false,false,false),v=>field(v,"state",null)),readLocal(805,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),values([mapValue(readLocal(806,false,false,false),v=>field(v,"terminal",null)),callFunction(pure(f124),[readLocal(807,false,false,false),readLocal(805,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),tailSelfCall(pure(f124),[readLocal(807,false,false,false),readLocal(805,false,false,true)]))]],false);
function g124(c,args,k){return enterFunction(b124,[804,805],null,c,args,k,false,false,[false,true],true);}

const b125 = sequence([defineLocal(812,false,callFunction(pure(f139),[borrowPlace(808,[],true),readLocal(809,false,true,false),readLocal(811,false,true,false),callFunction(pure(f74),[readLocal(809,false,false,true),readLocal(811,false,false,true)],false)],false),true),branch(values([readLocal(812,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([pure(0n)]),sequence([defineLocal(813,false,values([readLocal(812,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),callFunction(pure(f84),[mapValue(readLocal(808,false,false,false),v=>field(v,"rows",null)),values([values([readLocal(810,false,false,true),mapValue(readLocal(808,false,false,false),v=>field(v,"classes",null))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),readLocal(813,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false)]))]);
function f125(c,args,k){return enterFunction(b125,[808,809,810,811],null,c,args,k,false,false,[false,true,true,true],false);}

const b126 = callFunction(pure(f140),[callFunction(pure(f67),[callFunction(pure(f84),[mapValue(readLocal(814,false,false,false),v=>field(v,"accept_first",null)),values([readLocal(816,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),callFunction(pure(f84),[mapValue(readLocal(814,false,false,false),v=>field(v,"accept_first",null)),readLocal(816,false,true,false)],false)],false),borrowPlace(814,[],true),readLocal(815,false,false,true),callFunction(pure(f84),[mapValue(readLocal(814,false,false,false),v=>field(v,"accept_first",null)),readLocal(816,false,false,true)],false),readLocal(817,false,false,true),readLocal(818,false,false,true)],false);
function f126(c,args,k){return enterFunction(b126,[814,815,816,817,818],null,c,args,k,false,false,[false,true,true,true,true],false);}

function d127(l819){for(;;){t2:{const t1=unref(copyValue(l819.fields[1]));requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return l819;break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l820=small(t1.fields[0]);let l821=t1.fields[1];return dcons("ScanMode",["current","pushed"],[big(l820),l821],true,"ScanMode",true);break t2;}throw new Error('no arm of the match fits');}}}
function f127(c,args,k){return direct(d127,g127,c,args,k,[0]);}

const b127 = matchValue(mapValue(readLocal(819,false,false,false),v=>field(v,"pushed",null)),[[['ctor',"Nil",[],"List"],pure(true),readLocal(819,false,false,true)],[['ctor',"Cons",[['bind',820,false,true],['bind',821,false,true]],"List"],pure(true),values([readLocal(820,false,false,true),readLocal(821,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("ScanMode",["current","pushed"],vs,[0,1],true,"ScanMode",true))))]],false);
function g127(c,args,k){return enterFunction(b127,[819],null,c,args,k,false,false,[true],false);}

const b128 = sequence([defineLocal(829,false,readLocal(822,false,false,true),true),branch(values([readLocal(829,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(828,false,false,true)]),sequence([defineLocal(830,false,values([readLocal(829,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([readLocal(826,false,true,false),readLocal(827,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',false],pure(true),readLocal(828,false,false,true)],[['literal',true],pure(true),sequence([defineLocal(831,false,callFunction(pure(f125),[borrowPlace(823,[],true),readLocal(824,false,true,false),readLocal(825,false,false,true),readLocal(826,false,true,false)],false),true),branch(values([readLocal(831,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(828,false,false,true)]),sequence([defineLocal(832,false,values([readLocal(831,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f128),[readLocal(830,false,false,true),borrowPlace(823,[],true),readLocal(824,false,true,false),readLocal(832,false,true,false),values([readLocal(826,false,true,false),callFunction(pure(f73),[callFunction(pure(f74),[readLocal(824,false,true,false),readLocal(826,false,true,false)],false)],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(827,false,false,true),matchValue(callFunction(pure(f129),[borrowPlace(823,[],true),readLocal(832,false,false,true)],false),[[['literal',true],pure(true),values([values([readLocal(826,false,true,false),callFunction(pure(f73),[callFunction(pure(f74),[readLocal(824,false,true,false),readLocal(826,false,false,true)],false)],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(828,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))],[['literal',false],pure(true),readLocal(828,false,false,true)]],false)])]))])]],false)]))]);
function f128(c,args,k){return enterFunction(b128,[822,823,824,825,826,827,828],null,c,args,k,false,false,[true,false,true,true,true,true,true],true);}

const b129 = values([callFunction(pure(f84),[mapValue(readLocal(833,false,false,false),v=>field(v,"accept_first",null)),readLocal(834,false,true,false)],false),callFunction(pure(f84),[mapValue(readLocal(833,false,false,false),v=>field(v,"accept_first",null)),values([readLocal(834,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1])));
function f129(c,args,k){return enterFunction(b129,[833,834],null,c,args,k,false,false,[false,true],false);}

function d130(l835,l836,l837,l838,l839,l840){l835=small(l835);l838=small(l838);l839=small(l839);l840=small(l840);for(;;){{let l841=l835;if((l841==(0))){{return l840;}}else{{let l842=isub(l841,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref(((iadd(l838,small(pureBuiltin("Nat::of_u64",[big(textBytes(l837).length)])),0,9007199254740991,0n,Infinity)<=l839)&&d141(l836,l837,l838)));requireDataOwner(t1);if(equal(false,t1)){return l840;break t2;}if(equal(true,t1)){const t3=l842;const t4=l836;const t5=l837;const t6=iadd(l838,small(pureBuiltin("Nat::of_u64",[big(textBytes(l837).length)])),0,9007199254740991,0n,Infinity);const t7=l839;const t8=iadd(l840,(1),0,9007199254740991,0n,Infinity);l835=t3;l836=t4;l837=t5;l838=t6;l839=t7;l840=t8;continue;break t2;}throw new Error('no arm of the match fits');}}}}}}
function f130(c,args,k){return direct((...a)=>big(d130(...a)),g130,c,args,k,[0,0,0,0,0,0]);}

const b130 = sequence([defineLocal(841,false,readLocal(835,false,false,true),true),branch(values([readLocal(841,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(840,false,false,true)]),sequence([defineLocal(842,false,values([readLocal(841,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(branch(values([values([readLocal(838,false,true,false),builtin("Nat::of_u64",[values([readLocal(837,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(839,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),callFunction(pure(f141),[readLocal(836,false,true,false),readLocal(837,false,true,false),readLocal(838,false,true,false)],false),pure(false)),[[['literal',false],pure(true),readLocal(840,false,false,true)],[['literal',true],pure(true),tailSelfCall(pure(f130),[readLocal(842,false,false,true),readLocal(836,false,false,true),readLocal(837,false,true,false),values([readLocal(838,false,false,true),builtin("Nat::of_u64",[values([readLocal(837,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(839,false,false,true),values([readLocal(840,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))])]],false)]))]);
function g130(c,args,k){return enterFunction(b130,[835,836,837,838,839,840],null,c,args,k,false,false,[true,true,true,true,true,true],true);}

function d131(l843,l844){for(;;){t2:{const t1=unref(copyValue(l843));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return l844;break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l845=small(t1.fields[0]);t4:{const t3=unref(copyValue(l844));requireDataOwner(t3);if(t3.tag==="None"&&t3.owner==="Option"){return l843;break t4;}if(t3.tag==="Some"&&t3.owner==="Option"){let l846=small(t3.fields[0]);t6:{const t5=unref((l845<l846));requireDataOwner(t5);if(equal(true,t5)){return l844;break t6;}if(equal(false,t5)){return l843;break t6;}throw new Error('no arm of the match fits');}break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f131(c,args,k){return direct(d131,g131,c,args,k,[0,0]);}

const b131 = matchValue(readLocal(843,false,true,false),[[['ctor',"None",[],"Option"],pure(true),readLocal(844,false,false,true)],[['ctor',"Some",[['bind',845,false,true]],"Option"],pure(true),matchValue(readLocal(844,false,true,false),[[['ctor',"None",[],"Option"],pure(true),readLocal(843,false,false,true)],[['ctor',"Some",[['bind',846,false,true]],"Option"],pure(true),matchValue(values([readLocal(845,false,false,true),readLocal(846,false,false,true)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),readLocal(844,false,false,true)],[['literal',false],pure(true),readLocal(843,false,false,true)]],false)]],true)]],true);
function g131(c,args,k){return enterFunction(b131,[843,844],null,c,args,k,false,false,[true,true],false);}

const b132 = sequence([defineLocal(855,false,readLocal(847,false,false,true),true),branch(values([readLocal(855,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))]),sequence([defineLocal(856,false,values([readLocal(855,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([readLocal(854,false,true,false),readLocal(853,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['literal',false],pure(true),matchValue(callFunction(pure(f142),[borrowPlace(848,[],true),readLocal(849,false,true,false),mapValue(readLocal(850,false,false,false),v=>field(v,"suffix",null)),values([readLocal(851,false,true,false),values([readLocal(854,false,true,false),builtin("Nat::of_u64",[values([mapValue(readLocal(850,false,false,false),v=>field(v,"unit",null))],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(852,false,true,false)],false),[[['literal',true],pure(true),values([readLocal(854,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['literal',false],pure(true),sequence([defineLocal(857,false,readLocal(854,false,false,true),true),branch(values([readLocal(857,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))]),sequence([defineLocal(858,false,values([readLocal(857,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f132),[readLocal(856,false,false,true),borrowPlace(848,[],true),readLocal(849,false,false,true),readLocal(850,false,false,false),readLocal(851,false,false,true),readLocal(852,false,false,true),readLocal(853,false,false,true),readLocal(858,false,false,true)])]))])]],false)]],false)]))]);
function f132(c,args,k){return enterFunction(b132,[847,848,849,850,851,852,853,854],null,c,args,k,false,false,[true,false,true,false,true,true,true,true],true);}

const b133 = matchValue(borrowPlace(863,[],true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(865,false,false,true)],[['ctor',"Cons",[['bind',866,true,false],['bind',867,true,false]],"List"],pure(true),tailSelfCall(pure(f133),[borrowPlace(859,[],true),readLocal(860,false,true,false),readLocal(861,false,false,false),readLocal(862,false,true,false),readLocal(867,false,false,false),readLocal(864,false,true,false),matchValue(branch(callFunction(pure(f143),[readLocal(865,false,true,false),readLocal(862,false,true,false),readLocal(866,true,true,false)],false),callFunction(pure(f142),[borrowPlace(859,[],true),readLocal(860,false,true,false),mapValue(readLocal(861,false,false,false),v=>field(v,"suffix",null)),readLocal(866,true,true,false),readLocal(864,false,true,false)],false),pure(false)),[[['literal',true],pure(true),values([values([readLocal(862,false,true,false),readLocal(866,true,true,false)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['literal',false],pure(true),readLocal(865,false,false,true)]],false)])]],false);
function f133(c,args,k){return enterFunction(b133,[859,860,861,862,863,864,865],null,c,args,k,false,false,[false,true,false,true,false,true,true],true);}

function d134(l868,l869,l870,l871,l872){l868=small(l868);l869=small(l869);l871=small(l871);for(;;){{let l873=l868;if((l873==(0))){{return l872;}}else{{let l874=isub(l873,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref((l871<l869));requireDataOwner(t1);if(equal(false,t1)){return l872;break t2;}if(equal(true,t1)){const t16=l874;const t17=l869;const t18=copyValue(l870);const t19=iadd(l871,d84(copyValue(l870),small(l872.fields[1])),0,9007199254740991,0n,Infinity);const t7=small(l872.fields[0]);const t8=iadd(small(l872.fields[1]),(2),0,9007199254740991,0n,Infinity);const t9=small(l872.fields[2]);const t10=small(l872.fields[3]);const t11=copyValue(l872.fields[4]);const t12=copyValue(l872.fields[5]);const t13=copyValue(l872.fields[6]);const t14=copyValue(l872.fields[7]);const t15=copyValue(l872.fields[8]);const t6=d84(copyValue(l870),small(l872.fields[1]));let t3;{let l875=d84(copyValue(l870),iadd(small(l872.fields[1]),(1),0,9007199254740991,0n,Infinity));let t5;if((l875==(0))){t5=(0);}else{let t4;{let l876=isub(l875,(1),0,9007199254740991,0n,Infinity);t4=iadd(small(l872.fields[2]),iadd(l876,(1),0,9007199254740991,0n,Infinity),0,9007199254740991,0n,Infinity);}t5=t4;}t3=t5;}const t20=t16;const t21=t17;const t22=t18;const t23=t19;const t24=dcons("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],[big(t7),big(t8),big(t9),big(t10),t11,t12,t13,t14,t15,d144(t6,t3,copyValue(l872.fields[9]))],true,"ScanBuild",true);l868=t20;l869=t21;l870=t22;l871=t23;l872=t24;continue;break t2;}throw new Error('no arm of the match fits');}}}}}}
function f134(c,args,k){return direct(d134,g134,c,args,k,[0,0,0,0,0]);}

const b134 = sequence([defineLocal(873,false,readLocal(868,false,false,true),true),branch(values([readLocal(873,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(872,false,false,true)]),sequence([defineLocal(874,false,values([readLocal(873,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([readLocal(871,false,true,false),readLocal(869,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',false],pure(true),readLocal(872,false,false,true)],[['literal',true],pure(true),tailSelfCall(pure(f134),[readLocal(874,false,false,true),readLocal(869,false,false,true),readLocal(870,false,true,false),values([readLocal(871,false,false,true),callFunction(pure(f84),[readLocal(870,false,true,false),mapValue(readLocal(872,false,false,false),v=>field(v,"rp",null))],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([mapValue(readLocal(872,false,false,false),v=>field(v,"sp",null)),values([mapValue(readLocal(872,false,false,false),v=>field(v,"rp",null)),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),mapValue(readLocal(872,false,false,false),v=>field(v,"total",null)),mapValue(readLocal(872,false,false,false),v=>field(v,"accepts",null)),mapValue(readLocal(872,false,false,false),v=>field(v,"built_dfa_first",null)),mapValue(readLocal(872,false,false,false),v=>field(v,"built_accept_first",null)),mapValue(readLocal(872,false,false,false),v=>field(v,"built_accept_token",null)),mapValue(readLocal(872,false,false,false),v=>field(v,"built_accept_kind",null)),mapValue(readLocal(872,false,false,false),v=>field(v,"built_accept_dfa",null)),callFunction(pure(f144),[callFunction(pure(f84),[readLocal(870,false,true,false),mapValue(readLocal(872,false,false,false),v=>field(v,"rp",null))],false),sequence([defineLocal(875,false,callFunction(pure(f84),[readLocal(870,false,true,false),values([mapValue(readLocal(872,false,false,false),v=>field(v,"rp",null)),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),true),branch(values([readLocal(875,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([pure(0n)]),sequence([defineLocal(876,false,values([readLocal(875,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),values([mapValue(readLocal(872,false,false,false),v=>field(v,"total",null)),values([readLocal(876,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))]))]),mapValue(readLocal(872,false,false,false),v=>field(v,"built_rows",null))],false)],(c,vs,k)=>more(()=>k(c,construct("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],vs,[0,1,2,3,4,5,6,7,8,9],true,"ScanBuild",true))))])]],false)]))]);
function g134(c,args,k){return enterFunction(b134,[868,869,870,871,872],null,c,args,k,false,false,[true,true,true,true,true],true);}

function d135(l877,l878,l879){l877=small(l877);for(;;){{let l880=l877;if((l880==(0))){{return l879;}}else{{let l881=isub(l880,(1),0,9007199254740991,0n,Infinity);const t1=l881;const t2=copyValue(l878);const t3=dcons("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],[big(iadd(small(l879.fields[0]),(3),0,9007199254740991,0n,Infinity)),big(small(l879.fields[1])),big(small(l879.fields[2])),big(iadd(small(l879.fields[3]),(1),0,9007199254740991,0n,Infinity)),copyValue(l879.fields[4]),copyValue(l879.fields[5]),dcons("Cons",[null,null],[big(d84(copyValue(l878),small(l879.fields[0]))),copyValue(l879.fields[6])],false,"List",true),dcons("Cons",[null,null],[big(d84(copyValue(l878),iadd(small(l879.fields[0]),(1),0,9007199254740991,0n,Infinity))),copyValue(l879.fields[7])],false,"List",true),dcons("Cons",[null,null],[big(d84(copyValue(l878),iadd(small(l879.fields[0]),(2),0,9007199254740991,0n,Infinity))),copyValue(l879.fields[8])],false,"List",true),copyValue(l879.fields[9])],true,"ScanBuild",true);l877=t1;l878=t2;l879=t3;continue;}}}}}
function f135(c,args,k){return direct(d135,g135,c,args,k,[0,0,0]);}

const b135 = sequence([defineLocal(880,false,readLocal(877,false,false,true),true),branch(values([readLocal(880,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(879,false,false,true)]),sequence([defineLocal(881,false,values([readLocal(880,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f135),[readLocal(881,false,false,true),readLocal(878,false,true,false),values([values([mapValue(readLocal(879,false,false,false),v=>field(v,"sp",null)),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),mapValue(readLocal(879,false,false,false),v=>field(v,"rp",null)),mapValue(readLocal(879,false,false,false),v=>field(v,"total",null)),values([mapValue(readLocal(879,false,false,false),v=>field(v,"accepts",null)),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),mapValue(readLocal(879,false,false,false),v=>field(v,"built_dfa_first",null)),mapValue(readLocal(879,false,false,false),v=>field(v,"built_accept_first",null)),values([callFunction(pure(f84),[readLocal(878,false,true,false),mapValue(readLocal(879,false,false,false),v=>field(v,"sp",null))],false),mapValue(readLocal(879,false,false,false),v=>field(v,"built_accept_token",null))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),values([callFunction(pure(f84),[readLocal(878,false,true,false),values([mapValue(readLocal(879,false,false,false),v=>field(v,"sp",null)),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),mapValue(readLocal(879,false,false,false),v=>field(v,"built_accept_kind",null))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),values([callFunction(pure(f84),[readLocal(878,false,true,false),values([mapValue(readLocal(879,false,false,false),v=>field(v,"sp",null)),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),mapValue(readLocal(879,false,false,false),v=>field(v,"built_accept_dfa",null))],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true)))),mapValue(readLocal(879,false,false,false),v=>field(v,"built_rows",null))],(c,vs,k)=>more(()=>k(c,construct("ScanBuild",["sp","rp","total","accepts","built_dfa_first","built_accept_first","built_accept_token","built_accept_kind","built_accept_dfa","built_rows"],vs,[0,1,2,3,4,5,6,7,8,9],true,"ScanBuild",true))))])]))]);
function g135(c,args,k){return enterFunction(b135,[877,878,879],null,c,args,k,false,false,[true,true,true],true);}

function d136(l882,l883,l884,l885){l882=small(l882);l884=small(l884);for(;;){{let l886=l882;if((l886==(0))){{return d38(l885);}}else{{let l887=isub(l886,(1),0,9007199254740991,0n,Infinity);const t1=l887;const t2=copyValue(l883);const t3=iadd(l884,(1),0,9007199254740991,0n,Infinity);const t4=dcons("Cons",[null,null],[d145(small(d105(copyValue(l883),l884,big((0))))),l885],false,"List",true);l882=t1;l883=t2;l884=t3;l885=t4;continue;}}}}}
function f136(c,args,k){return direct(d136,g136,c,args,k,[0,0,0,0]);}

const b136 = sequence([defineLocal(886,false,readLocal(882,false,false,true),true),branch(values([readLocal(886,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([callFunction(pure(f38),[readLocal(885,false,false,true)],false)]),sequence([defineLocal(887,false,values([readLocal(886,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f136),[readLocal(887,false,false,true),readLocal(883,false,true,false),values([readLocal(884,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),values([callFunction(pure(f145),[callFunction(pure(f105),[readLocal(883,false,true,false),readLocal(884,false,false,true),pure(0n)],false)],false),readLocal(885,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])]))]);
function g136(c,args,k){return enterFunction(b136,[882,883,884,885],null,c,args,k,false,false,[true,true,true,true],true);}

function d137(l888,l889,l890){l888=small(l888);l890=small(l890);for(;;){{let l891=l888;if((l891==(0))){{return dcons("Nil",[],[],false,"List",true);}}else{{let l892=isub(l891,(1),0,9007199254740991,0n,Infinity);return dcons("Cons",[null,null],[big(small(d105(copyValue(l889),l890,big((0))))),d137(l892,l889,iadd(l890,(1),0,9007199254740991,0n,Infinity))],false,"List",true);}}}}}
function f137(c,args,k){return direct(d137,g137,c,args,k,[0,0,0]);}

const b137 = sequence([defineLocal(891,false,readLocal(888,false,false,true),true),branch(values([readLocal(891,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("Nil",[],vs,[],false,"List",true))))]),sequence([defineLocal(892,false,values([readLocal(891,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),values([callFunction(pure(f105),[readLocal(889,false,true,false),readLocal(890,false,true,false),pure(0n)],false),callFunction(pure(f137),[readLocal(892,false,false,true),readLocal(889,false,false,true),values([readLocal(890,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))]))]);
function g137(c,args,k){return enterFunction(b137,[888,889,890],null,c,args,k,false,false,[true,true,true],false);}

function d138(l893,l894,l895,l896,l897){l893=small(l893);l895=small(l895);l896=small(l896);l897=small(l897);for(;;){{let l898=l893;if((l898==(0))){{return l896;}}else{{let l899=isub(l898,(1),0,9007199254740991,0n,Infinity);t2:{const t1=unref((l896<l897));requireDataOwner(t1);if(equal(false,t1)){return l896;break t2;}if(equal(true,t1)){t4:{const t3=unref((d84(copyValue(l894),d146(iadd(l896,l897,0,9007199254740991,0n,Infinity),(2)))<=l895));requireDataOwner(t3);if(equal(true,t3)){const t5=l899;const t6=l894;const t7=l895;const t8=iadd(d146(iadd(l896,l897,0,9007199254740991,0n,Infinity),(2)),(1),0,9007199254740991,0n,Infinity);const t9=l897;l893=t5;l894=t6;l895=t7;l896=t8;l897=t9;continue;break t4;}if(equal(false,t3)){const t10=l899;const t11=l894;const t12=l895;const t13=l896;const t14=d146(iadd(l896,l897,0,9007199254740991,0n,Infinity),(2));l893=t10;l894=t11;l895=t12;l896=t13;l897=t14;continue;break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}}}}
function f138(c,args,k){return direct((...a)=>big(d138(...a)),g138,c,args,k,[0,0,0,0,0]);}

const b138 = sequence([defineLocal(898,false,readLocal(893,false,false,true),true),branch(values([readLocal(898,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(896,false,false,true)]),sequence([defineLocal(899,false,values([readLocal(898,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([readLocal(896,false,true,false),readLocal(897,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',false],pure(true),readLocal(896,false,false,true)],[['literal',true],pure(true),matchValue(values([callFunction(pure(f84),[readLocal(894,false,true,false),callFunction(pure(f146),[values([readLocal(896,false,true,false),readLocal(897,false,true,false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(2n)],false)],false),readLocal(895,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),[[['literal',true],pure(true),tailSelfCall(pure(f138),[readLocal(899,false,false,true),readLocal(894,false,false,true),readLocal(895,false,false,true),values([callFunction(pure(f146),[values([readLocal(896,false,false,true),readLocal(897,false,true,false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(2n)],false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(897,false,false,true)])],[['literal',false],pure(true),tailSelfCall(pure(f138),[readLocal(899,false,false,true),readLocal(894,false,false,true),readLocal(895,false,false,true),readLocal(896,false,true,false),callFunction(pure(f146),[values([readLocal(896,false,true,false),readLocal(897,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(2n)],false)])]],false)]],false)]))]);
function g138(c,args,k){return enterFunction(b138,[893,894,895,896,897],null,c,args,k,false,false,[true,true,true,true,true],true);}

const b139 = matchValue(values([readLocal(903,false,true,false),pure(128n)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),callFunction(pure(f84),[mapValue(readLocal(900,false,false,false),v=>field(v,"ascii",null)),readLocal(903,false,false,true)],false)],[['literal',false],pure(true),callFunction(pure(f116),[mapValue(readLocal(900,false,false,false),v=>field(v,"run_start",null)),mapValue(readLocal(900,false,false,false),v=>field(v,"run_end",null)),mapValue(readLocal(900,false,false,false),v=>field(v,"run_class",null)),callFunction(pure(f147),[readLocal(901,false,false,true),readLocal(902,false,false,true),readLocal(903,false,false,true)],false)],false)]],false);
function f139(c,args,k){return enterFunction(b139,[900,901,902,903],null,c,args,k,false,false,[false,true,true,true],false);}

const b140 = sequence([defineLocal(910,false,readLocal(904,false,false,true),true),branch(values([readLocal(910,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))]),sequence([defineLocal(911,false,values([readLocal(910,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f148),[borrowPlace(905,[],true),readLocal(906,false,true,false),readLocal(907,false,true,false),readLocal(908,false,true,false),readLocal(909,false,true,false)],false),[[['literal',true],pure(true),values([callFunction(pure(f84),[mapValue(readLocal(905,false,false,false),v=>field(v,"accept_token",null)),readLocal(907,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['literal',false],pure(true),tailSelfCall(pure(f140),[readLocal(911,false,false,true),borrowPlace(905,[],true),readLocal(906,false,false,true),values([readLocal(907,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(908,false,false,true),readLocal(909,false,false,true)])]],false)]))]);
function f140(c,args,k){return enterFunction(b140,[904,905,906,907,908,909],null,c,args,k,false,false,[true,false,true,true,true,true],true);}

function d141(l912,l913,l914){l914=small(l914);for(;;){t2:{const t1=unref(pureBuiltin("Text::slice",[l912,big(small(pureBuiltin("U64::of_nat",[big(l914)]))),big(small(pureBuiltin("U64::of_nat",[big(iadd(l914,small(pureBuiltin("Nat::of_u64",[big(textBytes(l913).length)])),0,9007199254740991,0n,Infinity))])))]));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return false;break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l915=t1.fields[0];return equal(l915,l913);break t2;}throw new Error('no arm of the match fits');}}}
function f141(c,args,k){return direct(d141,g141,c,args,k,[0,0,0]);}

const b141 = matchValue(builtin("Text::slice",[readLocal(912,false,false,true),builtin("U64::of_nat",[readLocal(914,false,true,false)]),builtin("U64::of_nat",[values([readLocal(914,false,false,true),builtin("Nat::of_u64",[values([readLocal(913,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))])]),[[['ctor',"None",[],"Option"],pure(true),pure(false)],[['ctor',"Some",[['bind',915,false,true]],"Option"],pure(true),values([readLocal(915,false,false,true),readLocal(913,false,false,true)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1]))))]],false);
function g141(c,args,k){return enterFunction(b141,[912,913,914],null,c,args,k,false,false,[true,true,true],false);}

const b142 = callFunction(pure(f149),[mapValue(callFunction(pure(f108),[borrowPlace(916,[],true),readLocal(917,false,false,true),readLocal(918,false,false,true),readLocal(919,false,false,true),readLocal(920,false,true,false)],false),v=>temporaryRef(v,true)),readLocal(920,false,false,true)],false);
function f142(c,args,k){return enterFunction(b142,[916,917,918,919,920],null,c,args,k,false,false,[false,true,true,true,true],false);}

function d143(l921,l922,l923){l922=small(l922);l923=small(l923);for(;;){t2:{const t1=unref(l921);requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return true;break t2;}if(t1.tag==="Some"&&t1.owner==="Option"&&t1.fields[0].tag==="Pair"&&t1.fields[0].owner==="Pair"){let l924=small(t1.fields[0].fields[0]);let l925=small(t1.fields[0].fields[1]);return (d67(l925,l924)<d67(l923,l922));break t2;}throw new Error('no arm of the match fits');}}}
function f143(c,args,k){return direct(d143,g143,c,args,k,[0,0,0]);}

const b143 = matchValue(readLocal(921,false,false,true),[[['ctor',"None",[],"Option"],pure(true),pure(true)],[['ctor',"Some",[['ctor',"Pair",[['bind',924,false,true],['bind',925,false,true]],"Pair"]],"Option"],pure(true),values([callFunction(pure(f67),[readLocal(925,false,false,true),readLocal(924,false,false,true)],false),callFunction(pure(f67),[readLocal(923,false,false,true),readLocal(922,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1])))]],true);
function g143(c,args,k){return enterFunction(b143,[921,922,923],null,c,args,k,false,false,[true,true,true],false);}

function d144(l926,l927,l928){l926=small(l926);l927=small(l927);for(;;){{let l929=l926;if((l929==(0))){{return l928;}}else{{let l930=isub(l929,(1),0,9007199254740991,0n,Infinity);const t1=l930;const t2=l927;const t3=dcons("Cons",[null,null],[big(l927),l928],false,"List",true);l926=t1;l927=t2;l928=t3;continue;}}}}}
function f144(c,args,k){return direct(d144,g144,c,args,k,[0,0,0]);}

const b144 = sequence([defineLocal(929,false,readLocal(926,false,false,true),true),branch(values([readLocal(929,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(928,false,false,true)]),sequence([defineLocal(930,false,values([readLocal(929,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f144),[readLocal(930,false,false,true),readLocal(927,false,true,false),values([readLocal(927,false,true,false),readLocal(928,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Cons",[null,null],vs,[0,1],false,"List",true))))])]))]);
function g144(c,args,k){return enterFunction(b144,[926,927,928],null,c,args,k,false,false,[true,true,true],true);}

function d145(l931){l931=small(l931);for(;;){return d150(l931);}}
function f145(c,args,k){return direct(d145,g145,c,args,k,[0]);}

const b145 = callFunction(pure(f150),[readLocal(931,false,false,true)],false);
function g145(c,args,k){return enterFunction(b145,[931],null,c,args,k,false,false,[true],false);}

function d146(l932,l933){l932=small(l932);l933=small(l933);for(;;){if((l933==(0))){return (0);}else{return idivide("div",l932,l933,0,9007199254740991,0n,Infinity);}}}
function f146(c,args,k){return direct((...a)=>big(d146(...a)),g146,c,args,k,[0,0]);}

const b146 = branch(values([readLocal(933,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),pure(0n),values([readLocal(932,false,false,true),readLocal(933,false,false,true)],(c,vs,k)=>more(()=>k(c,divide("div",vs,0n,Infinity)))));
function g146(c,args,k){return enterFunction(b146,[932,933],null,c,args,k,false,false,[true,true],false);}

function d147(l934,l935,l936){l935=small(l935);l936=small(l936);for(;;){t2:{const t1=unref(d151(l934,l935));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return l936;break t2;}if(t1.tag==="Some"&&t1.owner==="Option"&&t1.fields[0].tag==="Pair"&&t1.fields[0].owner==="Pair"){let l937=small(t1.fields[0].fields[0]);return l937;break t2;}throw new Error('no arm of the match fits');}}}
function f147(c,args,k){return direct((...a)=>big(d147(...a)),g147,c,args,k,[0,0,0]);}

const b147 = matchValue(callFunction(pure(f151),[readLocal(934,false,false,true),readLocal(935,false,false,true)],false),[[['ctor',"None",[],"Option"],pure(true),readLocal(936,false,false,true)],[['ctor',"Some",[['ctor',"Pair",[['bind',937,false,true],['wild']],"Pair"]],"Option"],pure(true),readLocal(937,false,false,true)]],false);
function g147(c,args,k){return enterFunction(b147,[934,935,936],null,c,args,k,false,false,[true,true,true],false);}

const b148 = sequence([defineLocal(943,false,callFunction(pure(f84),[mapValue(readLocal(938,false,false,false),v=>field(v,"accept_kind",null)),readLocal(940,false,true,false)],false),true),branch(values([readLocal(943,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([callFunction(pure(f152),[borrowPlace(938,[],true),readLocal(939,false,false,true),callFunction(pure(f84),[mapValue(readLocal(938,false,false,false),v=>field(v,"accept_token",null)),readLocal(940,false,false,true)],false),readLocal(941,false,false,true)],false)]),sequence([defineLocal(944,false,values([readLocal(943,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(945,false,readLocal(944,false,false,true),true),branch(values([readLocal(945,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([branch(callFunction(pure(f153),[borrowPlace(938,[],true),readLocal(939,false,true,false),callFunction(pure(f84),[mapValue(readLocal(938,false,false,false),v=>field(v,"accept_dfa",null)),readLocal(940,false,true,false)],false),readLocal(941,false,true,false),readLocal(942,false,false,true)],false),callFunction(pure(f152),[borrowPlace(938,[],true),readLocal(939,false,false,true),callFunction(pure(f84),[mapValue(readLocal(938,false,false,false),v=>field(v,"accept_token",null)),readLocal(940,false,false,true)],false),readLocal(941,false,false,true)],false),pure(false))]),sequence([defineLocal(946,false,values([readLocal(945,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),branch(callFunction(pure(f43),[callFunction(pure(f153),[borrowPlace(938,[],true),readLocal(939,false,true,false),callFunction(pure(f84),[mapValue(readLocal(938,false,false,false),v=>field(v,"accept_dfa",null)),readLocal(940,false,true,false)],false),readLocal(941,false,true,false),readLocal(942,false,false,true)],false)],false),callFunction(pure(f152),[borrowPlace(938,[],true),readLocal(939,false,false,true),callFunction(pure(f84),[mapValue(readLocal(938,false,false,false),v=>field(v,"accept_token",null)),readLocal(940,false,false,true)],false),readLocal(941,false,false,true)],false),pure(false))]))])]))]);
function f148(c,args,k){return enterFunction(b148,[938,939,940,941,942],null,c,args,k,false,false,[false,true,true,true,true],false);}

function d149(l947,l948){l948=small(l948);for(;;){t2:{const t1=unref(l947);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return false;break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l949=small(t1.fields[0]);let l950=t1.fields[1];t4:{const t3=unref((l949==l948));requireDataOwner(t3);if(equal(true,t3)){return true;break t4;}if(equal(false,t3)){const t5=l950;const t6=l948;l947=t5;l948=t6;continue;break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f149(c,args,k){return direct(d149,g149,c,args,k,[1,0]);}

const b149 = matchValue(borrowPlace(947,[],true),[[['ctor',"Nil",[],"List"],pure(true),pure(false)],[['ctor',"Cons",[['bind',949,true,false],['bind',950,true,false]],"List"],pure(true),matchValue(values([readLocal(949,true,true,false),readLocal(948,false,true,false)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),[[['literal',true],pure(true),pure(true)],[['literal',false],pure(true),tailSelfCall(pure(f149),[readLocal(950,false,false,false),readLocal(948,false,false,true)])]],false)]],false);
function g149(c,args,k){return enterFunction(b149,[947,948],null,c,args,k,false,false,[false,true],true);}

function d150(l951){l951=small(l951);for(;;){t2:{const t1=unref(d154(l951));requireDataOwner(t1);if(t1.tag==="Some"&&t1.owner==="Option"){let l952=t1.fields[0];return l952;break t2;}if(t1.tag==="None"&&t1.owner==="Option"){return "";break t2;}throw new Error('no arm of the match fits');}}}
function f150(c,args,k){return direct(d150,g150,c,args,k,[0]);}

const b150 = matchValue(callFunction(pure(f154),[readLocal(951,false,false,true)],false),[[['ctor',"Some",[['bind',952,false,true]],"Option"],pure(true),readLocal(952,false,false,true)],[['ctor',"None",[],"Option"],pure(true),pure("")]],false);
function g150(c,args,k){return enterFunction(b150,[951],null,c,args,k,false,false,[true],false);}

function d151(l953,l954){l954=small(l954);for(;;){t2:{const t1=unref(d37(l953,l954));requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return dcons("None",[],[],false,"Option",true);break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l955=small(t1.fields[0]);return d155(l953,l954,l955);break t2;}throw new Error('no arm of the match fits');}}}
function f151(c,args,k){return direct(d151,g151,c,args,k,[0,0]);}

const b151 = matchValue(callFunction(pure(f37),[readLocal(953,false,true,false),readLocal(954,false,true,false)],false),[[['ctor',"None",[],"Option"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['ctor',"Some",[['bind',955,false,true]],"Option"],pure(true),callFunction(pure(f155),[readLocal(953,false,false,true),readLocal(954,false,false,true),readLocal(955,false,false,true)],false)]],false);
function g151(c,args,k){return enterFunction(b151,[953,954],null,c,args,k,false,false,[true,true],false);}

const b152 = matchValue(callFunction(pure(f106),[mapValue(mapValue(readLocal(956,false,false,false),v=>field(v,"dyns",null)),v=>temporaryRef(v,true)),readLocal(958,false,false,true)],false),[[['ctor',"None",[],"Option"],pure(true),pure(true)],[['ctor',"Some",[['bind',960,false,true]],"Option"],pure(true),callFunction(pure(f156),[borrowPlace(956,[],true),readLocal(957,false,false,true),readLocal(960,false,false,true),mapValue(readLocal(956,false,false,false),v=>field(v,"start",null)),readLocal(959,false,false,true)],false)]],false);
function f152(c,args,k){return enterFunction(b152,[956,957,958,959],null,c,args,k,false,false,[false,true,true,true],false);}

const b153 = callFunction(pure(f157),[callFunction(pure(f67),[readLocal(965,false,true,false),readLocal(964,false,true,false)],false),borrowPlace(961,[],true),readLocal(962,false,false,true),callFunction(pure(f84),[mapValue(readLocal(961,false,false,false),v=>field(v,"dfa_first",null)),readLocal(963,false,false,true)],false),readLocal(964,false,false,true),readLocal(965,false,false,true)],false);
function f153(c,args,k){return enterFunction(b153,[961,962,963,964,965],null,c,args,k,false,false,[false,true,true,true,true],false);}

function d154(l966){l966=small(l966);for(;;){if((l966>(1114111))){return dcons("None",[],[],false,"Option",true);}else{return pureBuiltin("Text::of_code_point",[big(small(pureBuiltin("U32::of_u64",[big(small(pureBuiltin("U64::of_nat",[big(l966)])))])))]);}}}
function f154(c,args,k){return direct(d154,g154,c,args,k,[0]);}

const b154 = branch(values([readLocal(966,false,true,false),pure(1114111n)],(c,vs,k)=>more(()=>k(c,vs[0] > vs[1]))),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true)))),builtin("Text::of_code_point",[builtin("U32::of_u64",[builtin("U64::of_nat",[readLocal(966,false,false,true)])])]));
function g154(c,args,k){return enterFunction(b154,[966],null,c,args,k,false,false,[true],false);}

function d155(l967,l968,l969){l968=small(l968);l969=small(l969);for(;;){t2:{const t1=unref((l969<(128)));requireDataOwner(t1);if(equal(true,t1)){return dcons("Some",[null],[dcons("Pair",["fst","snd"],[big(l969),big((1))],true,"Pair",true)],false,"Option",true);break t2;}if(equal(false,t1)){return d158(l967,l968,l969);break t2;}throw new Error('no arm of the match fits');}}}
function f155(c,args,k){return direct(d155,g155,c,args,k,[0,0,0]);}

const b155 = matchValue(values([readLocal(969,false,true,false),pure(128n)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),values([values([readLocal(969,false,false,true),pure(1n)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['literal',false],pure(true),callFunction(pure(f158),[readLocal(967,false,false,true),readLocal(968,false,false,true),readLocal(969,false,false,true)],false)]],false);
function g155(c,args,k){return enterFunction(b155,[967,968,969],null,c,args,k,false,false,[true,true,true],false);}

const b156 = sequence([defineLocal(975,false,callFunction(pure(f107),[mapValue(mapValue(readLocal(970,false,false,false),v=>field(v,"dyn_states",null)),v=>temporaryRef(v,true)),mapValue(readLocal(972,false,false,false),v=>field(v,"state",null))],false),true),defineLocal(976,false,callFunction(pure(f108),[borrowPlace(970,[],true),readLocal(971,false,true,false),mapValue(readLocal(972,false,false,false),v=>field(v,"prefix",null)),readLocal(973,false,false,true),readLocal(974,false,true,false)],false),true),sequence([defineLocal(977,false,mapValue(readLocal(972,false,false,false),v=>field(v,"op",null)),true),branch(values([readLocal(977,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([callFunction(pure(f159),[callFunction(pure(f109),[borrowPlace(970,[],true),readLocal(971,false,false,true),borrowPlace(972,[],false),borrowPlace(975,[],false),borrowPlace(976,[],false),readLocal(974,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],false)],false)]),sequence([defineLocal(978,false,values([readLocal(977,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(979,false,readLocal(978,false,false,true),true),branch(values([readLocal(979,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([matchValue(callFunction(pure(f160),[mapValue(mapValue(readLocal(970,false,false,false),v=>field(v,"held",null)),v=>temporaryRef(v,true)),mapValue(readLocal(972,false,false,false),v=>field(v,"state",null))],false),[[['ctor',"ScanHeldCount",[['bind',980,false,true]],"ScanHeld"],pure(true),matchValue(callFunction(pure(f109),[borrowPlace(970,[],true),readLocal(971,false,false,true),borrowPlace(972,[],false),borrowPlace(975,[],false),borrowPlace(976,[],false),readLocal(974,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],false),[[['ctor',"None",[],"Option"],pure(true),pure(false)],[['ctor',"Some",[['bind',981,false,true]],"Option"],pure(true),callFunction(pure(f161),[readLocal(972,false,false,true),readLocal(981,false,false,true),readLocal(980,false,false,true)],false)]],false)],[['ctor',"ScanHeldText",[['bind',982,false,true]],"ScanHeld"],pure(true),pure(false)],[['ctor',"ScanHeldNone",[],"ScanHeld"],pure(true),pure(false)]],false)]),sequence([defineLocal(983,false,values([readLocal(979,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(984,false,readLocal(983,false,false,true),true),branch(values([readLocal(984,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([callFunction(pure(f159),[callFunction(pure(f111),[borrowPlace(970,[],true),readLocal(971,false,false,true),borrowPlace(972,[],false),borrowPlace(976,[],false),readLocal(974,false,false,true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],false)],false)]),sequence([defineLocal(985,false,values([readLocal(984,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f160),[mapValue(mapValue(readLocal(970,false,false,false),v=>field(v,"held",null)),v=>temporaryRef(v,true)),mapValue(readLocal(972,false,false,false),v=>field(v,"state",null))],false),[[['ctor',"ScanHeldText",[['bind',986,false,true]],"ScanHeld"],pure(true),callFunction(pure(f162),[borrowPlace(970,[],true),readLocal(971,false,false,true),borrowPlace(972,[],false),readLocal(986,false,false,true),borrowPlace(976,[],false),readLocal(974,false,false,true)],false)],[['ctor',"ScanHeldCount",[['bind',987,false,true]],"ScanHeld"],pure(true),pure(false)],[['ctor',"ScanHeldNone",[],"ScanHeld"],pure(true),pure(false)]],false)]))])]))])]))])]);
function f156(c,args,k){return enterFunction(b156,[970,971,972,973,974],null,c,args,k,false,false,[false,true,true,true,true],false);}

const b157 = sequence([defineLocal(994,false,readLocal(988,false,false,true),true),branch(values([readLocal(994,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([pure(false)]),sequence([defineLocal(995,false,values([readLocal(994,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([readLocal(992,false,true,false),readLocal(993,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',false],pure(true),pure(false)],[['literal',true],pure(true),sequence([defineLocal(996,false,callFunction(pure(f125),[borrowPlace(989,[],true),readLocal(990,false,true,false),readLocal(991,false,false,true),readLocal(992,false,true,false)],false),true),branch(values([readLocal(996,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([pure(false)]),sequence([defineLocal(997,false,values([readLocal(996,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([callFunction(pure(f84),[mapValue(readLocal(989,false,false,false),v=>field(v,"accept_first",null)),readLocal(997,false,true,false)],false),callFunction(pure(f84),[mapValue(readLocal(989,false,false,false),v=>field(v,"accept_first",null)),values([readLocal(997,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),pure(true)],[['literal',false],pure(true),tailSelfCall(pure(f157),[readLocal(995,false,false,true),borrowPlace(989,[],true),readLocal(990,false,true,false),readLocal(997,false,false,true),values([readLocal(992,false,true,false),callFunction(pure(f73),[callFunction(pure(f74),[readLocal(990,false,true,false),readLocal(992,false,false,true)],false)],false)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(993,false,false,true)])]],false)]))])]],false)]))]);
function f157(c,args,k){return enterFunction(b157,[988,989,990,991,992,993],null,c,args,k,false,false,[true,false,true,true,true,true],true);}

function d158(l998,l999,l1000){l999=small(l999);l1000=small(l1000);for(;;){t2:{const t1=unref((l1000<(192)));requireDataOwner(t1);if(equal(true,t1)){return dcons("None",[],[],false,"Option",true);break t2;}if(equal(false,t1)){return d163(l998,l999,l1000);break t2;}throw new Error('no arm of the match fits');}}}
function f158(c,args,k){return direct(d158,g158,c,args,k,[0,0,0]);}

const b158 = matchValue(values([readLocal(1000,false,true,false),pure(192n)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))],[['literal',false],pure(true),callFunction(pure(f163),[readLocal(998,false,false,true),readLocal(999,false,false,true),readLocal(1000,false,false,true)],false)]],false);
function g158(c,args,k){return enterFunction(b158,[998,999,1000],null,c,args,k,false,false,[true,true,true],false);}

function d159(l1001){for(;;){t2:{const t1=unref(l1001);requireDataOwner(t1);if(t1.tag==="None"&&t1.owner==="Option"){return false;break t2;}if(t1.tag==="Some"&&t1.owner==="Option"){let l1002=t1.fields[0];return true;break t2;}throw new Error('no arm of the match fits');}}}
function f159(c,args,k){return g159(c,args,k);}

const b159 = matchValue(readLocal(1001,false,false,true),[[['ctor',"None",[],"Option"],pure(true),pure(false)],[['ctor',"Some",[['bind',1002,false,true]],"Option"],pure(true),pure(true)]],true);
function g159(c,args,k){return enterFunction(b159,[1001],null,c,args,k,false,false,[true],false);}

function d160(l1003,l1004){l1004=small(l1004);for(;;){t2:{const t1=unref(l1003);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return dcons("ScanHeldNone",[],[],false,"ScanHeld",true);break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l1005=t1.fields[0];let l1006=t1.fields[1];{let l1007=l1004;if((l1007==(0))){{return copyValue(l1005);}}else{{let l1008=isub(l1007,(1),0,9007199254740991,0n,Infinity);const t3=l1006;const t4=l1008;l1003=t3;l1004=t4;continue;}}}break t2;}throw new Error('no arm of the match fits');}}}
function f160(c,args,k){return direct(d160,g160,c,args,k,[1,0]);}

const b160 = matchValue(borrowPlace(1003,[],true),[[['ctor',"Nil",[],"List"],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("ScanHeldNone",[],vs,[],false,"ScanHeld",true))))],[['ctor',"Cons",[['bind',1005,true,false],['bind',1006,true,false]],"List"],pure(true),sequence([defineLocal(1007,false,readLocal(1004,false,false,true),true),branch(values([readLocal(1007,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([readLocal(1005,true,true,false)]),sequence([defineLocal(1008,false,values([readLocal(1007,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),tailSelfCall(pure(f160),[readLocal(1006,false,false,false),readLocal(1008,false,false,true)])]))])]],false);
function g160(c,args,k){return enterFunction(b160,[1003,1004],null,c,args,k,false,false,[false,true],true);}

const b161 = sequence([defineLocal(1012,false,mapValue(readLocal(1009,false,false,false),v=>field(v,"ranged",null)),true),branch(values([readLocal(1012,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([readLocal(1010,false,false,true),readLocal(1011,false,false,true)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1]))))]),sequence([defineLocal(1013,false,values([readLocal(1012,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(callFunction(pure(f164),[mapValue(readLocal(1009,false,false,false),v=>field(v,"bounds",null)),pure(0n),readLocal(1011,false,true,false)],false),[[['ctor',"None",[],"Option"],pure(true),pure(false)],[['ctor',"Some",[['bind',1014,false,true]],"Option"],pure(true),matchValue(callFunction(pure(f164),[mapValue(readLocal(1009,false,false,false),v=>field(v,"bounds",null)),pure(5n),readLocal(1011,false,false,true)],false),[[['ctor',"None",[],"Option"],pure(true),pure(false)],[['ctor',"Some",[['bind',1015,false,true]],"Option"],pure(true),branch(values([readLocal(1014,false,false,true),readLocal(1010,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),values([readLocal(1010,false,false,true),readLocal(1015,false,false,true)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),pure(false))]],false)]],false)]))]);
function f161(c,args,k){return enterFunction(b161,[1009,1010,1011],null,c,args,k,false,false,[true,true,true],false);}

const b162 = matchValue(borrowPlace(1020,[],true),[[['ctor',"Nil",[],"List"],pure(true),pure(false)],[['ctor',"Cons",[['bind',1022,true,false],['bind',1023,true,false]],"List"],pure(true),matchValue(branch(branch(values([values([readLocal(1022,true,true,false),builtin("Nat::of_u64",[values([readLocal(1019,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(1021,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),callFunction(pure(f141),[readLocal(1017,false,true,false),readLocal(1019,false,true,false),readLocal(1022,true,true,false)],false),pure(false)),callFunction(pure(f142),[borrowPlace(1016,[],true),readLocal(1017,false,true,false),mapValue(readLocal(1018,false,false,false),v=>field(v,"suffix",null)),values([readLocal(1022,true,true,false),builtin("Nat::of_u64",[values([readLocal(1019,false,true,false)],(c,vs,k)=>more(()=>k(c,BigInt(textBytes(vs[0]).length))))])],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(1021,false,true,false)],false),pure(false)),[[['literal',true],pure(true),pure(true)],[['literal',false],pure(true),tailSelfCall(pure(f162),[borrowPlace(1016,[],true),readLocal(1017,false,false,true),readLocal(1018,false,false,false),readLocal(1019,false,false,true),readLocal(1023,false,false,false),readLocal(1021,false,false,true)])]],false)]],false);
function f162(c,args,k){return enterFunction(b162,[1016,1017,1018,1019,1020,1021],null,c,args,k,false,false,[false,true,false,true,false,true],true);}

function d163(l1024,l1025,l1026){l1025=small(l1025);l1026=small(l1026);for(;;){t2:{const t1=unref((l1026<(224)));requireDataOwner(t1);if(equal(true,t1)){return d165(d67(l1026,(192)),(2),d67(d74(l1024,iadd(l1025,(1),0,9007199254740991,0n,Infinity)),(128)),(0),(0));break t2;}if(equal(false,t1)){return d166(l1024,l1025,l1026);break t2;}throw new Error('no arm of the match fits');}}}
function f163(c,args,k){return direct(d163,g163,c,args,k,[0,0,0]);}

const b163 = matchValue(values([readLocal(1026,false,true,false),pure(224n)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),callFunction(pure(f165),[callFunction(pure(f67),[readLocal(1026,false,false,true),pure(192n)],false),pure(2n),callFunction(pure(f67),[callFunction(pure(f74),[readLocal(1024,false,false,true),values([readLocal(1025,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),pure(128n)],false),pure(0n),pure(0n)],false)],[['literal',false],pure(true),callFunction(pure(f166),[readLocal(1024,false,false,true),readLocal(1025,false,false,true),readLocal(1026,false,false,true)],false)]],false);
function g163(c,args,k){return enterFunction(b163,[1024,1025,1026],null,c,args,k,false,false,[true,true,true],false);}

function d164(l1027,l1028,l1029){l1028=small(l1028);l1029=small(l1029);for(;;){{let t1;{let l1030=small(d105(copyValue(l1027),l1028,big((0))));let t3;if((l1030==(0))){t3=small(d105(copyValue(l1027),iadd(l1028,(1),0,9007199254740991,0n,Infinity),big((0))));}else{let t2;{let l1031=isub(l1030,(1),0,9007199254740991,0n,Infinity);t2=l1029;}t3=t2;}t1=t3;}let l1032=t1;let t4;{let l1033=small(d105(copyValue(l1027),iadd(l1028,(3),0,9007199254740991,0n,Infinity),big((0))));let t6;if((l1033==(0))){t6=small(d105(copyValue(l1027),iadd(l1028,(4),0,9007199254740991,0n,Infinity),big((0))));}else{let t5;{let l1034=isub(l1033,(1),0,9007199254740991,0n,Infinity);t5=l1029;}t6=t5;}t4=t6;}let l1035=t4;{let l1036=small(d105(l1027,iadd(l1028,(2),0,9007199254740991,0n,Infinity),big((0))));if((l1036==(0))){{return dcons("Some",[null],[big(l1032)],false,"Option",true);}}else{{let l1037=isub(l1036,(1),0,9007199254740991,0n,Infinity);{let l1038=l1037;if((l1038==(0))){{return dcons("Some",[null],[big(iadd(l1032,l1035,0,9007199254740991,0n,Infinity))],false,"Option",true);}}else{{let l1039=isub(l1038,(1),0,9007199254740991,0n,Infinity);t8:{const t7=unref((l1035<=l1032));requireDataOwner(t7);if(equal(true,t7)){return dcons("Some",[null],[big(d67(l1032,l1035))],false,"Option",true);break t8;}if(equal(false,t7)){return dcons("None",[],[],false,"Option",true);break t8;}throw new Error('no arm of the match fits');}}}}}}}}}}
function f164(c,args,k){return direct(d164,g164,c,args,k,[0,0,0]);}

const b164 = sequence([defineLocal(1032,false,sequence([defineLocal(1030,false,callFunction(pure(f105),[readLocal(1027,false,true,false),readLocal(1028,false,true,false),pure(0n)],false),true),branch(values([readLocal(1030,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([callFunction(pure(f105),[readLocal(1027,false,true,false),values([readLocal(1028,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false)]),sequence([defineLocal(1031,false,values([readLocal(1030,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),readLocal(1029,false,true,false)]))]),true),defineLocal(1035,false,sequence([defineLocal(1033,false,callFunction(pure(f105),[readLocal(1027,false,true,false),values([readLocal(1028,false,true,false),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false),true),branch(values([readLocal(1033,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([callFunction(pure(f105),[readLocal(1027,false,true,false),values([readLocal(1028,false,true,false),pure(4n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false)]),sequence([defineLocal(1034,false,values([readLocal(1033,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),readLocal(1029,false,false,true)]))]),true),sequence([defineLocal(1036,false,callFunction(pure(f105),[readLocal(1027,false,false,true),values([readLocal(1028,false,false,true),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),pure(0n)],false),true),branch(values([readLocal(1036,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([readLocal(1032,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))]),sequence([defineLocal(1037,false,values([readLocal(1036,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),sequence([defineLocal(1038,false,readLocal(1037,false,false,true),true),branch(values([readLocal(1038,false,true,false),pure(0n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),sequence([values([values([readLocal(1032,false,false,true),readLocal(1035,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))]),sequence([defineLocal(1039,false,values([readLocal(1038,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]-vs[1],0n,Infinity))),true),matchValue(values([readLocal(1035,false,true,false),readLocal(1032,false,true,false)],(c,vs,k)=>more(()=>k(c,vs[0] <= vs[1]))),[[['literal',true],pure(true),values([callFunction(pure(f67),[readLocal(1032,false,false,true),readLocal(1035,false,false,true)],false)],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['literal',false],pure(true),values([],(c,vs,k)=>more(()=>k(c,construct("None",[],vs,[],false,"Option",true))))]],false)]))])]))])]);
function g164(c,args,k){return enterFunction(b164,[1027,1028,1029],null,c,args,k,false,false,[true,true,true],false);}

function d165(l1040,l1041,l1042,l1043,l1044){l1040=small(l1040);l1041=small(l1041);l1042=small(l1042);l1043=small(l1043);l1044=small(l1044);for(;;){t2:{const t1=unref((l1041==(2)));requireDataOwner(t1);if(equal(true,t1)){return dcons("Some",[null],[dcons("Pair",["fst","snd"],[big(iadd(imul((64),l1040,0,9007199254740991,0n,Infinity),l1042,0,9007199254740991,0n,Infinity)),big(l1041)],true,"Pair",true)],false,"Option",true);break t2;}if(equal(false,t1)){t4:{const t3=unref((l1041==(3)));requireDataOwner(t3);if(equal(true,t3)){return dcons("Some",[null],[dcons("Pair",["fst","snd"],[big(iadd(imul((64),iadd(imul((64),l1040,0,9007199254740991,0n,Infinity),l1042,0,9007199254740991,0n,Infinity),0,9007199254740991,0n,Infinity),l1043,0,9007199254740991,0n,Infinity)),big(l1041)],true,"Pair",true)],false,"Option",true);break t4;}if(equal(false,t3)){return dcons("Some",[null],[dcons("Pair",["fst","snd"],[big(iadd(imul((64),iadd(imul((64),iadd(imul((64),l1040,0,9007199254740991,0n,Infinity),l1042,0,9007199254740991,0n,Infinity),0,9007199254740991,0n,Infinity),l1043,0,9007199254740991,0n,Infinity),0,9007199254740991,0n,Infinity),l1044,0,9007199254740991,0n,Infinity)),big(l1041)],true,"Pair",true)],false,"Option",true);break t4;}throw new Error('no arm of the match fits');}break t2;}throw new Error('no arm of the match fits');}}}
function f165(c,args,k){return direct(d165,g165,c,args,k,[0,0,0,0,0]);}

const b165 = matchValue(values([readLocal(1041,false,true,false),pure(2n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),[[['literal',true],pure(true),values([values([values([values([pure(64n),readLocal(1040,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),readLocal(1042,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(1041,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['literal',false],pure(true),matchValue(values([readLocal(1041,false,true,false),pure(3n)],(c,vs,k)=>more(()=>k(c,equal(vs[0],vs[1])))),[[['literal',true],pure(true),values([values([values([values([pure(64n),values([values([pure(64n),readLocal(1040,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),readLocal(1042,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),readLocal(1043,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(1041,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))],[['literal',false],pure(true),values([values([values([values([pure(64n),values([values([pure(64n),values([values([pure(64n),readLocal(1040,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),readLocal(1042,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),readLocal(1043,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],(c,vs,k)=>operated(c,k,()=>checked(vs[0]*vs[1],0n,Infinity))),readLocal(1044,false,false,true)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity))),readLocal(1041,false,false,true)],(c,vs,k)=>more(()=>k(c,construct("Pair",["fst","snd"],vs,[0,1],true,"Pair",true))))],(c,vs,k)=>more(()=>k(c,construct("Some",[null],vs,[0],false,"Option",true))))]],false)]],false);
function g165(c,args,k){return enterFunction(b165,[1040,1041,1042,1043,1044],null,c,args,k,false,false,[true,true,true,true,true],false);}

function d166(l1045,l1046,l1047){l1046=small(l1046);l1047=small(l1047);for(;;){t2:{const t1=unref((l1047<(240)));requireDataOwner(t1);if(equal(true,t1)){return d165(d67(l1047,(224)),(3),d67(d74(l1045,iadd(l1046,(1),0,9007199254740991,0n,Infinity)),(128)),d67(d74(l1045,iadd(l1046,(2),0,9007199254740991,0n,Infinity)),(128)),(0));break t2;}if(equal(false,t1)){return d165(d67(l1047,(240)),(4),d67(d74(l1045,iadd(l1046,(1),0,9007199254740991,0n,Infinity)),(128)),d67(d74(l1045,iadd(l1046,(2),0,9007199254740991,0n,Infinity)),(128)),d67(d74(l1045,iadd(l1046,(3),0,9007199254740991,0n,Infinity)),(128)));break t2;}throw new Error('no arm of the match fits');}}}
function f166(c,args,k){return direct(d166,g166,c,args,k,[0,0,0]);}

const b166 = matchValue(values([readLocal(1047,false,true,false),pure(240n)],(c,vs,k)=>more(()=>k(c,vs[0] < vs[1]))),[[['literal',true],pure(true),callFunction(pure(f165),[callFunction(pure(f67),[readLocal(1047,false,false,true),pure(224n)],false),pure(3n),callFunction(pure(f67),[callFunction(pure(f74),[readLocal(1045,false,true,false),values([readLocal(1046,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),pure(128n)],false),callFunction(pure(f67),[callFunction(pure(f74),[readLocal(1045,false,false,true),values([readLocal(1046,false,false,true),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),pure(128n)],false),pure(0n)],false)],[['literal',false],pure(true),callFunction(pure(f165),[callFunction(pure(f67),[readLocal(1047,false,false,true),pure(240n)],false),pure(4n),callFunction(pure(f67),[callFunction(pure(f74),[readLocal(1045,false,true,false),values([readLocal(1046,false,true,false),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),pure(128n)],false),callFunction(pure(f67),[callFunction(pure(f74),[readLocal(1045,false,true,false),values([readLocal(1046,false,true,false),pure(2n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),pure(128n)],false),callFunction(pure(f67),[callFunction(pure(f74),[readLocal(1045,false,false,true),values([readLocal(1046,false,false,true),pure(3n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))],false),pure(128n)],false)],false)]],false);
function g166(c,args,k){return enterFunction(b166,[1045,1046,1047],null,c,args,k,false,false,[true,true,true],false);}

function d167(l68,l1048){l1048=small(l1048);for(;;){t2:{const t1=unref(l68);requireDataOwner(t1);if(t1.tag==="Nil"&&t1.owner==="List"){return l1048;break t2;}if(t1.tag==="Cons"&&t1.owner==="List"){let l69=t1.fields[0];let l70=t1.fields[1];const t3=l70;const t4=iadd(l1048,(1),0,9007199254740991,0n,Infinity);l68=t3;l1048=t4;continue;break t2;}throw new Error('no arm of the match fits');}}}
function f167(c,args,k){return g167(c,args,k);}

const b167 = matchValue(borrowPlace(68,[],true),[[['ctor',"Nil",[],"List"],pure(true),readLocal(1048,false,false,true)],[['ctor',"Cons",[['bind',69,true,false],['bind',70,true,false]],"List"],pure(true),tailSelfCall(pure(f167),[readLocal(70,false,false,false),values([readLocal(1048,false,false,true),pure(1n)],(c,vs,k)=>operated(c,k,()=>checked(vs[0]+vs[1],0n,Infinity)))])]],false);
function g167(c,args,k){return enterFunction(b167,[68,1048],null,c,args,k,false,false,[false,true],true);}

function instantiate(externs={}, options={}) {return instantiateWith({"syn_load":[f1,true,[null],null],"syn_answer":[f2,true,[null,null],null]},externs,options);}

async function run(show=console.log, externs={}, options={}) {return drive((c,k)=>f0(c,[],k),show,externs,options);}

function synBuild(v,ctors){
    const make=(d,fields)=>({owner:d[3],tag:d[0],names:d[1],fields,struct:d[2]});
    const value=v=>{
        if(typeof v!=='object')return v;
        if(Array.isArray(v)){const fields=[];for(let i=1;i<v.length;i++)fields.push(value(v[i]));return make(ctors[v[0]],fields);}
        if(v.a)return {kind:'Array',items:v.a.map(value)};
        let out=make(ctors[1],[]);
        for(let i=v.l.length-1;i>=0;i--)out=make(ctors[0],[value(v.l[i]),out]);
        return out;
    };
    return value(v);
}
function synCompare(built,read){
    const text=v=>JSON.stringify(v,(k,x)=>typeof x==='bigint'?x+'n':x);
    if(text(built)!==text(read))throw new Error('tauto: a parser read ahead of time is not what the text reads');
    return built;
}
const instance=instantiate();return {load:t=>share(instance.syn_load(t)),build:(v,ctors)=>share(synBuild(v,ctors)),compare:synCompare,answer:instance.syn_answer};})();
