// The runtime of the JavaScript backend, written by hand and copied into
// the generated programs. Integers retain their complete declared range.
function checked(n, min, max) {
    if (n < min || n > max) throw new Error('the number is too large');
    return n;
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
function ineg(a,lo,hi,min,max){if(typeof a==='number'){const r=0-a;if(r>=lo&&r<=hi)return r;}return small(checked(-big(a),min,max));}
// Both quotients of safe integers are exact: `a / b` is within less than
// `1 / |b|` of the true quotient, so truncating it cannot cross an integer.
function idivide(op,a,b,lo,hi,min,max){
    if(typeof a==='number'&&typeof b==='number'&&b!==0){const r=op==='div'?Math.trunc(a/b):a%b;if(r>=lo&&r<=hi)return r+0;}
    return small(divide(op,[big(a),big(b)],min,max));
}
function u32and(a,b){return typeof a==='number'&&typeof b==='number'?(a&b)>>>0:Number(big(a)&big(b));}
function u32or(a,b){return typeof a==='number'&&typeof b==='number'?(a|b)>>>0:Number(big(a)|big(b));}
function u32xor(a,b){return typeof a==='number'&&typeof b==='number'?(a^b)>>>0:Number(big(a)^big(b));}
function u32shl(a,b){return typeof a==='number'&&typeof b==='number'?(a<<(b%32))>>>0:Number(BigInt.asUintN(32,big(a)<<(big(b)%32n)));}
function u32shr(a,b){return typeof a==='number'&&typeof b==='number'?a>>>(b%32):Number(big(a)>>(big(b)%32n));}
function compare(a,b) {
    // Walk scalar values, not UTF-16 code units, without allocating arrays.
    let i=0,j=0;
    while(i<a.length&&j<b.length){
        const x=a.codePointAt(i),y=b.codePointAt(j);
        if(x!==y)return x<y?-1n:1n;
        i+=x>0xffff?2:1;j+=y>0xffff?2:1;
    }
    return i<a.length?1n:j<b.length?-1n:0n;
}
function field(v,name,index) {if(v?.project){const part=v.project(index??name,false);try{return dereference(part,true);}finally{part.release();}}const obj=unref(v);const i=index??obj.names.indexOf(name);return copyValue(unref(obj.fields[i]));}
function equal(a,b) {
    a=unref(a);b=unref(b);
    if(a?.union!==undefined)a=a.value;
    if(b?.union!==undefined)b=b.value;
    requireDataOwner(a);requireDataOwner(b);
    if(a===b)return true;
    if(a?.hostType!==undefined||b?.hostType!==undefined)return false;
    if(!a||!b||typeof a!=='object'||typeof b!=='object')return false;
    if(a.kind!==b.kind||a.tag!==b.tag||a.owner!==b.owner)return false;
    if(a.kind==='Buf')return a.text===b.text;
    if(a.kind==='Bytes')return a.bytes.length===b.bytes.length&&a.bytes.every((x,i)=>x===b.bytes[i]);
    const x=Array.isArray(a)?a:a.fields??a.items,y=Array.isArray(b)?b:b.fields??b.items;
    return Array.isArray(x)&&Array.isArray(y)&&x.length===y.length&&x.every((v,i)=>equal(v,y[i]));
}
function shown(v) {
    v=unref(v);
    if(v?.union!==undefined)return shown(v.value);
    switch(v?.kind) {
        case 'Shown':return v.text;
        case 'Buf':return 'Buf('+quoteText(v.text)+')';
        case 'Vec':case 'Array':return v.kind+'['+v.items.map(shown).join(', ')+']';
        case 'HashMap':return 'HashMap{'+v.items.map(([k,x])=>shown(k)+': '+shown(x)).join(', ')+'}';
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
function ordinaryArrayMethods(value){
    if(Array!==provenanceArray||!provenanceIsArray(value)
        ||provenancePrototype(value)!==provenanceArrayPrototype
        ||provenancePrototype(provenanceArrayPrototype)!==provenanceObjectPrototype
        ||provenancePrototype(provenanceObjectPrototype)!==null
        ||provenanceDescriptor(value,'constructor')!==undefined)return false;
    const ownMap=provenanceDescriptor(value,'map');
    if(ownMap!==undefined&&ownMap.value!==provenanceArrayMethods[0][1])return false;
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
        sharedFreeze(v.names);sharedFreeze(v.fields);sharedFreeze(v);sharedData.add(v);
        for(let i=0;i<v.fields.length;i++)pending.push(v.fields[i]);
    }
    return value;
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
    const copyShared=root=>{
        const top={...root,fields:root.fields.slice()},pending=[top];
        while(pending.length){
            const v=pending.pop(),fields=v.fields;
            for(let i=0;i<fields.length;i++){const f=fields[i];if(sharedData.has(f)){fields[i]={...f,fields:f.fields.slice()};pending.push(fields[i]);}}
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
    if (ev.fuel.left-- <= 0) throw new Error('interrupted: the step limit ran out');
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
