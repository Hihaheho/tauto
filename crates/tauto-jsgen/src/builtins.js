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
            // A host object (a Map, a Set, a class instance) is not Tauto data: copying it field by field would drop its contents. A copy of a host-owned value (an affine one moves) stands for the same object.
            else if(!Array.isArray(value)&&Object.getPrototypeOf(value)!==Object.prototype&&Object.getPrototypeOf(value)!==null)result=value;
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
function dereferenceTemporary(value){const copied=dereference(value,true);if(value?.release)value.release();return copied;}
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
function assignPlace(id,path,borrowed,value){return (c,k)=>value(c,(d,v)=>{const target=placeRef(d,id,path,borrowed);try{target.set(v);}finally{if(target.temporary)target.release();}return more(()=>k(d,null));});}
function remapUnion(v,to,table){return to===null?v.value:{union:to,variant:table[v.variant],value:v.value};}
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
            case 'Slots::copy':{const r=slotsNew(BigInt(a.items.length),vs[1],vs[2]);for(let i=0;i<a.items.length;i++)if(a.items[i]!==undefined)r.items[i]=copyValue(a.items[i]);return done(r);}
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
function budgetValue(id,steps,body,memory=false) {
    return (c,k)=>steps(c,(d,n)=>{
        const budget={id,memory,left:null};
        budget.left=budgetRefill(budget,n);
        const h={id:{},outer:d.h,env:d.env,arms:[],budget,target:k,scope:d.scope};
        return body({...d,h},(next,v)=>more(()=>next.h.target({...next,h:next.h.outer},v)));
    });
}
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
