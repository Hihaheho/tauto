const identity=x=>x;
const reference=(get,set)=>({ref:true,get,set});
const unref=x=>{if(stableData.has(x))stableAggregate(x);return x?.ref?x.get():x;};
const copyArray=Array,copyArrayPrototype=Array.prototype,copyArrayMap=Array.prototype.map;
function copyValue(value) {return copyWithin(value,new WeakSet());}
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
        }else if(stableAggregate(value))result=value;
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
        for(let i=path.length-1;i>=0;i--){const key=path[i],index=typeof key==='number'?key:value.names.indexOf(key);parents.push([value,index]);value=value.fields[index];}
        for(let i=parents.length-1;i>=0;i--){
            const [parent,index]=parents[i];
            if(sharedData.has(parent)){const fields=parent.fields.slice();fields[index]=replacement;replacement={...parent,fields};continue;}
            stableData.delete(parent);parent.fields[index]=replacement;replacement=parent;
        }
        root.set(replacement);
    });
    ref.projection={root,path};
    return ref;
}
function placeRef(c,id,path,borrowed) {
    const slot=c.env[id];
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
function signal(){return {kind:'Signal',shared:true,raised:false,waiters:[]};}
function raise(s){if(s.raised)return;s.raised=true;const ws=s.waiters;s.waiters=[];for(const w of ws)w();}
function listItems(value){const out=[];for(let v=value;v.tag==='Cons';v=v.fields[1])out.push(v.fields[0]);return out;}
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
        case 'Text::of_code_point':return a<0n||a>0x10ffffn||(a>=0xd800n&&a<=0xdfffn)?none():some(String.fromCodePoint(Number(a)));
        case 'Text::of_utf8':try{return some(new TextDecoder('utf-8',{fatal:true,ignoreBOM:true}).decode(Uint8Array.from(listItems(a),Number)));}catch{return none();}
        case 'I64::of_i32':case 'I64::of_u64':return checked(a,-9223372036854775808n,9223372036854775807n);
        case 'I32::of_i64':return checked(a,-2147483648n,2147483647n);
        case 'Nat::of_u64':return a;case 'U64::of_i64':case 'U64::of_u32':case 'U64::of_u8':case 'U64::of_nat':return checked(a,0n,18446744073709551615n);
        case 'U32::of_u64':return checked(a,0n,4294967295n);
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
    }
}
function builtin(name,args) {
    return values(args,(c,vs,k)=>{
        const done=v=>more(()=>k(c,v));
        if(vs[0]?.operation&&['replace','Buf::push','Vec::push','Vec::pop','Vec::len','Slice::len','Vec::as_slice','Vec::as_mut_slice','Vec::clear','Vec::truncate','Vec::get','Vec::get_mut','Slice::get','Vec::last_mut','Vec::index','Vec::swap'].includes(name)){
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
            case 'Vec::index':return inRange(a,n)?done(indexRef(vs[0],n)):route(c,'out_of_bounds','zero',[],k);
            case 'Vec::swap':if(!inRange(a,n)||!inRange(a,vs[2]))return route(c,'out_of_bounds','zero',[],k);[a.items[Number(n)],a.items[Number(vs[2])]]=[a.items[Number(vs[2])],a.items[Number(n)]];return done(null);
            case 'Vec::into_list':case 'Array::to_list':return done(list(a.items.map(copyValue)));
            case 'Vec::into_array':{const items=a.items;a.items=[];return done({kind:'Array',items});}
            case 'Array::of_list':return done({kind:'Array',items:listItems(a)});
            // `Secret`: shared like its content; `shown` does not print it.
            case 'secret':return done({kind:'Secret',shared:true,value:a});
            case 'expose':return done(a.value);
            case 'Bytes::of_list':return done(bytesValue(Uint8Array.from(listItems(a),Number)));
            case 'Bytes::to_list':return done(list(Array.from(a.bytes,x=>byteValues[x])));
            case 'Bytes::len':return done(BigInt(a.bytes.length));
            case 'Bytes::get':return done(n>=0n&&n<BigInt(a.bytes.length)?some(BigInt(a.bytes[Number(n)])):none());
            case 'Bytes::slice':{const end=vs[2];return done(n<0n||end<n||end>BigInt(a.bytes.length)?none():some(bytesValue(a.bytes.subarray(Number(n),Number(end)))));}
            case 'Bytes::concat':{const out=new Uint8Array(a.bytes.length+b.bytes.length);out.set(a.bytes);out.set(b.bytes,a.bytes.length);return done(bytesValue(out));}
            case 'Bytes::eq':return done(a.bytes.length===b.bytes.length&&a.bytes.every((x,i)=>x===b.bytes[i]));
            case 'Bytes::of_text':return done(bytesValue(textEncoder.encode(a)));
            case 'Text::of_bytes':try{return done(some(utf8Decoder.decode(a.bytes)));}catch{return done(none());}
            case 'Array::get':return done(inRange(a,n)?some(copyValue(a.items[Number(n)])):none());
            case 'HashMap::new':return done({kind:'HashMap',items:[]});
            case 'HashMap::insert':{const i=a.items.findIndex(([key])=>equal(key,b));if(i<0){a.items.push([b,vs[2]]);return done(none());}const old=a.items[i][1];a.items[i][1]=vs[2];return done(some(old));}
            case 'HashMap::get':case 'HashMap::get_mut':case 'HashMap::index':{
                const i=a.items.findIndex(([key])=>equal(key,b));
                if(i<0)return name==='HashMap::index'?route(c,'missing','zero',[],k):done(none());
                const ref=reference(()=>a.items[i][1],v=>{a.items[i][1]=v;});return done(name==='HashMap::index'?ref:some(ref));
            }
            case 'HashMap::into_vec':return done(vec(a.items.map(([x,y])=>pair(x,y))));
            case 'Text::byte':case 'Text::slice':case 'Text::of_code_point':case 'Text::of_utf8':case 'I64::of_i32':case 'I64::of_u64':case 'I32::of_i64':case 'Nat::of_u64':case 'U64::of_i64':case 'U64::of_u32':case 'U64::of_u8':case 'U64::of_nat':case 'U32::of_u64':case 'U8::of_u64':case 'U32::and':case 'U32::or':case 'U32::xor':case 'U32::shl':case 'U32::shr':case 'U32::rotl':case 'U32::rotr':case 'U64::and':case 'U64::or':case 'U64::xor':case 'U64::shl':case 'U64::shr':case 'U64::rotl':case 'U64::rotr':return done(pureBuiltin(name,vs));
            case 'Float::of_i64':case 'I64::of_float':case 'Float::of_text':case 'Text::of_float':case 'Float::bits':case 'Float::of_bits':case 'Float::is_nan':case 'Float::abs':case 'Float::floor':case 'Float::ceil':case 'Float::trunc':case 'Float::round':case 'Float::sqrt':case 'Float::cbrt':case 'Float::exp':case 'Float::ln':case 'Float::log2':case 'Float::log10':case 'Float::pow':case 'Float::sin':case 'Float::cos':case 'Float::tan':case 'Float::asin':case 'Float::acos':case 'Float::atan':case 'Float::atan2':case 'Float::sinh':case 'Float::cosh':case 'Float::tanh':return done(floatBuiltin(name,vs));
            case 'Float32::of_float':case 'Float::of_float32':case 'Float32::bits':case 'Float32::of_bits':case 'Float32::is_nan':case 'Float32::abs':case 'Float32::floor':case 'Float32::ceil':case 'Float32::trunc':case 'Float32::round':case 'Float32::sqrt':case 'Float32::cbrt':case 'Float32::exp':case 'Float32::ln':case 'Float32::log2':case 'Float32::log10':case 'Float32::pow':case 'Float32::sin':case 'Float32::cos':case 'Float32::tan':case 'Float32::asin':case 'Float32::acos':case 'Float32::atan':case 'Float32::atan2':case 'Float32::sinh':case 'Float32::cosh':case 'Float32::tanh':return done(pureBuiltin(name,vs));
            case 'words':return done(list(a.split(/\p{White_Space}+/u).filter(Boolean)));
            case 'Ref::new':return done({kind:'Ref',shared:true,value:a});
            case 'Ref::get':return done(copyValue(a.value));
            case 'Ref::set':a.value=vs[1];return done(null);
            case 'Weak::of':return done({kind:'Weak',shared:true,target:new WeakRef(a)});
            case 'Weak::get':{const r=a.target.deref();return done(r===undefined?none():some(r));}
            case 'Atomic::new':return done({kind:'Atomic',shared:true,value:a});
            case 'Atomic::load':return done(a.value);
            case 'Atomic::store':a.value=b;return done(null);
            case 'Atomic::fetch_add':{const old=a.value;a.value=BigInt.asUintN(64,old+b);return done(old);}
            case 'Mutex::new':return done({kind:'Mutex',shared:true,value:a,full:true,waiting:[]});
            // A place in the mutex's line: its signal is raised when the content is handed to it.
            case 'Mutex::claim':{const s=signal();if(a.full&&!a.waiting.length){a.full=false;s.handed=a.value;a.value=undefined;raise(s);}else a.waiting.push(s);return done(s);}
            case 'Mutex::take_claimed':{const v=b.handed;b.handed=undefined;return done(v);}
            case 'Mutex::put':if(a.waiting.length){const s=a.waiting.shift();s.handed=b;raise(s);}else{a.value=b;a.full=true;}return done(null);
            case 'Pending::ready':return done({kind:'Pending',resource:true,value:a});
            // What may take a while runs as a task of its own, whose result the caller waits for.
            case 'Os::offload':
            case 'pending_spawn':{const promise=drive((d,t)=>a(d,[],t),c.host.show,c.host.externs,c.host.options);const p={kind:'Pending',resource:true,promise,ready:false};promise.then(()=>{p.ready=true;},()=>{p.ready=true;});return done(p);}
            // A task still running gets a turn before the answer, so a loop that polls lets it go on.
            case 'Pending::is_ready':if(!a.promise||a.ready)return done(true);return new Promise(resolve=>setTimeout(()=>resolve(more(()=>k(c,a.ready))),0));
            case 'Pending::signal':{const s=signal();if(!a.promise||a.ready)raise(s);else a.promise.then(()=>raise(s),()=>raise(s));return done(s);}
            case 'Pending::take':return a.promise?a.promise.then(v=>more(()=>k(c,v))):done(a.value);
            case 'budget_value':return done({answer:'value',value:a});
            case 'info_more':return done({answer:'more',steps:b});
            case 'info_unbounded':return done({answer:'more',steps:null});
            case 'Os::args':return done(list(c.host.options.args??[]));
            case 'Os::print':case 'Os::eprint':{
                const f=c.host.options['os_'+name.slice(4)];if(!f)throw new Error('host does not provide os_'+name.slice(4));
                forgetStableData();try{f(a);}finally{forgetStableData();}return done(null);
            }
            case 'Os::read_file':case 'Os::write_file':case 'Os::read_bytes':case 'Os::write_bytes':case 'Os::create_dir':{
                const f=c.host.options['os_'+name.slice(4)];if(!f)throw new Error('host does not provide os_'+name.slice(4));
                // Bytes cross as a Uint8Array of their own: the host may keep or change it.
                const bytes=name==='Os::read_bytes',args=name==='Os::write_bytes'?[unref(vs[0]),unref(vs[1]).bytes.slice()]:vs.map(unref);
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
            case 'Os::list_dir':case 'Os::remove':case 'Os::temp_dir':case 'Os::run':{
                const f=c.host.options['os_'+name.slice(4)];if(!f)return done(err('host does not provide os_'+name.slice(4)));
                let call;
                if(name==='Os::run'){const flat=listItems(vs[3]).map(String);const env=[];for(let i=0;i+1<flat.length;i+=2)env.push([flat[i],flat[i+1]]);call=()=>f(unref(vs[0]),listItems(vs[1]).map(String),unref(vs[2]),env,unref(vs[4]).bytes.slice());}
                else call=()=>f(...vs.map(unref));
                // The exit status (`null` when a signal ended it), standard output and standard error.
                const back=r=>{
                    if(name==='Os::list_dir')return list([...r].map(String).sort((x,y)=>x<y?-1:x>y?1:0));
                    if(name==='Os::temp_dir'){const dir=String(r);permissionGrantDir(c.host.options,dir);return dir;}
                    if(name==='Os::run')return pair(list([r.status===null||r.status===undefined?'':String(r.status),String(r.stderr??'')]),bytesValue(new Uint8Array(r.stdout??[])));
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
            case 'Os::read_line':{
                const f=c.host.options.os_read_line;if(!f)throw new Error('host does not provide os_read_line');
                const line=f();return done(line===null||line===undefined?none():some(String(line)));
            }
            case 'Os::env':{
                const env=c.host.options.env??{};const v=Object.prototype.hasOwnProperty.call(env,a)?env[a]:undefined;
                return done(v===undefined||v===null?none():some(String(v)));
            }
            case 'Os::wall_ms':return done(BigInt(Date.now()));
            case 'Os::monotonic_ns':return done(BigInt(Math.floor(performance.now()*1e6)));
            case 'Os::sleep_pending':{const promise=new Promise(resolve=>setTimeout(()=>resolve(null),Number(a)));const p={kind:'Pending',resource:true,promise,ready:false};promise.then(()=>{p.ready=true;});return done(p);}
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
                        ([items,got])=>more(()=>k(c,ok(pair(list(items.map(String)),bytesValue(got))))),
                        e=>more(()=>k(c,err(e.message??String(e)))));
                }
                const f=c.host.options.fetch??globalThis.fetch;if(!f)return done(err('host does not provide fetch'));
                return Promise.resolve().then(()=>f(b,init)).then(async r=>{
                    const out=[String(r.status)];let bad=null;
                    r.headers.forEach((v,n)=>{const t=headerText(v);if(t===null)bad??=n;else out.push(n,t);});
                    if(bad!==null)return more(()=>k(c,err('the value of the response header '+bad+' is not UTF-8')));
                    const got=new Uint8Array(await r.arrayBuffer());
                    return more(()=>k(c,ok(pair(list(out),bytesValue(got)))));
                },e=>more(()=>k(c,err(e.message??String(e)))));
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
            // TLS: the JavaScript host has none yet. A program that needs it here answers
            // `tls_*` with a handler of its own.
            case 'Os::tls_close':return done(null);
            case 'Os::tls_accept':case 'Os::tls_connect':case 'Os::tls_read':case 'Os::tls_write':case 'Os::tls_shutdown':
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

function temporaryRef(v,immutable=false){const ref=reference(()=>v,x=>{v=x;});let owners=1;ref.temporary=true;ref.retain=()=>{owners++;};ref.release=()=>{if(--owners!==0)return;const value=v;v=undefined;dropValue(value);};if(immutable&&stableAggregate(v)){const value=v;trackStableReference(ref,stableState(()=>v===value&&stableAggregate(value)));}return ref;}
