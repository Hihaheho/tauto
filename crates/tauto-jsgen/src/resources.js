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
function envHas(env,id){return envGet(env,id)!==undefined;}
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
