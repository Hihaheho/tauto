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
    for(const [id,slot] of Object.entries(env))scopeAlias(scope,Number(id),slot);
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
        if(boundaryEnv&&frames.length)for(const [id,slot] of Object.entries(boundaryEnv))scopeAlias(frames[frames.length-1],Number(id),slot);
        return {originals:frames,sourceSlots:slots,frames,env:c.env,inPlace:true};
    }
    for(const s of frames)for(const slot of s.slots)if(clone&&!slot.shared)slots.set(slot,{...slot});
    const copies=frames.map(s=>{const frame={...s,slots:s.slots.map(slot=>slots.get(slot)??slot)};copyScopeAliases(s,frame,slots);return frame;});
    // A resumed body keeps its lexical boundary before its new dynamic caller.
    // Empty raw snapshots have no body frame on which to install a boundary.
    if(boundaryEnv&&copies.length)for(const [id,slot] of Object.entries(boundaryEnv))scopeAlias(copies[copies.length-1],Number(id),slots.get(slot)??slot);
    return {originals:frames,sourceSlots:slots,frames:copies,env:Object.fromEntries(Object.entries(c.env).map(([id,slot])=>[id,slots.get(slot)??slot]))};
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
    return {scope,scopes,sourceSlots,env:Object.fromEntries(Object.entries(snapshot.env).map(([id,slot])=>[id,slots.get(slot)??slot]))};
}

function restoreEnv(env,scope){
 // Every return runs this, so it allocates only when a slot was replaced.
 // Until an alias or a resumption rebinds an id, every binding is still
 // its own, and the walk is skipped.
 if(!slotsRebound)return env;
 const ids=Object.keys(env),found={};
 let left=ids.length;
 for(let s=scope;s&&left;s=s.parent){
  for(const slot of s.slots)if(slot.id in env&&!(slot.id in found)){found[slot.id]=slot;left--;}
  const aliases=scopeAliases.get(s);
  if(aliases)for(const {id,slot} of aliases)if(id in env&&!(id in found)){found[id]=slot;left--;}
 }
 let same=true;
 for(const id of ids)if(id in found&&found[id]!==env[id]){same=false;break;}
 if(same)return env;
 const out={};
 for(const id of ids)out[id]=id in found?found[id]:env[id];
 return out;
}

function exitScope(scope,id){let found=scope;while(found&&found.id!==id)found=found.parent;if(!found)return scope;while(scope){const done=scope.id===id;closeScope(scope);scope=scope.parent;if(done)break;}return scope;}
