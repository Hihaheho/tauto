// Computations return a trampoline step. Promise suspension belongs to the
// driver; effect continuations remain ordinary, reusable values.
const more = f => f;
const pure = value => (c, k) => more(() => k(c, value));
const mapValue = (e, f) => (c, k) => e(c, (d, v) => more(() => k(d, f(v))));
const values = (es, f) => (c, k) => {
    const scope=openScope(c.scope),env={...c.env};
    // Temporaries are numbered by their depth in the context, so siblings reuse
    // ids and environments keep the same shape from one iteration to the next.
    const base=c.td??0,ids=es.map((_,i)=>-(base+i+1));
    for(const id of ids)env[id]=own(scope,{id,value:undefined,shared:false});
    const finish=(d,value)=>{
        const parent=exitScope(d.scope,scope.id);
        return more(()=>k({...d,scope:parent,env:restoreEnv(c.env,parent),td:c.td},value));
    };
    const loop = (i, d) => {
        if(i===es.length){
            const args=ids.map(id=>{const slot=d.env[id],value=slot.value;if(!value?.temporary)slot.value=undefined;return value;});
            return more(()=>f(d,args,finish));
        }
        return es[i](d,(next,value)=>{next.env[ids[i]].value=value;return more(()=>loop(i+1,next));});
    };
    return loop(0,{...c,scope,env,td:base+ids.length});
};
function readLocal(id,deref=false,copy=false,move=false) { return (c,k)=>more(()=>{const slot=c.env[id];let v=slot.value;if(deref&&copy&&v?.cloneOwned){v=v.cloneOwned();copy=false;}else if(deref)v=unref(v);if(move)slot.value=undefined;return k(c,copy?copyValue(v):!deref&&!move&&v?.ref?borrowedRef(v):v);}); }
function defineLocal(id, shared, init, immutable=false) {
    return (c, k) => init(c, (d, v) => {
        const env = {...d.env, [id]: own(d.scope,{id,value: v, shared,immutable})};
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
function loopWhile(cond, body, ticked) {
    return (c, k) => {
        const loop = d => cond(d,(next,yes) => {
            if (!yes) return more(() => k(next,null));
            return ticked?tickBudget(next,(t)=>body(t,(after)=>more(()=>loop(after)))):body(next,(after)=>more(()=>loop(after)));
        });
        return more(() => loop(c));
    };
}
const returnValue = e => (c, k) => e(c,(d,v) => more(() => d.ret(d,v)));
function callFunction(fn, args, ticked) {
    return values([fn,...args], (c,[value,...vs],k) => {
        const f=unref(value),scope=openScope(c.scope),id=-(c.td??0)-1;
        const env={...c.env,[id]:own(scope,{id,value,shared:false})};
        const inner={...c,env,scope,td:-id};
        const finish=(d,v)=>{const parent=exitScope(d.scope,scope.id);return more(()=>k({...d,scope:parent,env:restoreEnv(c.env,parent),td:c.td},v));};
        const enter=d=>f.tautoNative?external(f,vs.map(pure))(d,finish):more(()=>f(d,vs,finish));
        return ticked?tickBudget(inner,enter):enter(inner);
    });
}
function tailSelfCall(fn,args) {
    return (c,k)=>{
        if(!c.restart)return callFunction(fn,args,false)(c,k);
        return values(args,(d,vs,finish)=>{
            // Static eligibility excludes effects, borrows and destructors.
            // Unknown host values still keep the ordinary ownership path.
            if(d.h!==d.restart.handlers||!allStableMembers(vs))return callFunction(fn,vs.map(pure),false)(d,finish);
            return more(()=>d.restart.run(d,vs));
        })(c,k);
    };
}
function enterFunction(body, params, captures, caller, args, k, borrowed=false, exportBorrows=true, ownedParams=[], restartable=false, consumeCaptures=false) {
    const env = {},scope=openScope(caller.scope);
    for(const [id,slot] of Object.entries(captures)){
        if(borrowed||slot.shared){env[id]=slot;scopeAlias(scope,Number(id),slot);}
        else {
            env[id]=own(scope,{...slot,value:consumeCaptures?slot.value:copyValue(slot.value)});
            if(consumeCaptures)slot.value=undefined;
        }
    }
    for (let i=0;i<params.length;i++){if(args[i]?.ref&&args[i]?.retain)args[i].retain();env[params[i]]=own(scope,{id:params[i],value:args[i],shared:false,immutable:ownedParams[i]===true});}
    const boundary = caller.h?.id;
    const ret = (d,v) => {
        if(exportBorrows)v=exportBorrow(v);
        let h = d.h;
        while (h && h.id !== boundary) h = h.outer;
        const scope=unwind(d.scope,caller.scope);
        return more(() => k({...caller,scope,env:restoreEnv(caller.env,scope),h},v));
    };
    const restart=restartable&&allStableMembers(args)?{
        handlers:caller.h,
        run:(d,values)=>{
            const parent=unwind(d.scope,caller.scope);
            return more(()=>enterFunction(body,params,captures,{...caller,scope:parent},values,k,borrowed,exportBorrows,ownedParams,true));
        }
    }:null;
    return more(() => body({...caller,env,ret,scope,restart},ret));
}
function closureValue(body,params,captureIds,borrowed=false,refs=[],exportBorrows=true,ownedParams=[],captureMoves=[],once=false) {
    return (c,k) => {
        if(!borrowed)charge(1);
        const captures = {};
        const releaseCaptures=()=>{
            for(const slot of Object.values(captures)){
                if(slot.shared){if(--slot.owners===0)dropValue(slot.value);}
                else if(!borrowed){dropValue(slot.value);slot.value=undefined;}
            }
        };
        try{
            for(const id of captureIds){
                if(!Object.hasOwn(c.env,id))continue;
                const slot=c.env[id];
                if(slot.shared)slot.owners++;
                if(borrowed||slot.shared)captures[id]=slot;
                else{
                    const moved=captureMoves.includes(id);
                    captures[id]={...slot,value:moved?slot.value:copyValue(slot.value)};
                    if(moved)slot.value=undefined;
                }
            }
            for(const [inner,outer] of refs) captures[inner]={value:placeRef(c,outer,[],true),shared:true};
        }catch(error){releaseCaptures();throw error;}
        let called=false;
        const fn=(caller,args,target)=>{
            if(once&&called)throw new Error('owned closure called more than once');
            called=true;
            return enterFunction(body,params,captures,caller,args,target,borrowed,exportBorrows,ownedParams,false,once&&!borrowed);
        };
        let owners=1;
        fn.retain=()=>{owners++;};
        fn.release=()=>{if(--owners===0)releaseCaptures();};
        return more(() => k(c,fn));
    };
}
// With `taken`, the match owns `v` outright: a binding takes its part instead
// of copying it, and `taken` records where it came from, so a chosen arm can
// clear that place before the scrutinee is dropped.
function matchPattern(p,v,bindings,taken=null,from=null,index=0) {
    switch(p[0]) {
        case 'wild': return true;
        case 'bind':
            if(taken&&!p[2]&&!v?.ref){bindings[p[1]]={value:v,shared:false,immutable:p[3]===true};taken.push([from,index,bindings[p[1]]]);return true;}
            bindings[p[1]]={value:p[2]?(v?.ref?copyValue(v):reference(()=>v,x=>{v=x;})):copyValue(unref(v)),shared:false,immutable:!p[2]&&p[3]===true};return true;
        case 'literal': return equal(p[1],unref(v));
        case 'product': { const obj=unref(v);const inner=v?.ref?null:taken;return p[1].every((q,i)=>matchPattern(q,v?.ref?fieldRef(v,i):obj.fields[i],bindings,inner,obj,i)); }
        case 'ctor': { const obj=unref(v);requireDataOwner(obj);const inner=v?.ref?null:taken;return obj?.tag===p[1]&&obj.owner===p[3]&&p[2].every((q,i)=>matchPattern(q,v?.ref?fieldRef(v,i):obj.fields[i],bindings,inner,obj,i)); }
    }
}
// `take` is set only when the scrutinee is a fresh owned value and no arm has
// a guard, so a matched arm is final once its pattern fits.
function matchValue(scrut,arms,take=false) {
    return (c,k)=>scrut(c,(d,v)=>{
        const scope=openScope(d.scope),id=-(d.td??0)-1;
        const slot=own(scope,{id,value:v,shared:false});
        const env={...d.env,[id]:slot};
        const finish=(after,value)=>{const parent=exitScope(after.scope,scope.id);return more(()=>k({...after,scope:parent,env:restoreEnv(d.env,parent),td:d.td},value));};
        const loop=i=>{
            if(i===arms.length)throw new Error('no arm of the match fits');
            const [pat,guard,body]=arms[i],bindings={},taken=take?[]:null;
            if(!matchPattern(pat,v,bindings,taken)){
                const kept=new Set(taken?.map(t=>t[2]));
                for(const binding of Object.values(bindings))if(!kept.has(binding))dropValue(binding.value);
                return more(()=>loop(i+1));
            }
            if(taken)for(const [from,index] of taken){if(from){if(sharedData.has(from))continue;stableData.delete(from);from.fields[index]=undefined;}else slot.value=undefined;}
            for(const [id,slot] of Object.entries(bindings))own(scope,Object.assign(slot,{id:Number(id)}));
            const inner={...d,scope,env:{...env,...bindings},td:-id};
            return guard(inner,(next,yes)=>{
                if(yes)return more(()=>body(next,finish));
                for(const slot of Object.values(bindings)){dropValue(slot.value);slot.value=undefined;}
                return more(()=>loop(i+1));
            });
        };
        return loop(0);
    });
}
function handleValue(body,arms,ret) {
    return (c,k) => {
        const h={id:{},outer:c.h,env:c.env,arms,target:k,scope:c.scope};
        const inner={...c,h};
        return more(()=>body(inner,(d,v)=>{
            const frame=d.h;
            const out={...d,h:frame.outer};
            if(ret){
                const scope=openAliasScope(out.scope,frame.env);
                return matchValue(pure(v),[ret])({...out,scope,env:frame.env},(after,value)=>{
                    const parent=exitScope(after.scope,scope.id);
                    return more(()=>frame.target({...after,scope:parent,env:frame.env},value));
                });
            }
            return more(()=>frame.target(out,v));
        }));
    };
}
function performValue(op,quant,args) {
    return values(args,(c,vs,k)=>route(c,op,quant,vs,k));
}
function route(c,op,quant,vs,k,inside=null,skip=null) {
    let outside=inside===null;
    const prefix=[];
    const search=frame=>{
        if(!frame) {
            if(op==='show'){const text=vs[0]+' = '+shown(vs[1]);forgetStableData();try{c.host.show(text);}finally{forgetStableData();}return more(()=>k(c,null));}
            // The host answers `wait`: the task goes on once its signal is raised.
            if(op==='wait'&&vs[0]?.kind==='Signal'){const s=vs[0];if(s.raised)return more(()=>k(c,null));return new Promise(resolve=>s.waiters.push(()=>resolve(more(()=>k(c,null)))));}
            throw new Error('nothing handles '+op);
        }
        if(frame.callback && quant!=='direct' && frame.id!==skip?.id)return frame.suspend(c,op,quant,vs,k);
        prefix.push(frame);
        if(frame.budget===inside)outside=true;
        const arms=outside?frame.arms.filter(a=>a.op===op):[];
        const armAt=i=>{
            if(i===arms.length)return more(()=>search(frame.outer));
            const arm=arms[i],bindings={};
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
                    const env=Object.fromEntries(Object.entries(old.env).map(([id,slot])=>[id,context.sourceSlots.get(slot)??slot]));
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
            const releaseInitial=()=>{if(!initialOwned)return;initialOwned=false;pending.delete(releaseInitial);if(accepted&&!resumed)for(const frame of captured)frame.cancel?.();if(arm.k===null||bindings[arm.k].value===resume)resume.release();keepAround();};
            if(quant!=='direct')pending.add(releaseInitial);
            resume.retain=()=>{owners++;};
            // The bindings around the handle: a `k` kept past its arm reads
            // them after their scope may have closed, so that scope leaves
            // them to it.
            let around=[];
            const keepAround=()=>{if(owners===0||quant==='direct')return;around=Object.values(frame.env);for(const slot of around)(slot.keptBy??=new Set()).add(resume);};
            resume.release=()=>{if(--owners!==0)return;unprotect();if(ownsSnapshot())for(const scope of snapshot.originals)closeScope(scope);for(const slot of around)unkeep(slot,resume);};
            if(arm.k!==null)bindings[arm.k]={value:resume,shared:false};
            const env={...frame.env,...bindings},scope=openAliasScope(frame.scope,env);
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
    hostHandles.add(handle);host.handles.add(handle);
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
        const hostArgs=vs.map((v,i)=>{const type=signature?.params[i];if(type){if(v?.ref)return hostObject(c.host,type,v.get());const object=hostObject(c.host,type,v);consumed.push(v);return object;}const value=unref(v);if(typeof value==='function'&&signature?.owner!=null)return keptCallback(c.host,vs[signature.owner]?.ref?vs[signature.owner].get():vs[signature.owner],value);if(typeof value==='function'){if(value.tautoNative)return value;const adapted=callback(value);adapted.nib=value;adapted.release=()=>{if(!v?.ref)dropValue(value);};return adapted;}if(fn.tautoNative)return v;if(!v?.ref)return thaw(v);{const target=v.get(),own=thaw(target);if(own!==target)v.set(own);}return reference(()=>{alive();return v.get();},x=>{alive();v.set(x);});});
        let value;
        try{value=fn.tautoNative?fn.invoke(hostArgs,callback,!c.direct,c.wasm??null):fn(...hostArgs);}catch(e){forgetStableData();cancel();throw e;}
        // The host has the object now; the moved Tauto references end.
        finally{for(const handle of consumed)handle.toHost();}
        forgetStableData();
        if(value&&typeof value.then==='function') {
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
// `permissions.div` lets `Div` run without it (`--allow-div`).
function hostSteps(options){return options.steps??(options.permissions?.div===true?Infinity:10000000);}
function newHost(show,externs,options){
    return {show,externs,options,temporary:0,fuel:{left:hostSteps(options)},handles:new Set(),objects:new WeakMap(),instance:{}};
}
// Each call has its own context, handlers and step budget; the instance's
// host values outlive the call.
function startCall(host){
    const call={...host,temporary:0,fuel:{left:hostSteps(host.options)}};
    let result;
    const c={env:{},h:null,host:call,ret:null,direct:false,scope:openScope(null)};
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
async function driveIn(start,host){
    forgetStableData();
    const {c,finish,result}=startCall(host);
    try {
        let step=start(c,finish);
        while(step!==null){
            if(typeof step==='function')step=step();
            else{forgetStableData();try{step=await step;}finally{forgetStableData();}}
        }
    } finally {endCall(c);}
    return result();
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
async function drive(start,show,externs,options={}) {
    const host=newHost(show,externs,options);
    try{return await driveIn(start,host);}finally{disposeHost(host);}
}
// An instance runs exported functions; importing the module runs nothing.
// A host object argument gets a handle of the instance, a borrowed one only
// for the call; a host function is callable during the call; a function
// result is kept by the instance until it is disposed.
function instantiateWith(table,externs,options){
    const host=newHost(options.show??console.log,externs,options);
    let disposed=false,running=0;
    const owner={kept:[],closing:false,enter(){},leave(){}};
    const instance={dispose(){if(disposed)return;disposed=true;owner.closing=true;
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
                return v;
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
function T(v){if(H.fuel.left--<=0)throw new Error('interrupted: the step limit ran out');return v;}
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
function dcons(tag,names,fields,isStruct,owner){charge(1+fields.length);return generatedAggregate({owner,tag,names,fields,struct:isStruct},fields);}
const dsome=v=>dcons('Some',[null],[v],false,'Option'),dnone=()=>dcons('None',[],[],false,'Option');
function vecNew(){const v=vec([]);F.add(v.items);return v;}
function vecGet(v,i){const a=v.items;i=Number(i);return i>=0&&i<a.length?dsome(a[i]):dnone();}
function vecGetMut(v,i){const a=v.items;i=Number(i);return i>=0&&i<a.length?dsome(new VecCell(a,i)):dnone();}
function vecPush(v,x){const a=v.items;if(logged(a))J.push(a,-1,a.length);a.push(x);return null;}
function vecPop(v){const a=v.items;if(!a.length)return dnone();const x=a.pop();if(logged(a))J.push(a,-3,x);return dsome(x);}
// Emptied or cut, a logged vector takes new items, and the log keeps the old.
function vecClear(v){const a=v.items;if(logged(a)){J.push(v,'items',a);v.items=[];F.add(v.items);}else a.length=0;return null;}
function vecTruncate(v,n){
    n=Number(n);const a=v.items;
    if(n<a.length){if(logged(a)){J.push(v,'items',a);v.items=a.slice(0,n);F.add(v.items);}else a.length=n;}
    return null;
}
function bytesGet(b,i){i=Number(i);return i>=0&&i<b.bytes.length?dsome(BigInt(b.bytes[i])):dnone();}
function bufOf(t){const b={kind:'Buf',text:t.text??t};F.add(b);return b;}
function bufPush(b,text){if(logged(b))J.push(b,'text',b.text);b.text+=text;return null;}
// `replace` of a vector's or a `Buf`'s content: the old content comes out as a value.
function replaceObject(v,w){
    if(v.kind==='Buf'){const old={kind:'Buf',text:v.text};J.push(v,'text',v.text);v.text=w.text;return old;}
    const old=vec(v.items);J.push(v,'items',v.items);v.items=w.items;return old;
}
// A cell is an item of a vector, a reference from the continuation form, or
// one made of a local (`{ref, get, set}`).
class VecCell{constructor(items,index){this.items=items;this.index=index;}get(){return this.items[this.index];}set(v){this.items[this.index]=v;}}
VecCell.prototype.ref=true;
function cellGet(r){return r.get();}
function cellSet(r,v){
    if(r instanceof VecCell){const a=r.items;if(logged(a))J.push(a,r.index,a[r.index]);a[r.index]=v;}
    else{J.push(r,-2,r.get());r.set(v);}
    return null;
}
function cellReplace(r,v){const old=r.get();cellSet(r,v);return old;}
// `borrowed[i]`: 1, the direct form reads the value; 2, it changes the value
// in place, which a host's value (one with `operation`) does not let it do;
// 3, it keeps the reference.
function direct(d,cps,c,args,k,borrowed){
    let budget=false;
    for(let h=c.h;h;h=h.outer)if(h.budget){budget=true;break;}
    for(let i=0;i<args.length;i++)if(borrowed[i]===2&&args[i]?.operation)budget=true;
    if(!budget&&!c.continuationOnly){
        const outer=H,left=c.host.fuel.left,log=[],outerJ=J,outerF=F;
        H=c.host;J=log;F=new WeakSet();
        try{const v=d(...args.map((a,i)=>borrowed[i]===1||borrowed[i]===2?unref(a):a));return more(()=>k(c,v));}
        catch(e){
            // Too deep for the host stack: start again in continuation form.
            if(!(e instanceof RangeError))throw e;
            undo(log);
            c.host.fuel.left=left;
        }finally{H=outer;J=outerJ;F=outerF;}
        return cps({...c,continuationOnly:true},args,(d,v)=>more(()=>k(c,v)));
    }
    return cps(c,args,k);
}
