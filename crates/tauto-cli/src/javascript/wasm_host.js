// The instance owns every address; JavaScript holds checked, instance-local IDs.
export async function bindWasm(bytes) {
    let api, disposed=false, poisoned=false, current=null, nextCallback=1, nextTicket=1;
    const canSuspend=typeof WebAssembly.Suspending==='function'&&typeof WebAssembly.promising==='function';
    const pending=[], promising=new Map();
    const map=(value,f)=>value&&typeof value.then==='function'?value.then(f):f(value);
    const owners=new WeakSet(), callbacks=new Map(), roots=new Map();
    const check=()=>{if(disposed||poisoned)throw new Error('wasm extern instance is unavailable');};
    const write=value=>{
        const bytes=new TextEncoder().encode(JSON.stringify(value));
        api.input_clear();for(const b of bytes)api.input_byte(b);
    };
    const read=()=>{
        const out=new Uint8Array(api.output_len());for(let i=0;i<out.length;i++)out[i]=api.output_byte(i);
        return JSON.parse(new TextDecoder('utf-8',{fatal:true}).decode(out));
    };
    const invoke=(fn,...args)=>{check();try{return fn(...args);}catch(e){poisoned=true;throw e;}};
    const transfer=(fn,params,payload,suspend=false)=>{
        check();const ticket=nextTicket++;write(payload);
        let target=fn;
        if(suspend&&canSuspend){if(!promising.has(fn))promising.set(fn,WebAssembly.promising(fn));target=promising.get(fn);}
        const result=invoke(target,...params,ticket);
        const finish=()=>{api.result_take(ticket);return read();};
        return result&&typeof result.then==='function'?result.then(finish,e=>{poisoned=true;throw e;}):finish();
    };
    const encode=v=>{
        if(v?.wire)return encode(v.wire);
        if(typeof v==='bigint')return {$int:String(v)};
        if(v?.wasmHandle!==undefined||v?.kind==='Opaque'){
            v.invalidate?.();
            if(!owners.has(v))throw new Error('released wasm handle or handle belongs to another instance');
            return {handle:v.wasmHandle??v.handle};
        }
        if(v?.ref)return encode(v.get());
        if(typeof v==='function'){
            const id=nextCallback++,original=v.nib??v;
            original.retain?.();callbacks.set(id,{original,host:v});
            return {callback:id};
        }
        if(Array.isArray(v))return v.map(encode);
        if(v&&typeof v==='object')return Object.fromEntries(Object.entries(v).filter(([,x])=>typeof x!=='function').map(([k,x])=>[k,encode(x)]));
        return v;
    };
    const releaseValue=v=>{
        if(v?.release){v.release();return;}
        if(v?.ref)return;
        if(Array.isArray(v)){v.forEach(releaseValue);return;}
        if(v?.fields)releaseValue(v.fields);
        if(v?.items)releaseValue(v.items);
    };
    const access=(codec,action,value,extra={})=>{
        return map(transfer(api.access,[codec,action],{value:encode(value),...extra},action===3&&current?.suspend),decode);
    };
    let syncing=false;
    const syncRoots=()=>{
        if(syncing||disposed||poisoned)return;
        syncing=true;
        try{
            // A root becomes writable only after every descendant view releases
            // its loan. This includes views returned by a later extern call.
            let changed=true;
            while(changed){changed=false;for(const [id,root] of roots){
                if(!api.root_ready(id))continue;
                roots.delete(id);changed=true;
                const value=decode(transfer(api.access,[root.codec,2],{value:{handle:id}}));
                if(root.ref?.ref){releaseValue(root.ref.get());root.ref.set(value);}
                else releaseValue(value);
            }}
        }finally{syncing=false;}
    };
    const own=(value,id)=>{
        let refs=1;owners.add(value);
        value.retain=()=>{if(refs===0)throw new Error('released wasm handle');refs++;};
        value.release=()=>{if(refs>0&&--refs===0){owners.delete(value);if(!disposed&&!poisoned){api.release(id);syncRoots();}}};
        return value;
    };
    const drain=()=>{
        for(const job of pending)while(job.parent?.closed)job.parent=job.parent.previous;
        const i=pending.findIndex(job=>job.parent===current);
        if(i>=0){const job=pending.splice(i,1)[0];try{job.resolve(job.start());}catch(e){job.reject(e);}}
    };
    const native=fn=>{
        const f=(...args)=>f.invoke(args,null,false,null);f.tautoNative=true;
        f.invoke=(args,adapt,allowSuspend=true,parent=null)=>{
            while(parent?.closed)parent=parent.previous;
            const start=()=>{
                const previous=current,record={adapt,previous,suspend:allowSuspend&&canSuspend};current=record;
                const finish=()=>{record.closed=true;current=previous;drain();};
                try{
                    const result=fn(args);
                    if(result&&typeof result.then==='function')return result.then(v=>{finish();return v;},e=>{finish();throw e;});
                    finish();return result;
                }catch(e){finish();throw e;}
            };
            if(current&&parent!==current&&allowSuspend)return new Promise((resolve,reject)=>pending.push({parent,resolve,reject,start:()=>{try{return start();}catch(e){reject(e);}}}));
            return start();
        };
        return f;
    };
    const decode=v=>{
        if(v?.$int!==undefined)return BigInt(v.$int);
        if(v?.kind==='Opaque'){own(v,v.handle);if(v.clone)v.copy=()=>access(v.codec,7,v);return v;}
        if(v?.kind==='View'){
            const ref={ref:true,wasmHandle:v.handle,resource:true};
            let borrowed,snapshot;
            ref.invalidate=()=>{const old=snapshot;snapshot=undefined;if(old!==undefined)releaseValue(old);};
            ref.cloneOwned=()=>access(v.codec,7,ref);
            ref.operation=(operation,args)=>operation==='replace'?access(v.codec,6,ref,{replacement:encode(args[0])}):access(v.codec,10,ref,{operation,args:encode(args)});
            ref.get=()=>{
                check();if(!owners.has(ref))throw new Error('released wasm view');
                if(v.opaque){
                    if(!borrowed){borrowed={kind:'Opaque',handle:v.handle,resource:true,copy:()=>ref.cloneOwned(),retain:()=>ref.retain(),release:()=>ref.release()};owners.add(borrowed);}
                    return borrowed;
                }
                if(snapshot===undefined)snapshot=access(v.codec,0,ref);
                return snapshot;
            };
            ref.set=x=>{if(!v.mutable)throw new Error('cannot mutate a shared wasm view');access(v.codec,1,ref,{replacement:encode(x)});};
            ref.project=(key,mutable=false)=>access(v.codec,mutable&&v.mutable?5:4,ref,{field:key});
            own(ref,v.handle);
            const release=ref.release;
            ref.release=()=>{release();if(!owners.has(ref)){ref.invalidate();if(borrowed)owners.delete(borrowed);}};
            return ref;
        }
        if(v?.kind==='Function'){
            let f;f=native(args=>access(v.codec,3,f,{args:encode(args)}));
            f.wasmHandle=v.handle;return own(f,v.handle);
        }
        if(Array.isArray(v))return v.map(decode);
        if(v&&typeof v==='object')return Object.fromEntries(Object.entries(v).map(([k,x])=>[k,decode(x)]));
        return v;
    };
    const call=(index,args,owned)=>map(transfer(api.invoke,[index],encode(args),current?.suspend),result=>{
        for(const root of result.roots)roots.set(root.value.handle,{ref:args[root.index],codec:root.codec});
        const value=decode(result.value);
        syncRoots();for(const i of owned)releaseValue(args[i]);
        return value;
    });
    const imports={tauto:{
        callback(id,request){
            const saved=callbacks.get(id);if(!saved)throw new Error('released wasm callback');
            const record=current,args=decode(read());
            const fn=saved.host.nib&&current?.adapt?current.adapt(saved.original,current):saved.host;
            const value=fn(...args);
            const respond=value=>{
                const finish=()=>{check();write(encode(value));api.callback_result(request);};
                if(current!==record)return new Promise((resolve,reject)=>pending.push({parent:record,resolve,reject,start:finish}));
                return finish();
            };
            if(value&&typeof value.then==='function'){
                if(!canSuspend){Promise.resolve(value).catch(()=>{});throw new Error('asynchronous Rust callbacks require WebAssembly.Suspending and WebAssembly.promising');}
                return value.then(respond);
            }
            respond(value);
        },
        callback_drop(id){const saved=callbacks.get(id);callbacks.delete(id);saved?.original.release?.();}
    }};
    if(canSuspend)imports.tauto.callback=new WebAssembly.Suspending(imports.tauto.callback);
    const {instance}=await WebAssembly.instantiate(bytes,imports);api=instance.exports;
    const externs={};
    // BINDINGS
    return {externs,
        release(value){if(!owners.has(value))throw new Error('invalid wasm handle');value.release();},
        dispose(){if(disposed)return;disposed=true;if(!poisoned)api.dispose();for(const {original} of callbacks.values())original.release?.();callbacks.clear();roots.clear();api=null;}
    };
}
