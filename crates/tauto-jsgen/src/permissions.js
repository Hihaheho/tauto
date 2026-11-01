// What a run may ask of the host (`docs/design/host-effects.md`):
// `options.permissions` is `{read, write, env, net, run}`, each `true` (all) or a
// list of what it covers; a kind left out is denied.
function permissionGrant(options,kind){
    const g=options.permissions?.[kind];
    if(g===true)return true;
    if(Array.isArray(g)&&g.length>0)return g.map(String);
    return null;
}
function missingPermissions(options,needs){return [...new Set(needs)].filter(kind=>permissionGrant(options,kind)===null);}
function missingMessage(missing){return 'the program needs '+missing.map(k=>'--allow-'+k).join(' ')+' to run; the host denies it by default';}
// A path as the system resolves it, `null` when it cannot be checked: the
// host's `options.resolvePath` follows links in order; without one there are
// no links, and the path is made absolute against `options.cwd`.
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
