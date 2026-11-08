import { readFileSync, writeFileSync, mkdirSync, readSync, realpathSync, lstatSync, readlinkSync, readdirSync, rmSync, mkdtempSync, statSync, renameSync, copyFileSync, openSync, closeSync, fstatSync, constants as fsConstants } from 'node:fs';
import { dirname, join } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync, spawn as spawnChild } from 'node:child_process';
import { request as httpRequest } from 'node:http';
import { request as httpsRequest } from 'node:https';
import { isIP, createServer as createNetServer, createConnection } from 'node:net';
import { lookup } from 'node:dns/promises';
const permissions = {};
let rest = process.argv.slice(2);
while (rest.length > 0) {
  const a = rest[0];
  if (a === '--') { rest = rest.slice(1); break; }
  if (a === '--allow-all' || a === '-A') { for (const k of ['read','write','env','net','run','div']) permissions[k] = true; rest = rest.slice(1); continue; }
  if (a === '--allow-div') { permissions.div = true; rest = rest.slice(1); continue; }
  const m = /^--allow-(read|write|env|net|run)(?:=(.*))?$/.exec(a);
  if (!m) { if (a.startsWith('--allow-')) { console.error(`unknown permission \`${a}\`: the permissions are --allow-read, --allow-write, --allow-env, --allow-net, --allow-run, --allow-div and --allow-all`); process.exit(2); } break; }
  if (m[2] === undefined) permissions[m[1]] = true;
  else {
    const items = m[2].split(',').filter(s => s !== '');
    if (items.length === 0) { console.error(`\`${a}\` names nothing; write --allow-${m[1]} for all`); process.exit(2); }
    if (permissions[m[1]] !== true) permissions[m[1]] = [...(permissions[m[1]] ?? []), ...items];
  }
  rest = rest.slice(1);
}
const realPath = p => {
  // As the system resolves it: each part in turn, a link followed before a
  // `..` after it; past what exists only plain names (`docs/design/host-effects.md`).
  const whole = p.startsWith('/') ? p : process.cwd() + '/' + p;
  let at = realpathSync('/'), missing = false;
  for (const part of whole.split('/')) {
    if (part === '' || part === '.') { if (missing && part === '.') return null; continue; }
    if (part === '..') { if (missing) return null; at = dirname(at); continue; }
    const next = join(at, part);
    if (missing) { at = next; continue; }
    try { at = realpathSync(next); } catch (e) {
      try { lstatSync(next); return null; } catch (e2) { missing = true; at = next; }
    }
  }
  return at;
};
let stdinBuffer = Buffer.alloc(0), stdinDone = false;
const readStdin = max => {
  if (stdinBuffer.length === 0 && !stdinDone) {
    const chunk = Buffer.alloc(65536); let n = 0;
    for (;;) {
      try { n = readSync(0, chunk, 0, chunk.length, null); break; } catch (e) { if (e.code === 'EAGAIN') continue; if (e.code !== 'EOF') stdinDone = true; break; }
    }
    if (n === 0) stdinDone = true; else stdinBuffer = Buffer.concat([stdinBuffer, chunk.subarray(0, n)]);
  }
  const out = stdinBuffer.subarray(0, Math.min(max, stdinBuffer.length)); stdinBuffer = stdinBuffer.subarray(out.length);
  return new Uint8Array(out);
};
const readLine = () => {
  for (;;) {
    const i = stdinBuffer.indexOf(10);
    if (i >= 0) { const line = stdinBuffer.subarray(0, i).toString('utf8').replace(/\r$/, ''); stdinBuffer = stdinBuffer.subarray(i + 1); return line; }
    if (stdinDone) { if (stdinBuffer.length === 0) return null; const line = stdinBuffer.toString('utf8'); stdinBuffer = Buffer.alloc(0); return line; }
    const chunk = Buffer.alloc(65536); let n = 0;
    try { n = readSync(0, chunk, 0, chunk.length, null); } catch (e) { if (e.code === 'EAGAIN') continue; if (e.code !== 'EOF') { stdinDone = true; continue; } }
    if (n === 0) stdinDone = true; else stdinBuffer = Buffer.concat([stdinBuffer, chunk.subarray(0, n)]);
  }
};
// `net_resolve`: the addresses the system resolves a host name to.
const resolveHost = host => lookup(host, { all: true, verbatim: true }).then(as => as.map(a => a.address));
// `net_addr`: a request connected to `address` without resolving the URL's host
// again; the Host header and the TLS name stay the URL's host.
const fetchAt = (url, init, address) => new Promise((resolve, reject) => {
  const u = new URL(url), ip = address.replace(/^\[|\]$/g, ''), family = isIP(ip);
  if (!family) { reject(new Error('not an IP address: ' + address)); return; }
  const send = u.protocol === 'https:' ? httpsRequest : httpRequest;
  const req = send(u, { method: init.method, headers: Object.fromEntries(init.headers), lookup: (_h, o, cb) => o && o.all ? cb(null, [{ address: ip, family }]) : cb(null, ip, family) }, res => {
    const chunks = [];
    res.on('data', c => chunks.push(c));
    res.on('end', () => {
      const items = [String(res.statusCode)];
      for (let i = 0; i + 1 < res.rawHeaders.length; i += 2) items.push(res.rawHeaders[i].toLowerCase(), res.rawHeaders[i + 1]);
      resolve([items, new Uint8Array(Buffer.concat(chunks))]);
    });
    res.on('error', reject);
  });
  req.on('error', reject);
  if (init.body !== undefined) req.write(init.body);
  req.end();
});
// Byte streams of `--allow-net` (`tcp_*`): each stream buffers what arrives
// until the program reads it. A deadline is nanoseconds of `monotonic_clock`.
const tcpListeners = new Map(), tcpStreams = new Map();
let nextTcp = 0;
const untilDeadline = d => d === null ? null : Math.max(0, Number(d) / 1e6 - performance.now());
const socketAddress = a => a.unix !== undefined ? { path: a.unix } : { host: a.host.replace(/^\[|\]$/g, ''), port: a.port };
const parseAddress = t => t.startsWith('unix:') ? { unix: t.slice(5) } : (m => m && { host: m[1], port: Number(m[2]) })(/^(.*):([0-9]+)$/.exec(t));
const shown = (socket, side) => {
  const a = side === 'local' ? socket.localAddress : socket.remoteAddress, p = side === 'local' ? socket.localPort : socket.remotePort;
  if (a === undefined) return 'unix:';
  return a.includes(':') ? `[${a}]:${p}` : `${a}:${p}`;
};
const addTcp = (socket, local, peer) => {
  const s = { socket, chunks: [], ended: false, error: null, wake: [] };
  const wake = () => { const w = s.wake; s.wake = []; for (const f of w) f(); };
  socket.on('data', c => { s.chunks.push(c); wake(); });
  socket.on('end', () => { s.ended = true; wake(); });
  socket.on('close', () => { s.ended = true; wake(); });
  socket.on('error', e => { s.error = e; wake(); });
  socket.setNoDelay(true);
  const id = nextTcp++;
  tcpStreams.set(id, s);
  return [String(id), local, peer];
};
// Waits for `ready` to hold, for a wake, or for the deadline: true when ready.
const waitFor = (wakes, ready, deadline) => new Promise(resolve => {
  if (ready()) return resolve(true);
  const ms = untilDeadline(deadline);
  if (ms === 0) return resolve(false);
  let timer = null;
  const on = () => { if (ready()) { if (timer) clearTimeout(timer); resolve(true); } else wakes.push(on); };
  wakes.push(on);
  if (ms !== null) timer = setTimeout(() => resolve(ready()), ms);
});
const children = new Map(); let nextChild = 1;
const childOf = id => { const s = children.get(id); if (!s) throw new Error('no such program'); return s; };
const childSpawn = (program, args, dir, env, stdin, modes) => new Promise((resolve, reject) => {
  const p = spawnChild(program, args, { cwd: dir === '' ? undefined : dir, env: { ...process.env, ...Object.fromEntries(env) }, stdio: modes.map(m => m === 1 ? 'inherit' : 'pipe'), detached: true });
  const s = { p, done: false, code: null, wake: [], pipes: [null, null, null] };
  const wake = () => { for (const f of s.wake.splice(0)) f(); };
  const pipe = (stream, i) => { if (!stream) return; const q = { chunks: [], ended: false }; s.pipes[i] = q; stream.on('data', c => { q.chunks.push(c); wake(); }); stream.on('end', () => { q.ended = true; wake(); }); stream.on('close', () => { q.ended = true; wake(); }); stream.on('error', () => { q.ended = true; wake(); }); };
  pipe(p.stdout, 1); pipe(p.stderr, 2);
  p.stdin?.on('error', () => {});
  p.once('error', reject);
  p.once('close', code => { s.done = true; s.code = code; wake(); });
  p.once('spawn', () => {
    if (p.stdin && stdin.length > 0) p.stdin.write(stdin);
    const id = nextChild++; children.set(id, s); resolve([String(id)]);
  });
});
const childRead = async (id, which, max, deadline) => {
  const s = childOf(id); const q = s.pipes[which === 2 ? 2 : 1];
  if (!q || max === 0) return new Uint8Array(0);
  if (!await waitFor(s.wake, () => q.chunks.length > 0 || q.ended, deadline)) return null;
  if (q.chunks.length === 0) return new Uint8Array(0);
  const c = q.chunks[0];
  if (c.length <= max) { q.chunks.shift(); return new Uint8Array(c); }
  q.chunks[0] = c.subarray(max);
  return new Uint8Array(c.subarray(0, max));
};
const childWrite = (id, bytes) => new Promise((resolve, reject) => {
  const s = childOf(id);
  if (!s.p.stdin || s.p.stdin.destroyed || s.p.stdin.writableEnded) return reject(new Error('the standard input is closed'));
  s.p.stdin.write(bytes, e => e ? reject(e) : resolve());
});
const childCloseStdin = id => { const s = childOf(id); if (s.p.stdin) s.p.stdin.end(); };
const childWait = async (id, deadline) => {
  const s = childOf(id);
  if (!await waitFor(s.wake, () => s.done, deadline)) return null;
  return s.code === null ? [] : [s.code];
};
const childClose = id => { const s = children.get(id); if (!s) return; children.delete(id); if (!s.done) { try { process.kill(-s.p.pid, 'SIGKILL'); } catch { s.p.kill('SIGKILL'); } } };
const tcpListen = address => new Promise((resolve, reject) => {
  const a = parseAddress(address);
  if (!a) return reject(new Error(`cannot listen on ${address}`));
  const l = { queue: [], wake: [], closed: false };
  const server = createNetServer(c => { l.queue.push(c); const w = l.wake; l.wake = []; for (const f of w) f(); });
  l.server = server;
  server.once('error', reject);
  server.listen(socketAddress(a), () => {
    const id = nextTcp++;
    tcpListeners.set(id, l);
    const b = server.address();
    resolve([String(id), typeof b === 'string' ? `unix:${b}` : b.family === 'IPv6' ? `[${b.address}]:${b.port}` : `${b.address}:${b.port}`]);
  });
});
const tcpAccept = async (id, deadline) => {
  const l = tcpListeners.get(id);
  if (!l) throw new Error(`no listener ${id}`);
  if (!await waitFor(l.wake, () => l.queue.length > 0 || l.closed, deadline)) return null;
  if (l.closed) throw new Error('the listener was closed');
  const c = l.queue.shift();
  return addTcp(c, c.localAddress === undefined ? 'unix:' : shown(c, 'local'), shown(c, 'peer'));
};
const tcpConnect = (address, deadline) => new Promise((resolve, reject) => {
  const a = parseAddress(address);
  if (!a) return reject(new Error(`cannot connect to ${address}`));
  const c = createConnection(socketAddress(a));
  const ms = untilDeadline(deadline);
  const timer = ms === null ? null : setTimeout(() => { c.destroy(); resolve(null); }, ms);
  c.once('error', e => { if (timer) clearTimeout(timer); reject(e); });
  c.once('connect', () => {
    if (timer) clearTimeout(timer);
    resolve(addTcp(c, a.unix !== undefined ? 'unix:' : shown(c, 'local'), a.unix !== undefined ? address : shown(c, 'peer')));
  });
});
const tcpStream = id => { const s = tcpStreams.get(id); if (!s) throw new Error(`no stream ${id}`); return s; };
const tcpRead = async (id, max, deadline) => {
  const s = tcpStream(id);
  if (max === 0) return new Uint8Array(0);
  if (!await waitFor(s.wake, () => s.chunks.length > 0 || s.ended || s.error, deadline)) return null;
  if (s.chunks.length === 0) { if (s.error && !s.ended) throw s.error; return new Uint8Array(0); }
  const c = s.chunks[0];
  if (c.length <= max) { s.chunks.shift(); return new Uint8Array(c); }
  s.chunks[0] = c.subarray(max);
  return new Uint8Array(c.subarray(0, max));
};
const tcpWrite = (id, bytes, deadline) => new Promise((resolve, reject) => {
  const s = tcpStream(id);
  const ms = untilDeadline(deadline);
  const timer = ms === null ? null : setTimeout(() => resolve(null), ms);
  s.socket.write(bytes, e => { if (timer) clearTimeout(timer); if (e) reject(e); else resolve(true); });
});
const tcpShutdown = (id, how) => {
  const s = tcpStream(id);
  if (how !== 1) { s.ended = true; s.chunks = []; s.socket.pause(); const w = s.wake; s.wake = []; for (const f of w) f(); }
  if (how !== 0) return new Promise(resolve => s.socket.end(resolve));
};
const tcpClose = id => {
  const s = tcpStreams.get(id);
  if (!s) return;
  tcpStreams.delete(id);
  s.ended = true; s.socket.destroy(); const w = s.wake; s.wake = []; for (const f of w) f();
};
const tcpUnlisten = id => {
  const l = tcpListeners.get(id);
  if (!l) return;
  tcpListeners.delete(id);
  l.closed = true; l.server.close(); const w = l.wake; l.wake = []; for (const f of w) f();
};
// A request to end the run (SIGINT, SIGTERM) raises the tokens the program
// asked for; a second one ends the process as the signal would. While a token
// waits, a timer keeps Node from ending the run as a deadlock.
const shutdownWaiters = [];
let shutdownFired = false, shutdownKeep = null;
const onShutdownSignal = name => {
  if (shutdownFired) process.exit(128 + (name === 'SIGINT' ? 2 : 15));
  shutdownFired = true;
  if (shutdownKeep) { clearInterval(shutdownKeep); shutdownKeep = null; }
  for (const f of shutdownWaiters.splice(0)) f();
};
const onShutdown = raise => {
  if (shutdownFired) { raise(); return; }
  if (!shutdownWaiters.length && !shutdownKeep) {
    process.on('SIGINT', onShutdownSignal);
    process.on('SIGTERM', onShutdownSignal);
    shutdownKeep = setInterval(() => {}, 1 << 30);
  }
  shutdownWaiters.push(raise);
};
const closeServers = () => { if (shutdownKeep) { clearInterval(shutdownKeep); shutdownKeep = null; } for (const id of [...tcpStreams.keys()]) tcpClose(id); for (const id of [...tcpListeners.keys()]) tcpUnlisten(id); };
// `fs_read_under`: node has no `openat`, so each directory on the way is
// checked with `lstat` and the file is opened with `O_NOFOLLOW`. A directory
// swapped for a link between the check and the open is not caught, as it is
// by the descriptors of the other hosts.
function readUnder(root,path){
  const parts=path.split('/');
  if(path.includes('\0')||parts.some(p=>p===''||p==='.'||p==='..'))throw new Error(path+': not a path of names under the root (empty, absolute, `.` or `..`)');
  if(fsConstants.O_NOFOLLOW===undefined)throw new Error('fs_read_under: this system cannot open a path without following links');
  if(!statSync(root).isDirectory())throw new Error(root+': not a directory');
  let at=root;
  for(let i=0;i+1<parts.length;i++){at=join(at,parts[i]);const st=lstatSync(at);if(!st.isDirectory())throw new Error(path+': '+(st.isSymbolicLink()?'a link':'not a directory'));}
  const fd=openSync(join(root,...parts),fsConstants.O_RDONLY|fsConstants.O_NOFOLLOW|(fsConstants.O_NONBLOCK??0));
  try{if(!fstatSync(fd).isFile())throw new Error(path+': not a file');return readFileSync(fd);}finally{closeSync(fd);}
}
const options = {args:rest,os_on_shutdown:onShutdown,os_resolve:resolveHost,os_fetch_at:fetchAt,os_tcp_listen:tcpListen,os_tcp_accept:tcpAccept,os_tcp_connect:tcpConnect,os_tcp_read:tcpRead,os_tcp_write:tcpWrite,os_tcp_shutdown:tcpShutdown,os_tcp_close:tcpClose,os_tcp_unlisten:tcpUnlisten,permissions,env:process.env,cwd:process.cwd(),resolvePath:realPath,os_read_line:readLine,os_child_spawn:childSpawn,os_child_read:childRead,os_child_write:childWrite,os_child_close_stdin:childCloseStdin,os_child_wait:childWait,os_child_close:childClose,os_read_stdin:readStdin,os_flush:()=>{},os_print:s=>process.stdout.write(s),os_eprint:s=>process.stderr.write(s),os_read_file:p=>readFileSync(p,'utf8'),os_write_file:(p,s)=>writeFileSync(p,s),os_read_bytes:p=>new Uint8Array(readFileSync(p)),os_write_bytes:(p,b)=>writeFileSync(p,b),os_read_under:(r,p)=>new TextDecoder('utf-8',{fatal:true}).decode(readUnder(r,p)),os_read_bytes_under:(r,p)=>new Uint8Array(readUnder(r,p)),os_create_dir:p=>{mkdirSync(p,{recursive:true});},os_list_dir:p=>readdirSync(p),os_remove:p=>{if(!lstatSync(p))return;rmSync(p,{recursive:true});},os_stat:p=>{let st;try{st=statSync(p);}catch(e){if(e&&e.code==='ENOENT')return null;throw e;}return {kind:st.isDirectory()?'dir':st.isFile()?'file':'other',size:st.size,modified_ms:Math.max(0,Math.trunc(st.mtimeMs))};},os_read_link:p=>{let st;try{st=lstatSync(p);}catch(e){if(e&&e.code==='ENOENT')return null;throw e;}return st.isSymbolicLink()?readlinkSync(p):null;},os_write_new:(p,s)=>writeFileSync(p,s,{flag:'wx'}),os_move_path:(a,b)=>renameSync(a,b),os_copy_file:(a,b)=>copyFileSync(a,b),os_canonicalize:p=>realpathSync(p),os_temp_dir:()=>mkdtempSync(join(tmpdir(),'tauto-')),os_run:(program,args,dir,env,stdin)=>{const r=spawnSync(program,args,{cwd:dir===''?undefined:dir,env:{...process.env,...Object.fromEntries(env)},input:stdin,maxBuffer:1<<30});if(r.error)throw r.error;return {status:r.status,stdout:new Uint8Array(r.stdout),stderr:r.stderr.toString('utf8')};}};

// A suspended program cannot resume once Node has no remaining host work.
const runUntilIdle = async promise => {
  let idle;
  const stopped = new Promise((_, reject) => {
    idle = () => reject(new Error('deadlock: no host work can resume the program'));
    process.once('beforeExit', idle);
  });
  try { return await Promise.race([promise, stopped]); }
  finally { process.removeListener('beforeExit', idle); }
};
