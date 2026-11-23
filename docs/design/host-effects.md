# Host effects and permissions

Everything a program asks of its host is an effect from `std/builtin/os.taut`,
visible in rows. Permissions are denied by default and granted by the user at the start of a
run, or when the program is built.

## Effects

| Effects | Resume | Permission |
|---|---|---|
| `stdout`, `stderr`, `stdout_flush`, `stdin` (a line, `None` at end), `stdin_bytes(max)` | direct | – |
| `argv`, `wall_clock` (Unix ms), `monotonic_clock` (ns), `random` (not for secrets), `secure_random` | direct | – |
| `uhost_add`, `uhost_sub`, `uhost_mul`, `uhost_of_u64`, `host_width`, `hash_seed` ([`uhost`](#uhost)) | direct | – |
| `exit(code)`, `stop(message)` | 0 | – |
| `sleep(ms)`, `wait(signal)` | 1 | – |
| `timer(deadline)`, `shutdown_token()` | direct | – |
| `fs_read*`, `fs_list_dir`, `fs_stat`, `fs_canonicalize` | direct | `read` |
| `fs_write*`, `fs_create_dir`, `fs_remove` (recursive) | direct | `write` |
| `fs_rename`, `fs_copy` | direct | `write` on both / `read` src, `write` dst |
| `fs_read_link`, `fs_write_new`, `fs_read_under`, `fs_temp_dir` | direct | see [Files](#files) |
| `proc_run`, `proc_spawn` (then `proc_read`, `proc_write`, `proc_wait`, …) | direct / 1 | `run` |
| `env(name)` | direct | `env` |
| `permission(kind, target)` | direct | – |
| `net(request)`, `net_addr`, `net_resolve`, `net_open` (then `net_write`, `net_finish`, `net_read`, …), `tcp_*`, `tls_*` | 1 | `net` |

- `IoError` is `Denied` (not granted), `Failed` (the host tried and failed) or
  `TimedOut`.
- Bodies are `Bytes`; `Text::of_bytes` checks UTF-8. `print`, `read_file` and
  `http_get` are ordinary functions over these effects.
- `secure_random` reaches nothing, so it needs no permission, but it is its own
  effect so rows show it and tests can stub it. `Secret` has no `Show` or `Eq`
  ([`secret.md`](secret.md)).
- Effects that resume once let the host run other tasks while waiting.

## `uhost`

`uhost` is the unsigned integer of the word of the machine the program runs
on, for sizes and indices. Its operations are host effects, so a handler may
answer them:

- `a + b`, `a - b` and `a * b` of two `uhost`s are `perform uhost_add(a, b)`,
  `uhost_sub` and `uhost_mul`, and a function that uses them has the effect in
  its row. `uhost_of_u64(x)` converts a `u64`.
- The host computes in the word of its target: 32 bits on JavaScript, 64 bits
  elsewhere (Rust, LLVM, the virtual machine and niri). A result that
  does not fit, such as `1 - 2`, ends the run, and the effect is not resumed.
  Where no `handle` answers the effect, a backend writes one checked machine
  operation instead of a perform.
- `host_width()` answers `W32` or `W64`, so `checked_*` functions can tell
  where the host would stop and answer `None` instead.
- `hash_seed()` answers the seed of the hash maps that leave their order to the
  host: a random seed that is the same for the whole run and new for the next.
  A program that wants one order handles it with a seed of its own.

A function whose row has no `uhost_*`, `host_width` or `hash_seed` gives the
same result on every target.

## Who answers

Standard effects are `pub(open)`, so programs may `handle` them; tests stub
files and network this way. The host answers, and checks permissions, only
when an effect reaches top level. Effects of tasks are always answered by the
host ([`nib.md`](nib.md)「Tasks」).

What a handler answers can be stated in theorems: a file that imports
`std::os` has the standard effects whose types the kernel has read in proofs
([`effect-proofs.md`](effect-proofs.md)「Effects and rows」).

The host is the outermost handler. Nothing is written around the program for
it: the lowering puts the host's handler outside the top level and outside the
body of each task, so a standard effect that no `handle` of the program answers
reaches it, and its direct arms answer where it is performed. The arms are the
handler in the prelude's `Host::run`, which nothing calls; they call the `Os::`
externs, which programs may not call directly, since that would skip handlers
and the permission check: they and the `Host::` functions are not `pub`
([`visibility.md`](visibility.md)). A program that performs `main` or `test`
still has its top level put in `Entry::run(() => { … })`, which finds the
entries and calls their bodies.

### Slow answers

The host's handler passes `wait` to the host. Arms for `sleep`, `net`, waiting `tcp_*`
and `tls_*` start the work and wait on its signal, and the host answers `wait`
where it runs the top level and each task body, blocking only that task. On the
Rust reactor the task yields ([`rust-backend.md`](rust-backend.md)
「Tasks (`spawn`)」); with threads, or without `spawn`, work completes in place;
on JavaScript `wait` is a Promise; on the virtual machine waiting on a signal
nobody raises is a deadlock.

## Network

HTTP servers are not effects: listening, parsing, framing, limits and deadlines
are Tauto libraries over `tcp_*`, so programs can stream, tune limits and prove
the parser.

- `net_resolve(host)` returns addresses; permission reads the name as
  `http://host/`. `net_addr(request, address)` connects to an already-checked
  address without resolving again (against DNS rebinding), and permission
  checks both the URL and the address.
- `tcp_*` covers TCP and Unix sockets (`HOST:PORT`, `unix:PATH`). Every waiting
  call takes a monotonic deadline, so silent peers cannot hang a program.
  `tcp_shutdown`, `tcp_close` and `tcp_unlisten` wake pending operations.
  Permission is checked at `tcp_listen` and `tcp_connect`. `tauto dev` keeps
  listeners across restarts.
- `TcpListener`, `TcpStream` and `TlsStream` are affine and cannot be built
  outside `os.taut`. `tcp_accept`, `tcp_read`, `tcp_write`, `tls_read` and
  `tls_write` take the handle and give it back in their answer
  (`TcpRead { stream, got }`, …), so a use after close is a type error.
  Stopping is a separate shared value: `TcpStream::stopper(&s)`,
  `TcpListener::stopper(&l)` and `TlsStream::stopper(&t)` give a
  `TcpStopper`, `ListenStopper` or `TlsStopper`, which `tcp_shutdown`,
  `tcp_unlisten` and `tls_shutdown` take, so one task can wake another's read.
  What `spawn` runs is shared, so a handle reaches a task through a `Mutex`.

### Streaming HTTP

`net_open(head, address)` starts a request and gives an affine `RequestBody`.
`net_write` sends a piece of it, and `net_finish` ends it and waits for the
response head: `Responded(Opened { head, body })` with an affine
`ResponseBody`, `Unanswered(body)` when the deadline passes (finish again to
wait again, or `net_cancel`), or `NoResponse(error)`. `net_read(body, max,
deadline)` gives up to `max` bytes as soon as they arrive, empty at the end,
and `net_close` drops the response. Each call gives the body back in its
answer (`Written`, `Piece`), so a body is never used after it is closed, and a
cancelled request is never sent as complete. `std/sse.taut` decodes server-sent
events from such pieces, proved to give the same events wherever the stream is
cut. Permission is checked as for `net` at `net_open`.

### TLS

`tls_accept`, `tls_connect`, `tls_read`, `tls_write`, `tls_shutdown` and
`tls_close` layer TLS over a `tcp_*` stream, terminated by the host (rustls).
Servers configure certificates by SNI, ALPN and optional client roots; clients
configure the server name, roots and client certificate. Verification cannot be
disabled; pass a self-signed CA as the only root. A connection ending without
close_notify is `Failed`. No new permission is needed. A Tauto TLS library can
answer the same effects with `handle`.

## Permissions

```
tauto run main.taut -- ARGS…
```

Tauto knows before a run every standard effect that reaches the top level
unanswered: the rows say so. So `tauto run` and `tauto dev` take no flags
that grant permissions. At the start they show the kinds those effects need
and ask once:

```
main.taut needs these permissions to run (+ marks one not allowed before):
  + net: reach the network
  + read: read files
Allow? [a] from now on / [y] this time only / [N] do not run:
```

- The kinds are `read`, `write`, `env`, `net`, `run` (starting a program),
  `clipboard` (reading it; writing is always allowed) and `div` (the top
  level may not stop: the host's step limit is lifted). `--steps N` keeps a
  limit and does not ask for `div`.
- **From now on** is kept under `~/.tauto/allowed/` (or `$TAUTO_HOME`), one
  file per program, named by a hash of its absolute path (the file, or the
  tote's folder), holding the kinds allowed. A later run is not asked while
  what it needs is among them; when it needs more it is asked again with the
  new kinds marked `+`. **This time only** keeps nothing (`tauto dev` keeps
  it until it exits). Anything else, an empty line included, runs nothing.
- **Without a terminal** (CI, a pipe, an editor's process) the run does not
  start and says so. `--yes` allows what would be asked, for that run only,
  and keeps nothing: a script that passes it has reviewed what it runs.
  `div` alone does not stop it: it reaches nothing outside the program, so
  the run keeps the step limit, as before anything was asked.
- **Narrowed grants.** A project narrows a kind to paths, names or hosts in
  `trust.run` of its `Tauto.eure`; a kind written there is granted as
  written and not asked at the start:

  ```eure
  trust {
    run {
      read = ["data"]
      net = ["api.example.com", "localhost:8080"]
    }
  }
  ```

  `true` grants the whole kind, except for `env`, `net` and `all`, which
  always list what they grant. `interactive = true` asks the user at the
  terminal when the program reaches what nothing grants, instead of at the
  start (once, always for the rest of the run, or not). Relative paths are
  taken from the project's folder. It is approved with the rest of `trust`
  (below).
- **Safe defaults.** What is allowed at the start (asked, or `--yes`) is
  narrow: `read` and `write` under the folder the run starts in, and `env`
  and `net` not at all, since a variable or a host is named in `trust.run`.
  A run that needs `env` or `net` without such a list does not start and
  says where to write it.
- **Fixed in the program.** `tauto build` asks (or takes `--yes`) as a run
  does, and the binary or `main.mjs` it makes carries what was allowed: it
  reads no `--allow-*` of its own and gives its whole command line to the
  program, so one file runs as it was built. `tauto run` builds the same way
  and passes only the arguments after `--`.
  `tauto build` also takes `--allow-*` flags, which are fixed in the output
  as given (a tool that builds a program for its own use, as the selfhost
  harness does, says so there); `run` takes none.
- Paths are resolved like the OS resolves them (following links), and the host
  uses the resolved path. `env` grants exact names. `net` grants hosts parsed by
  the client's own URL parser (`host` for all ports, `host:port` for one), for
  `http` and `https` only, without following redirects. Requests outside a
  narrowed grant get `Denied`.
- **Trust approval.** `tauto run`, `dev`, `build` and a tote command
  (`tauto NAME`) compare the project's `trust` section with the last
  approved one and ask for approval of the difference. `--approve-trust`
  approves non-interactively (before NAME for a command). Every project a
  path argument lies in is asked about, not only the first.
- **Powerbox.** A path the user picks in a host file dialog grants access to
  that file or folder, resolved at choice time.
- Tote commands use `trust.commands` instead
  ([`commands.md`](commands.md)「Permissions」).
- `permission(kind, target)` runs the host's own check and returns the
  resolved target or `None`, revealing only what trying would. Programs that
  answer other programs' effects (VMs) use it to return `Denied`.

## Origins

Each standard effect that reaches the top level comes with the set of
functions it comes from (`RowReport::host_origins`), and a run is asked for
each kind once per function, `kind(origin)`:

```
app needs these permissions to run (+ marks one not allowed before):
    read(app::file_loader::load): read files
  + write(app::persistent::file): write files
  + write(time::datetime::get_day): write files
```

A reader sees which tote asks for what: a date library that writes files
stands out, and a dependency's update that starts writing is asked about.

- The origin of one `perform` is the function that holds it as written; a
  lambda's is the named function around it, the top level's is its module.
  A function of the standard library is the origin of nothing: the function
  outside it that calls into it is. So an origin is fixed where it is
  written, and a callback passed through a row variable keeps its own.
- A call of a function of the program brings that function's origins. An
  arm that answers an effect completely takes away what its body brings of
  it, and a lambda given to a call brings only what the call's row still
  has (a callee may answer it). What an arm performs comes from the
  function that holds the arm.
- Origins are not part of a row's meaning: a written row names effects
  only, and whether one row contains another reads effects only.
- An effect a row cannot follow (`?…`) is an error, so a program that runs
  has every origin known before it starts.
- A key of `trust.run` names the origins it grants to: `"write(app::*)"`
  (the functions of `app` and its modules), `"write(app::store::save)"`
  (one function), `"write(*)"` or `write` (every origin). An origin no key
  covers is asked about at the start. A kind kept alone under
  `~/.tauto/allowed/` (from before origins) covers every origin.

  ```eure
  trust {
    run {
      "read(app::*)" = ["data"]
      "write(app::persistent::*)" = ["out"]
    }
  }
  ```

  Until the host tells targets apart by origin, the lists of a kind's keys
  are joined: each origin granted the kind may reach each of its targets.

## Backends

- **VM:** permissions come from the CLI's question at the start.
  `tauto run --backend rust|javascript` asks the same question and fixes
  what was allowed in the program it builds.
- **Rust:** a built binary carries the permissions it was built with and
  reads no `--allow-*` flags (whoever starts it cannot widen what it may do);
  embedders call `tauto_rt::run_embedded(permissions, args, run)`, which denies by default,
  runs one program per process at a time, and restores all settings afterwards.
  Checked requests go to the process's `Host` (`System`, or `Absent` on
  `wasm32-unknown-unknown`, replaceable with `tauto_rt::host::set`); a `Host`
  never sees denied requests.
- **JavaScript:** `run(show, externs, options)` with `options.permissions` and
  `options.os_*` host functions; the node entry (`main.mjs`) carries the
  permissions it was built with and reads no `--allow-*` flags.

## Dependency externs

Externs run host code invisible to rows, so `--allow-*` cannot cover them. A
dependency tote declaring `extern` is rejected at load unless the entry tote
names it in `trust { extern = ["regex"] }`. Externs are callable only inside
their tote, checked after macro expansion so macros cannot smuggle calls out;
totes export wrapper functions instead.

## Standard I/O

`stdin` and `stdin_bytes` share one buffer and can be mixed (headers by line,
bodies by bytes). `stdin_bytes(0)` returns empty without meaning end of input.

## Shutdown

`shutdown_token()` returns a [cancellation](#cooperative-cancellation) token
requested by SIGINT or SIGTERM. Once a program has asked for it, the first
signal does not terminate the program, which cleans up and returns normally; a
second one exits at once (`128 + n`). Programs that never ask exit on the first
signal. The signal handler only sets a flag, and its unsafe code lives in
`tauto-rt-signal`.

## Files

- `fs_stat` returns kind, size and modification time, or `None`; it follows
  links, like permission checks.
- `fs_rename` replaces `dst`; `fs_copy` copies files only.
- `fs_read_link` and `fs_write_new` act on the entry itself, not its target;
  `fs_write_new` creates only where nothing exists, including dangling links.
- `fs_read_under(root, path)` reads inside untrusted directories: `path` has
  only plain names, no component may be a link, and each component opens from
  its parent's descriptor, so concurrent renames cannot escape. Only `root` is
  checked.
- `fs_temp_dir()` creates a fresh directory and grants access under it for the
  run. It does not stand in for `read` or `write`: a program that also reads or
  writes elsewhere is asked for them like any other.
- There is no `chdir` or `set_var`: process-wide state would affect concurrent
  tasks and break check-then-use. Use `permission("read", ".")`,
  `Process::dir` and `Process::env`.

## Processes

`proc_run(p)` runs a program with arguments,
directory, added environment and stdin, and returns its status, stdout and
stderr. `--allow-run=git,clang` matches the program's spelling exactly. A child
runs outside Tauto's permissions with the user's full authority, so `run` is the
strongest grant. `tauto` names the running `tauto` itself. A bare program name is
searched for on the run's own `PATH`, the same on every backend and whatever
`Process::env` holds (which the child gets exactly as given, `PATH` or not); a
name with a directory in it is used as spelled, and a name nothing answers
is refused by the system. `proc_spawn` starts a
child with piped or inherited streams, read and written with deadlines; closing
the handle kills the child.

## `div`

Outside `budget`, `div` runs under a host step limit (ten million by default)
that catches accidental infinite loops. Programs that loop on purpose already
have `div` in their rows, so `tauto run` asks for `div` at the start, and
allowing it removes the limit (a built binary carries what `tauto build`
was allowed). `tauto dev` and
tote commands are always unlimited; `TAUTO_STEP_LIMIT` sets the limit for Rust
binaries. `budget` is unaffected.

## `budget`

`perform budget(n, f)` and `perform budget_memory(n, f)` are answered by the
host that runs the program, where they are performed: the top level, a task and
a handler's arm alike. No program's `handle` has an arm for them, as none has
one for `wait`. They ask for no permission, since counting reaches nothing
outside the program, and they are not among the effects the host's handler answers:
every backend has the count built in
([`semantics.md`](semantics.md)「The effect `budget`」).

## Cooperative cancellation

In `std::builtin::par`, `Cancellation` is the authority to request and
`CancelToken` the authority to observe; tokens cannot recover the source.
`Signal::either` combines readiness and cancellation signals without consuming
them. A request stops and rolls back nothing: code checks its token where it
chooses, releases resources and returns normally, and owners confirm completion
with `Task::join`.

## Undecided

- `tauto test` grants no permissions; tests stub with handlers.
