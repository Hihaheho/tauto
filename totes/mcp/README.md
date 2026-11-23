# mcp

A Model Context Protocol (MCP) server over standard input and output, written
in Tauto. It gives an AI agent the step-by-step proof commands of `tauto`
(`check`, `goals`, `try`, `suggest`, `library`) as MCP tools, so the agent can read
the goal at a hole, try a term in it and see the checker's verdict, without
scraping terminal text. Each tool runs the `tauto` command of the same name with
`--json` and returns its output; the server decides nothing about proofs itself.

The commands and their output are described in the `tauto` section of the root
`README.md` and, for `suggest`, in `docs/design/lemma-search.md`. The effects the
server uses (`stdin`, `stdout`, `stdout_flush`, `proc_run`) and the `run`
permission they need are those of `docs/design/host-effects.md`. There is no
design document of the server itself. It speaks MCP specification version
`2024-11-05` and JSON-RPC 2.0; the specifications are the reference for the
protocol.

| Source | What it holds |
| --- | --- |
| `src/main.taut` | The loop: read a line from standard input, answer it on standard output |
| `src/jsonrpc.taut` | JSON-RPC 2.0 requests, responses, ids and error codes |
| `src/mcp.taut` | The MCP layer: `initialize`, `ping`, `tools/list`, `tools/call`, and one function per tool |

JSON is read and written by the `json` tote (`totes/json`); the server has no
other dependency (`Tauto.eure` also names `text`).

## Tools

Every tool needs `file`, the path to a `.taut` file, read from the server's
working directory when relative. The server starts `tauto` with that argument list:

| Tool | Arguments | Runs |
| --- | --- | --- |
| `tauto_check` | `file` | `tauto check --json FILE` |
| `tauto_goals` | `file`, `hole` (optional) | `tauto goals --json [--hole NAME] FILE` |
| `tauto_try` | `file`, `hole`, `expr` | `tauto try --json --hole NAME --with EXPR FILE` |
| `tauto_suggest` | `file`, `hole`, `limit` (optional) | `tauto suggest --json --hole NAME [--limit N] FILE` |
| `tauto_library` | `file` | `tauto library --json FILE` |

`hole` is a hole name without the `?`. `tauto_try` checks the file with `expr` in the
hole and does not write it. An empty string counts as a missing argument. A `limit`
that is not a number is ignored. A `tools/call` request must carry `arguments`, even
an empty object.

The result is `{"content": [{"type": "text", "text": ...}]}`, where the text is the
JSON the command printed. The exit status of `tauto` is not looked at: `check` exits
with 3 when only holes are left and its JSON is still returned. A command that
writes anything to standard error, or whose output is not JSON, is answered with
error `-32005` carrying that text. Failures are errors of the response, not results
marked `isError`.

## Use

The server is a program, run by `tauto run`. It starts `tauto` by name (`proc_run`)
and hands it its own environment (`environ`), so it needs the `run` and `env`
permissions, which the host denies by default (`docs/design/host-effects.md`),
and nothing else. `tauto run` asks for them at
the start:

```sh
tauto run --backend rust totes/mcp/src/main.taut
```

An MCP client that starts servers over standard input and output gives them
no terminal to ask at, so its command allows it with `--yes`. The shape most clients accept, with the file it goes in named by the
client's own documentation:

```json
{
  "mcpServers": {
    "tauto": {
      "command": "tauto",
      "args": ["run", "--backend", "rust", "--yes", "/path/to/totes/mcp/src/main.taut"]
    }
  }
}
```

The relative `file` of a tool is read from the directory the client starts the
server in.

To try it by hand, send one session to a single process; a fresh process has not
been initialized, and answers every other method with `-32002`:

```sh
cd totes/mcp
{
  echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"clientInfo":{"name":"test","version":"1.0"}}}'
  echo '{"jsonrpc":"2.0","method":"notifications/initialized"}'
  echo '{"jsonrpc":"2.0","id":2,"method":"tools/list"}'
  echo '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"tauto_goals","arguments":{"file":"examples/simple_proof.taut","hole":"proof"}}}'
} | tauto run --backend rust --yes src/main.taut
```

`examples/simple_proof.taut` has one proved theorem and one with the hole `?proof`.

## Protocol

One JSON-RPC message per line, in and out. An empty line is skipped. The server
ends when standard input does.

* `initialize` is answered with `protocolVersion` `2024-11-05` whatever the client
  asked for, `serverInfo` (`tauto-mcp-server`, `0.1.0`) and `capabilities` of
  `{"tools": {}}`. `clientInfo` is read and kept, and not used. `ping` is answered
  with `{}`.
* A request with an `id` gets exactly one response with the same `id`. A message
  without an `id`, or whose `id` is not null, a number or a string, is a
  notification and gets none; every notification is ignored, `initialized` and
  `notifications/cancelled` included.
* A line that is not JSON is answered with `-32700`, and a JSON value that is not a
  request (no `"jsonrpc": "2.0"`, no string `method`) with `-32600`, both with a
  null `id`.

| Code | When |
| --- | --- |
| `-32002` | a method other than `initialize` before `initialize` |
| `-32003` | `initialize` a second time |
| `-32004` | `tools/call` of an unknown tool |
| `-32005` | the command could not be started, wrote to standard error, or did not print JSON |
| `-32006` | `tools/call` without `params` or `arguments`, or a missing `file`, `hole` or `expr` |

A method the server does not know is answered with `-32601`. The codes `-32602` and
`-32603` are defined in `src/jsonrpc.taut` and not produced.

## Not done

* Resources, prompts, cancellation and progress are not offered
  (`capabilities` has `tools` only).
* There are no proofs about the server, and no automated test: nothing under `cases/`
  runs it. Its only check is the session above.
