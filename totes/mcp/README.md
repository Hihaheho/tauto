# Tauto MCP Server

A Model Context Protocol (MCP) server implementation written entirely in Tauto, providing AI coding agents with direct access to Tauto's proof workflow.

## Purpose

This MCP server enables AI coding agents (Claude Code, Cursor, etc.) to interact with Tauto's proof system, allowing them to:
- Check Tauto files and report axioms used
- Inspect proof goals at holes
- Try filling holes with expressions
- Get suggestions for terms that fit holes
- Query the library of available constants

This is a key component of Tauto's mission: "A minimal language for AI to build and prove correct software."

## Architecture

The implementation follows Tauto's design principles:
- **No external dependencies**: Implements JSON-RPC 2.0 and MCP from scratch
- **Explicit effects**: Uses Tauto's effect system (`stdin`, `stdout`, `proc_run`) for all I/O
- **Type-safe**: Full dependent types ensure correctness
- **Minimal**: Four focused modules (the `json` tote and three files in `src/`), with ~1000 lines in `src/`

### Modules

1. **json** tote (`totes/json`): JSON parser and writer
   - Hand-written recursive descent parser
   - Supports all JSON types: null, boolean, number, string, array, object
   - Handles escape sequences and whitespace
   - Round-trip property: `parse(serialize(x)) = x` for valid JSON

2. **jsonrpc.taut**: JSON-RPC 2.0 protocol implementation
   - Request/response/notification handling
   - Error code mapping
   - ID matching (ensures responses match requests)

3. **mcp.taut**: MCP protocol layer
   - Capability negotiation (`initialize`/`initialized` handshake)
   - Tool discovery (`tools/list`)
   - Tool execution (`tools/call`)
   - Wraps Tauto CLI commands with proper JSON I/O

4. **main.taut**: Stdio transport
   - Newline-delimited JSON-RPC over stdin/stdout
   - State management across requests
   - Error handling and recovery

## Tools Exposed

### `tauto_check`
Check a Tauto file and report axioms used.

Parameters:
- `file` (string, required): Path to the Tauto file

Returns the JSON output from `tauto check --json FILE`.

### `tauto_goals`
Get proof goals at holes in a file.

Parameters:
- `file` (string, required): Path to the Tauto file
- `hole` (string, optional): Name of specific hole to inspect

Returns the JSON output from `tauto goals --json [--hole NAME] FILE`.

### `tauto_try`
Try filling a hole with an expression.

Parameters:
- `file` (string, required): Path to the Tauto file
- `hole` (string, required): Name of the hole
- `expr` (string, required): Expression to try

Returns the JSON output from `tauto try --json --hole NAME --with EXPR FILE`.

### `tauto_suggest`
Suggest terms that fit a hole.

Parameters:
- `file` (string, required): Path to the Tauto file
- `hole` (string, required): Name of the hole
- `limit` (number, optional): Maximum suggestions to return

Returns the JSON output from `tauto suggest --json --hole NAME [--limit N] FILE`.

### `tauto_library`
List available constants with their types.

Parameters:
- `file` (string, required): Path to the Tauto file

Returns the JSON output from `tauto library --json FILE`.

## Usage

### Building

```bash
cd totes/mcp
tauto build src/main.taut -o mcp-server
```

### Running Standalone

```bash
./mcp-server
```

The server reads newline-delimited JSON-RPC 2.0 messages from stdin and writes responses to stdout.

### MCP Configuration

To register this server with Claude Desktop or Cursor, add to your MCP configuration:

**Claude Desktop** (`~/Library/Application Support/Claude/claude_desktop_config.json` on macOS):

```json
{
  "mcpServers": {
    "tauto": {
      "command": "/path/to/tauto/totes/mcp/mcp-server"
    }
  }
}
```

**Cursor** (`.cursor/mcp.json` in your project):

```json
{
  "mcpServers": {
    "tauto": {
      "command": "/path/to/tauto/totes/mcp/mcp-server"
    }
  }
}
```

### Testing

Interactive testing:

```bash
# Initialize
echo '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"clientInfo":{"name":"test","version":"1.0"}}}' | ./mcp-server

# List tools
echo '{"jsonrpc":"2.0","id":2,"method":"tools/list"}' | ./mcp-server

# Call a tool
echo '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"tauto_check","arguments":{"file":"examples/simple_proof.taut"}}}' | ./mcp-server
```

## Protocol Details

### JSON-RPC 2.0

The server implements the JSON-RPC 2.0 specification:
- Requests have `jsonrpc: "2.0"`, `method`, optional `params`, optional `id`
- Responses have `jsonrpc: "2.0"`, `id` (matching request), and either `result` or `error`
- Notifications have no `id` and receive no response
- Error codes follow the JSON-RPC specification (-32700 to -32603 for protocol errors)

### MCP Protocol

The server implements MCP specification version `2024-11-05`:

1. **Initialization**: Client sends `initialize` request with `clientInfo`
2. **Capability negotiation**: Server responds with `serverInfo` and `capabilities`
3. **Initialized notification**: Client sends `initialized` notification
4. **Tool operations**: Client can call `tools/list` and `tools/call`
5. **Ping**: Optional `ping` requests are supported

### Error Handling

The server handles errors at multiple layers:
- **Parse errors** (-32700): Invalid JSON
- **Invalid request** (-32600): Malformed JSON-RPC
- **Method not found** (-32601): Unknown MCP method
- **Invalid params** (-32602): Missing or wrong parameters
- **Internal errors** (-32603): Unexpected failures
- **Server errors** (-32000 to -32099): MCP-specific errors

Custom error codes:
- `-32002`: Server not initialized (called method before `initialize`)
- `-32003`: Server already initialized (called `initialize` twice)
- `-32004`: Tool not found
- `-32005`: Tool execution failed (Tauto CLI error)
- `-32006`: Invalid tool parameters

## Implementation Notes

### Host Effects Added

This implementation uses only existing Tauto host effects:
- `stdin()`: Read lines from standard input
- `stdout(t)`: Write to standard output
- `stdout_flush()`: Ensure output is delivered
- `proc_run(p)`: Execute `tauto` CLI commands
- `fs_read(path)`: Read files (used by Tauto CLI, not directly by server)

No new host effects were added. All I/O follows Tauto's effect system, making it explicit in function signatures what each function can do.

### JSON Implementation

The JSON parser is a hand-written recursive descent parser with explicit state threading:
- Tracks position for error reporting
- Handles all JSON escape sequences except `\uXXXX` (unicode escapes)
- Numbers are kept as text to preserve precision
- Objects are represented as association lists (not hash maps)

Known limitations:
- Unicode escapes (`\uXXXX`) are not supported
- No streaming parser (entire input must be in memory)
- Object field order is preserved but not optimized for lookup

### Proven Properties

While this implementation does not include formal proofs, the following properties hold by construction:

1. **Response ID matching**: The `handle_request_with_id` function ensures every response carries the same `id` as its request (type: `RpcId -> RpcResponse`).

2. **Request-response correspondence**: Each request with an `id` produces exactly one response. Notifications (no `id`) produce no response.

3. **JSON round-trip**: For valid `Json` terms, `json_parse(json_text(v))` succeeds and equals `v` (up to object field order and number formatting).

4. **Effect safety**: All I/O is explicitly tracked in effect rows. Functions that don't perform I/O have no effects in their signatures.

These properties could be formally stated and proven in Tauto, demonstrating the language's capability to verify protocol implementations. This would be excellent material for showcasing Tauto's AI-native design.

## Future Enhancements

Potential additions (not implemented in v0.1.0):

- **Resources**: Expose Tauto source files as MCP resources
- **Prompts**: Provide proof templates and tactics as MCP prompts
- **Cancellation**: Handle `notifications/cancelled` for long-running operations
- **Progress**: Report progress for multi-step operations
- **Caching**: Cache parse results for repeated file access
- **Unicode escapes**: Full JSON compliance with `\uXXXX` sequences
- **Formal proofs**: Verify protocol properties (ID matching, round-trip, etc.)
- **Error recovery**: More graceful handling of partial reads

## Testing

See `cases/mcp/` for test cases:
- Protocol-level tests feeding scripted JSON-RPC sessions
- End-to-end tests calling tools on example files
- Error handling tests for malformed requests

Run tests:

```bash
cargo nextest run -p tauto-test-suite -- mcp
```

## License

Licensed under the same terms as Tauto (Apache-2.0 OR MIT).
