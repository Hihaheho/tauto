# Incremental computation: whale and query-flow

Both are written in Tauto.

- **whale** (`totes/whale`) tracks dependencies only: nodes (key `K`, content
  `T`) record what they read and when, and whale answers whether a node is
  still valid. The graph is a value. Validity, early cutoff, reverse edges and
  cycle detection are proved axiom-free (`totes/whale/README.md`).
- **query-flow** (`totes/query-flow`) runs queries on whale, caches results,
  handles assets and persists state.

## Queries and assets

- A **query** is a function from a database `Db` to a value; what it reads is
  recorded, and if nothing read changed, the cached result is returned.
- An **asset** is an external input (file text, config), a leaf of the graph,
  provided by the host via `resolve_asset` or by a registered locator on first
  read. A query reading a loading asset stops and `run` returns `Suspended`;
  `pending_assets` lists what to provide.
- **Early cutoff**: a recomputed result equal to the old one keeps its
  `changed_at`. Outputs compare by encoded text unless `output_eq` is given,
  assets by `asset_eq`, errors by the runtime's comparator (default: never
  equal).
- **Durability** (`Volatile` < `Transient` < `Stable` < `Static`): a query's is
  the lowest it read; a change at one level only revalidates queries at or below
  it.
- **Errors**: `Db::fail(db, e)` results are cached like values, propagate
  through `Db::query` and are caught by `Db::try`. `Db::cancel`, `Cycle`,
  `Suspended` and `DependenciesRemoved` are not cached.

```
@query!(Add) => fn Add, fn Add::register
fn add(db: Db, a: i64, b: i64): i64 ! {halt, div} { a + b }

@query!(Tagged { keys: [a] }) => fn Tagged
fn tagged(db: Db, a: i64, note: Text): i64 ! {halt, div} { a }

@asset_key!(Source { asset: Text }) => fn SourceFile::codec, fn Source
pub struct SourceFile { path: Text }

@asset_key!(Labeled { asset: Text, keys: [path] }) => fn LabeledFile::codec, fn Labeled
pub struct LabeledFile { path: Text, label: Text }
```

- `@query!(Add)` makes `fn Add(a: i64, b: i64): Query(i64)` (first parameter is
  the database, the rest are keys) and `fn Add::register(rt: Runtime)`, which
  registers how to rebuild the query from its keys so results loaded from disk
  can be recomputed. `output_eq: f` sets the comparison.
- `keys: [a, …]` keys only the listed arguments (`Tagged(1, "x")` and
  `Tagged(1, "y")` are the same query); such queries get no `register`.
- `@asset_key!` on a parameterless struct with named fields makes the kind
  `fn Source(): AssetKind(SourceFile, Text)` and `SourceFile::codec()`.
  `asset_eq: f` and `keys: [path, …]` as above; with partial keys the asset
  remembers, in this process only, the last full key it was named by, and
  reports that key to `list_asset_keys`, `pending_assets(_of)` and locators.
- Locators are `(Db, K) -> LocateResult(T)`, registered with
  `register_asset_locator(rt, Source(), f)`; they return `Ready(v, d)` or
  `Pending`.
- Keys, outputs and assets are encoded by `Codec`: built in for `i64`, `u64`,
  `Nat`, `Text`, `Bool`, `Unit` and their `List`/`Option`; otherwise `T::codec()`.
- Inside queries: `Db::query`, `try`, `asset`, `asset_state` (`None` while
  loading), `list_asset_keys` (recomputes when the set changes), `fail`,
  `cancel`.
- Outside: `run`, `poll` (answer and last-changed revision), `changed_at`,
  `invalidate`, `remove_query`, `remove_query_if_unused`, `clear_cache`,
  `resolve_asset`, `resolve_asset_error`, `invalidate_asset`, `remove_asset`,
  `pending_assets`, `pending_assets_of`, `has_pending_assets`. `build_runtime`
  takes the error comparator and a tracer receiving `Event`s.

Graph keys are text: `q` (query), `a` (asset) or `s` (asset-kind key set),
then the name and encoded keys as fields. A whale node's content is a `Slot`:
asset state, query result (encoded output or error) or invalidated query.
Revalidation brings each dependency up to date in read order and recomputes if
any changed after it was read. A query's runner is learned the first time it
runs in the process.

## Storage

`save(rt)` and `load(rt)` use only query-flow's storage effects
(`src/storage.taut`): `store_read(name): Option(Bytes)` and
`store_replace(name, b): Result(Unit, Text)`, which replaces atomically. The
state is item `state.qflow`. Handlers:

- `with_dir_store(dir, body)` (`src/storage_fs.taut`): item `name` is file
  `dir/name`, written to `name.tmp` then renamed; unreadable files are absent.
- `with_memory_store(m, body)`: a `MemoryStore` (`get`, `set`, `remove`), for
  environments without a filesystem and for tests.

### Format

UTF-8 text made of fields `<byte length>:<content>` (`5:hello`):

```
"query-flow" "1" checksum body…
```

- The checksum is FNV-1a (32-bit) of the body's bytes, in decimal.
- Body: the number of revision levels (4) and their counters, then the number
  of nodes and the nodes.
- Node: key; content (`L` loading asset, `R` value, `F` asset error, `O`
  output, `E` query error, `C` invalidated query); durability, `verified_at`,
  `changed_at`, level; dependencies as (key, `changed_at` when read);
  dependents.

Loading returns `NoState` if the item is missing, and `Discarded(reason)`
(leaving the runtime unchanged) on any mismatch: name, version, checksum,
malformed fields, trailing data, level count, duplicate keys, dependencies on
missing nodes. Otherwise the graph is replaced and every level counter is
bumped. Assets with values are unconfirmed until the host resolves them again
(or a locator does): an equal value with the same durability keeps
`changed_at`, so dependents stay valid; a different value is a change.
Queries reading unconfirmed assets stop, and the assets appear in
`pending_assets`. Loaded queries have no runner until they recompute.

## Undecided

- Single-threaded only, so no detection of assets resolved mid-run.
- Full keys of partially keyed assets are not saved; after loading,
  unnamed ones are not listed and locators are not called for them.
- Errors are `Text`; there is no typed downcast.
- Saving writes the whole state, not only changed nodes.
