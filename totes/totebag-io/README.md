# totebag-io

The part of Totebag that touches files, in Tauto: what `crates/totebag/src/source.rs`,
`lock.rs`, `cache.rs`, `git.rs`, `index/*` and `crates/totebag-index` do. `totes/totebag` keeps the checks (which paths and trees are taken); this tote
reads a directory and computes its source ID.

| Function | Does |
| --- | --- |
| `tb_tree(files)` | checks files as `Tree::new` does; gives them in path order with the `source-v1` ID |
| `tb_parse_lock(text)` | the entries of a `Tauto.lock` in name order, read as `lock::parse` reads it (totes/eure reads the document), or the ID of the message `crates/totebag` gives |
| `tb_default_branch`, `tb_mirror_open`, `tb_fetch_head`, `tb_fetch_history`, `tb_fetch_rev`, `tb_resolve`, `tb_keep`, `tb_git_tree`, `tb_commit`, `tb_root_entry`, `tb_blob` | Git as `git.rs` drives it, through `proc_run` (`src/git.taut`), with the same variables taken out of its environment |
| `tb_strict_parse`, `tb_fields`, `tb_field_*`, `tb_time`, `tb_time_text`, `tb_sha256`, … | an index document read strictly, as `index/strict.rs` reads it (`src/strict.taut`) |
| `tb_config`, `tb_batch`, `tb_render_batch` | `Index.eure` and `observations.eure` (`src/ledger.taut`) |
| `tb_parse_policy`, `tb_parse_user`, `tb_strengthen` | the trust policy and the user's policy (`src/policy.taut`, `src/user.taut`) |
| `tb_parse_state`, `tb_render_state`, `tb_receive`, `tb_state_dir`, `tb_hold`, `tb_save`, `tb_let_go` | the index state `state.eure` (`src/state.taut`) |
| `tb_history`, `tb_checkpoint_digest` | an index's history and its checkpoint digests (`src/checkpoint.taut`) |
| `tb_sync`, `tb_evaluate` | syncing a trusted index and whether a package revision may be adopted, through `totes/index` (`src/engine.taut`) |
| `tb_read_dir(dir)` | reads regular files and directories under `dir` as `Tree::read_dir` does, refusing links and other kinds |

A file is executable when its owner may execute it, as for Rust; the cache
makes the files it installs read-only and keeps their executable bit.
An error is the ID of the message `crates/totebag` gives; where Rust wraps one under
`totebag-at`, it is written `totebag-at <the inner ID>`.
`state.eure` is read and written whole under the lock Rust takes on `state.lock`
(`tb_hold`, `tb_save`, `tb_let_go`).
`tools/selfhost-harness/tests/totebag.rs` compares every part with Rust's.
