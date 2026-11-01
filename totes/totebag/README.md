# totebag

What Totebag decides without the network, Git or the file system: whether a tote
name, a repository URL, a ref, a directory, a commit ID, a tree ID and a path in a
source tree are taken. `crates/totebag` reads manifests and locks, runs Git and
writes the cache; each of these questions it asks here.

| Function | Takes |
| --- | --- |
| `tb_valid_name(t)` | lowercase letters, digits and `-`, starting with a letter, at most 64 bytes |
| `tb_check_url(t)` | `https://` in the form `url` writes it, without credentials, query or fragment, or `file:///` not going through `..`; else why not |
| `tb_check_ref(t)` | `refs/heads/…` or `refs/tags/…` as `git check-ref-format` takes it, without patterns or `@{` |
| `tb_check_dir(t)` | `""`, or relative plain components |
| `tb_check_rev(t)` | `sha1:` and 40 lowercase hex digits, or `sha256:` and 64 |
| `tb_check_source_id(t)` | `sha256:` and 64 lowercase hex digits |
| `tb_check_tree(ps)` | no two paths one file without case, no file also a directory |
| `tb_put`, `tb_render`, `tb_changes`, `tb_plan` | the entries of `Tauto.lock`, its text, what locking changed, and where a commit comes from |
| `tb_twice`, `tb_independent` | a policy's names each once, and age witnesses apart from observers |
| `tb_check_path(t)` | a relative path without empty components, `.`, `..`, backslashes or control characters; else why not |

`proof/samples.taut` checks the examples of `docs/design/totebag.md` and further cases of each rule.

## Changing it

`crates/totebag/src/core.rs` is this tote compiled by tauto-build. The compiler reads
totes through `crates/totebag`, so it cannot be compiled in a build script; after a
change here, run `cargo run -p totebag-gen`. A test in `crates/totebag` fails while
the file is out of date.

```
tauto check proof/samples.taut
```
