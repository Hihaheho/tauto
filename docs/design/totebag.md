# Totebag

Totebag is how a tote depends on totes in Git repositories. There is no central
registry: a dependency names a repository, a ref and a directory, and the
project fixes the exact commit and content of each in `Tauto.lock`. Which
commits may be adopted is decided by the user or by the indexes the project
trusts, never by a server.

What Totebag accepts is decided in Tauto (`totes/totebag` checks names, URLs,
refs, directories and paths; `totes/index` decides adoption). The Rust side
(`crates/totebag`, `crates/totebag-index`) only touches the world: Git, the
network, the disk cache, Eure, SHA-256 and the clock.

## Declaring

```eure
dependencies {
  text { path = "../text" }
  fire: workspace
  semver { git = "https://example.com/tauto/monorepo", ref = "refs/heads/main", dir = "semver" }
}
```

- `path` names a directory relative to the depending tote.
- `NAME: workspace` resolves to a member of the enclosing workspace by
  `package.name` ([`workspace.md`](workspace.md)). It is not locked.
- `git` is an `https://` URL without credentials, query or fragment, or a
  `file:///` URL; only the project's own manifests may name `file:///`.
- `ref` is a full `refs/heads/…` or `refs/tags/…`, never `HEAD` or a pattern.
- `dir` is the tote's directory (default: the root). `sparse = true` fetches
  and hashes only that directory, so the tote cannot read outside it.
- One dependency entry is path, workspace, or Git—not a combination.
- A project has one tote per name; two totes asking for one name must ask for
  the same source.

## The lock

`Tauto.lock` beside the project's `Tauto.eure` has one entry per Git
dependency, transitively, with `name`, `git`, `ref`, `dir`, optional `sparse`,
`rev` (the full commit ID with its object format) and `source`, the SHA-256 of
the tree in `source-v1` form:

```text
frame(B)  = u64be(length(B)) || B
source-v1 = UTF8("tauto-source-v1\0") || u64be(number of files)
            || per file, in byte order of path: frame(UTF8(path)) || executable byte || frame(bytes)
```

Links, submodules, special files, `.`/`..` components and paths that collide
case-insensitively are refused. The whole repository is hashed (only `dir` for
sparse sources, with repository paths), so paths between totes of one
repository stay inside what was fetched. The lock of the tote being read is
the lock for every tote it reads.

## Fetching

Trees are kept read-only under their IDs in `$TAUTO_TOTES` (default
`~/.cache/tauto/totes`). A tree is written to a temporary directory, hashed
again and renamed into place only when the ID matches. Git runs with
redirects, prompts and hooks off and only `https` and `file` allowed; the
user's own Git configuration still applies. Sparse sources fetch with a blob
filter and ask only for the blobs under `dir`.

## Commands

| Command | Does |
|---|---|
| `tauto add --git URL [NAME] [--branch B \| --tag T] [--dir D [--sparse]] [--project ID]` | writes, locks and fetches an entry |
| `tauto add --path DIR [NAME]` | writes a path entry |
| `tauto remove NAME` | removes it and what is no longer used |
| `tauto update [NAME…] [--dry-run]` | moves to the ref's newest adoptable commit |
| `tauto lock [--check]` | locks what is missing, drops what is unused |
| `tauto fetch [--verify]` | fetches what the lock fixes |
| `tauto deps` | the dependency tree |
| `tauto audit [--json]` | per tote: externs, axioms, effects, Rust bridges, crates, JavaScript sources |

`add` guesses the default branch, the directory and the name when it can, and
leaves `Tauto.eure` unchanged when locking fails. `check`, `run`, `build`,
`test` and `doc` fetch what the lock fixes but never change the lock; a
dependency missing from it is an error naming `tauto lock`, since adopting a
commit is a decision. `--offline` makes a missing tree an error.

## Trusted indexes

An index is a Git repository in which its keeper records, one batch per commit,
the package revisions they observed and accepted or rejected. A project's
`Trust.eure` names the indexes it trusts (pinned by ID, repository, ref and
checkpoint) and what adoption requires: which observers must accept, which age
witnesses (`local` is this machine) must have seen the revision, a minimum age,
and how fresh checkpoints and origin checks must be. Under a policy every Git
dependency names its `project` ID.

`add`, `update` and `lock` sync the named indexes and ask `totes/index`
whether the new commit may be adopted; `update` stays at the locked commit and
says why when it may not, and `add` and `lock` refuse. Locked commits are not
asked about again.

### The user's own policy

`~/.config/tauto/trust.eure` (or `$TAUTO_USER_TRUST`) adds to every project's
policy and can only add: observers and witnesses join every rule, the longer
wait and the shorter lifetimes win. A wait left out is 14 days, so nothing just
published is adopted by default. An index both files name must be the same
index at the same checkpoint, which is what makes adding to a rule admit
nothing more (`ix_policy_strengthening`).

### Reading an index

An index's root holds `Index.eure` (the same in every commit) and
`observations.eure` (the commit's batch). The history is a line from an empty
root batch; merges are refused, and both files are read strictly. A
checkpoint's digest chains its parent's:

```text
H(c) = SHA256("tauto-index-checkpoint-v1\0" || P(c) || frame(rev)
              || frame(commit) || frame(Index.eure) || frame(observations.eure))
P(c) = 0x00 at the root, else 0x01 || H(parent)
```

The index's ID is its root's digest.

### What this machine keeps

`~/.local/state/tauto/index` (or `$TAUTO_INDEX_STATE`) keeps per index the pin,
the prefix taken in, whether it stopped, the last origin check, when each
checkpoint was first seen, and the latest evaluation time. Syncing takes in new
batches through the core; a refused batch or a rewritten history stops the
index at its prefix for good, while an unreadable history changes nothing and
lets the origin check age. Evaluation times only move forward.

### Commands

| Command | Does |
|---|---|
| `tauto index sync` / `status` / `check [NAME…]` | sync, show requirements, explain whether locked commits may be adopted |
| `tauto index new DIR` | starts an index and prints its `Trust.eure` entry |
| `tauto index observe`, `decide accept\|reject`, `withdraw` | add events to the batch being written, each checked by the core |
| `tauto index publish [--valid-for S]` | commits the batch |

## Undecided

- Recording other indexes' contents from the CLI.
- Result kinds (pending, rejected, conflict) as values rather than text.
- Version requirements, several instances of one tote, features.
- Totes with `syntax` must commit their tables, since the cache is read-only.
- Only SHA-1 repositories are fetched.