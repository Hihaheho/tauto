# Totebag

Totebag is how a tote depends on totes in Git repositories. It has no central
registry: a dependency names a repository, a ref and a directory, and the
project fixes the exact commit and the content of each one in `Tauto.lock`.
Which commits may be adopted is decided by the user, or by the indexes the
project trusts (`totes/index`), never by a server.

What Totebag accepts is decided in Tauto: the checks of names, URLs, refs,
directories, IDs and tree paths are `totes/totebag`, and whether an index lets
a commit be adopted is `totes/index`. The Rust side (`crates/totebag`,
`crates/totebag-index`) keeps what touches the world: Git, the network, the
cache on disk, reading Eure, SHA-256 and the clock.

## Declaring

```eure
dependencies {
  text { path = "../text" }
  semver {
    git = "https://example.com/tauto/monorepo"
    ref = "refs/heads/main"
    dir = "semver"
  }
}
```

- `git` is an `https://` URL without credentials, query or fragment, or a
  `file:///` URL of a repository on this machine. Only the project's own
  manifests may name a `file:///` repository; a fetched tote may not.
- `ref` is a full ref, `refs/heads/NAME` or `refs/tags/NAME`: where `update`
  looks for newer commits. It is never `HEAD` or a pattern.
- `dir` is the tote's directory in the repository; without it, the root.
- A path dependency of a fetched tote stays inside what was fetched.

A project has one tote of each name. Two totes asking for the same name must
ask for the same directory or the same Git source; otherwise locking fails and
names both.

## The lock

`Tauto.lock`, beside `Tauto.eure` of the project, has one entry per Git
dependency of the project and of everything it depends on:

```eure
format = 1

@ totes[] {
  name = "semver"
  git = "https://example.com/tauto/monorepo"
  ref = "refs/heads/main"
  dir = "semver"
  rev = "sha1:0123456789abcdef0123456789abcdef01234567"
  source = "sha256:…"
}
```

`rev` is the full commit ID with its object format. `source` is the SHA-256
of the commit's whole tree in the `source-v1` form:

```text
frame(B)  = u64be(length(B)) || B
source-v1 = UTF8("tauto-source-v1\0") || u64be(number of files)
            || each file, in the byte order of its path:
               frame(UTF8(path)) || executable (one byte) || frame(bytes)
```

Paths are relative with `/`; links, submodules, other special files, empty
components, `.`, `..`, backslashes, NUL, and two paths that are one file when
case is not told apart are refused. Times and owners are not part of it. The
whole repository is hashed, not only `dir`, so that the paths between totes of
one repository stay inside what was fetched.

The lock of the tote being read is the lock of every tote it reads: a tote
reached by path or from Git finds its own Git dependencies there, not in a lock
of its own.

## Fetching

Trees are kept under their IDs in `$TAUTO_TOTES` (else
`$XDG_CACHE_HOME/tauto/totes`, else `~/.cache/tauto/totes`):

```text
src/<hex>/…      a tree, its files read-only
git/<hex>.git    a bare repository per URL
tmp/             trees being written
```

A tree is written to `tmp/`, read back, hashed again and renamed into place
only when the ID matches, so `src/<hex>` holds that tree whenever it exists.
Git runs as `git` with redirects, terminal prompts and hooks off and only the
`https` and `file` protocols allowed. The user's own Git configuration (a
credential helper, `insteadOf`) still applies.

## Commands

| Command | Does | Network | Lock |
| --- | --- | --- | --- |
| `tauto add --git URL [NAME] [--branch B \| --tag T] [--dir D] [--project ID]` | writes the entry, locks and fetches it | yes | adds |
| `tauto add --path DIR [NAME]` | writes a path entry | no | as needed |
| `tauto remove NAME` | takes the entry out | no | drops what is no longer used |
| `tauto update [NAME…] [--dry-run]` | moves to the newest commit of the ref, and shows what changed | yes | changes |
| `tauto lock [--check]` | locks what is not locked, drops what is not used; `--check` fails when the lock is not up to date | `--check`: no | adds, drops |
| `tauto fetch [--verify]` | fetches what the lock fixes; `--verify` hashes the cache again | yes | no |
| `tauto deps` | the dependency tree with sources and commits | no | no |
| `tauto audit [--json]` | per tote: the externs, axioms and effects its sources declare, and its Rust bridge, crates and JavaScript sources | no | no |

`add` guesses what it can: the default branch of the repository when neither
`--branch` nor `--tag` is given; the root, the directory named `NAME`, or the
only tote of the repository when `--dir` is not given (with several, it lists
them); the tote's own name when `NAME` is not given. When the dependency cannot
be locked, `Tauto.eure` is left as it was.

`check`, `run`, `build`, `test` and `doc` read the lock. What it fixes and the
cache lacks is fetched and checked against `source`; the lock is never changed
by them. `--offline` (or `TAUTO_OFFLINE=1`) makes a missing tree an error. A
dependency the lock does not have, or has for another source, is an error that
names `tauto lock`: adopting a commit is a decision, taken only by `add`,
`update` and `lock`.

## Trusted indexes

A project may say whose judgement a commit needs before it is adopted. Its
`Trust.eure`, beside `Tauto.eure`, names indexes and what adopting asks of
them; an index is a Git repository that records, one batch a commit, the
package revisions its keeper observed and accepted or rejected.

```eure
format = 1
kind = "policy"
track = "dependency-closure"

@ indexes[] {
  alias = "alice"
  id = "sha256:…"
  transport = "https"
  repository = "https://example.org/alice/index"
  ref = "refs/heads/main"
  pin_rev = "sha1:…"
  pin_sha256 = "sha256:…"
}

@ defaults {
  require = "all"
  observers = ["alice"]
  age_witnesses = ["local"]
  min_age_seconds = 604800
  max_checkpoint_lifetime_seconds = 86400
  max_source_check_age_seconds = 3600
}
```

`rules` may give a project its own complete rule. A remote age witness is read
over `https` and is not an observer's index or repository; `local` is this
machine. `transport = "local-owned"` is one's own index in a `file:///`
repository.

Under a policy every Git dependency names its project, the ID its revisions
are known by in the indexes:

```eure
semver {
  git = "https://example.com/tauto/monorepo"
  ref = "refs/heads/main"
  dir = "semver"
  project = "sha256:…"
}
```

The revision is the commit's hex ID and the content is the SHA-256 of the
whole tree (`source` in the lock). `add`, `update` and `lock` sync the indexes
a rule names, then ask the core in `totes/index`, compiled into
`totebag-index`, whether the new commit may be adopted. `update` keeps a
dependency at its locked commit when it may not, and says why; `add` and
`lock` refuse. A commit already in the lock is not asked about again.

### The user's own policy

The user's own policy adds to every project's `Trust.eure` on this machine,
and can only add: observers and age witnesses join every rule, the wait is
the longer of the two, and the checkpoint lifetime and the origin check age
the shorter. It is read from `$TAUTO_USER_TRUST`, else
`$XDG_CONFIG_HOME/tauto/trust.eure`, else `~/.config/tauto/trust.eure`; a
file `$TAUTO_USER_TRUST` names must be there.

```eure
format = 1
kind = "user-policy"
track = "dependency-closure"

@ indexes[] {
  …as in Trust.eure
}

@ require {
  observers = ["dave"]
  age_witnesses = ["local"]
  min_age_seconds = 1209600
  max_checkpoint_lifetime_seconds = 86400
  max_source_check_age_seconds = 3600
}
```

Every field of `require`, and `require` itself, may be left out. Safe by
default: a wait left out is 14 days, so nothing published just now is
adopted, and with no user policy at all that wait is all it adds.
`min_age_seconds = 0` waits only as long as `Trust.eure` says. An index both
files name is the same index read from the same repository and ref and pinned
at the same checkpoint; the user's policy may add to what the project trusts,
not change it, which is what makes adding to a rule admit nothing more
(`ix_policy_strengthening`). A witness stays independent of every observer of
the rule it joins. `tauto index status` shows the user policy in effect and
what each rule requires with it, and a refusal whose wait comes from it says
so.

### Reading an index

An index's root holds `Index.eure`, the same bytes in every commit, and
`observations.eure`, the batch the commit adds. The history is a line from a
root whose batch is numbered 0 and is empty; a merge is refused. Both files
are read as mode-100644 blobs, every object hashed again by Git, and read
strictly: an unknown key, an extension, a hole or a value of the wrong type
refuses the batch. A checkpoint's digest fixes its parent's, its commit
payload and both files:

```text
H(c) = SHA256("tauto-index-checkpoint-v1\0" || P(c) || frame(rev)
              || frame(commit) || frame(Index.eure) || frame(observations.eure))
P(c) = 0x00 at the root, else 0x01 || H(parent)
```

The index's ID is its root's digest. The core compares identities only for
equality, so each identity is given a small number for one evaluation: one
number per identity and kind, never two identities to a number.

### What this machine keeps

`$TAUTO_INDEX_STATE` (else `$XDG_STATE_HOME/tauto/index`, else
`~/.local/state/tauto/index`) holds `state.eure` and a Git mirror of each
index. Nothing fetched writes it. For each index it keeps the pin, the prefix
of the history taken in, whether the index stopped and why, and the last check
of its origin; it keeps when each checkpoint was first had here, and the
latest time an evaluation ran. A writer holds `state.lock` from reading to
writing, and the file is replaced whole.

Syncing fetches the branch with all its history and takes in the batches after
the prefix through `ix_ingest_grounded`. A batch the core refuses, or a
history that no longer holds the prefix, stops the index at the prefix for
good. A history that cannot be read changes nothing; the last check of the
origin ages until nothing can be adopted with it. The pin moves to the head
when the origin answered with it just now. Every evaluation moves the
evaluation time forward, whatever it answers, and one at an earlier time is
refused.

The core answers yes or no; `tauto index check` and a held `update` also say
why not (not observed, not accepted, rejected, withdrawn, another source tree,
stopped, a stale origin check, an expired batch, still waiting and until when),
found by walking the same facts.

### Commands

| Command | Does |
| --- | --- |
| `tauto index sync` | fetches every index `Trust.eure` names and takes in what is new |
| `tauto index status` | what adopting requires, with the user policy, and what this machine holds of each index |
| `tauto index check [NAME…]` | whether the locked commits may be adopted now, and why not |
| `tauto index new DIR [--name N]` | starts an index and prints its entry for `Trust.eure` |
| `tauto index observe (NAME [--locked] \| --project ID --git URL)` | observes a commit and its tree in the batch being written |
| `tauto index decide (NAME \| --project ID) accept\|reject --reason T` | accepts or rejects a revision |
| `tauto index withdraw (NAME \| --project ID) --reason T` | takes a revision back for good |
| `tauto index publish [--valid-for S]` | commits the batch being written, or an empty one |

The batch being written is `observations.eure` in one's own index's working
tree; each event is checked by the core before it is added, and `publish`
commits the two files only.

## Undecided

- Crawling other indexes and recording what they hold
  (`index-observation`) from the CLI; it is read and checked when present.
- The detailed result kinds (pending, rejected, conflict) as values: the
  reasons are text.
- Reading an index's history takes several `git` processes a commit.
- Version requirements, several instances of one tote, and features.
- A tote with `syntax` must have its table files in the repository: the cache
  is read-only, so `tauto syntax gen` cannot write them there.
- Only SHA-1 repositories are fetched by `add` and `update`.
