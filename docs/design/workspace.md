# Workspace dependencies

A workspace is a set of totes that may depend on each other by package name.
Membership is declared on both sides: the workspace root lists member
directories, and each member names that root. Tools never invent members by
scanning every `Tauto.eure` under a directory, and never infer membership from
ancestor manifests alone.

Path and Git dependencies stay as in [`totebag.md`](totebag.md). A dependency
entry is path, Git, or workspace—never more than one of these on the same
entry. There is no `workspace.exclude`.

## Declaring a workspace root

A workspace root writes a `workspace` map with `members`:

```eure
workspace {
  members = [
    ".",
    "game",
    "engine",
    glob`plugins/*`,
  ]
}
```

- `members` is an array. Each element is a plain path string or a `glob`…``
  value (Eure text whose language is `glob`).
- Every element names a **directory** relative to this `Tauto.eure`. A path
  that ends at a `Tauto.eure` file is refused.
- Plain strings are exact relative paths (metacharacters are ordinary
  characters). `glob`…`` patterns use `*` for one segment, `**` for zero or
  more segments, and `?` for one character other than `/`; other glob syntax
  is refused.
- Glob expansion walks only real directories. It does not follow symlinks. It
  skips hidden directory names (a segment that starts with `.`) and the
  build directories `target` and `node_modules`. A plain path may still name such
  a directory explicitly.
- Relative paths may contain `..` and `.`. Absolute paths and empty segments
  are refused.
- A manifest may omit `package`. Then it is a virtual workspace root: it names
  members and is not itself a tote.

A nested workspace root that also belongs to an outer workspace writes both
`parent` and `members`:

```eure
workspace {
  parent = "../.."
  members = ["demo", "refusals"]
}
```

`parent` is the relative path from this directory to the outer workspace root.
Having its own `members` does not make this directory the lock root (see
Lock).

## Member affiliation

Each member tote names its workspace root with a relative path:

```eure
workspace = "../.."
```

When the same file is also a nested workspace root, affiliation is the map's
`parent` field (above), not a second scalar.

Membership requires both:

1. The root's `members` (after glob expansion) names that tote's directory.
2. The tote's affiliation (`workspace = "…"` or `workspace.parent`) resolves
   to that root.

Tools do not walk ancestors to guess a root. A tote with no affiliation is
never a member. Syntax errors and illegal affiliation paths are errors; they
are not treated as “no affiliation”.

If the root itself has `package`, it is a member only when `"."` is in
`members` and its affiliation is that same root (the root's own `workspace`
map with `members`, and no `parent` pointing elsewhere).

## Candidate handling

Expand each `members` entry to candidate directories. For each candidate:

| `members` entry | Candidate | Result |
|---|---|---|
| glob | no `Tauto.eure` / not a tote | drop |
| glob | tote with no affiliation | drop |
| glob | tote affiliated to another root | drop |
| glob | tote affiliated to this root | member |
| plain path | missing tote, no affiliation, or other root | membership mismatch error |
| plain path | tote affiliated to this root | member |

Discovery does not recurse into a member looking for further `Tauto.eure`
files. Nested packages are members of a workspace only when that workspace's
`members` names them.

Within one workspace, member `package.name` values must be unique. Reading a
member's `Tauto.eure` is required for affiliation and `package.name`; that
read is not the same as checking or running the tote.

## Depending with `NAME: workspace`

```eure
dependencies {
  engine: workspace
  text { path = "../vendor/text" }
}
```

- `NAME: workspace` resolves to the unique member of the depending tote's
  workspace whose `package.name` is `NAME`.
- Only that workspace is searched. No member named `NAME` is an error. A tote
  that is not a workspace member may not write `*: workspace`.
- Path and Git forms stay. Combining path, Git, or workspace on one entry is
  an error.
- Duplicate dependency names, and two requests for the same name with
  different sources, follow the existing uniqueness rules
  ([`totebag.md`](totebag.md)).

Path dependencies may name totes in another workspace or totes with no
workspace affiliation. Workspace membership is not required for path
dependencies.

## Nested workspaces and cross-workspace path deps

A tote in another workspace is reached with an ordinary path dependency. Its
affiliation is whatever that tote declares. `NAME: workspace` inside it
resolves in **its** workspace, never rewritten to the depender’s. Reaching a
nested workspace does not pull all of its members into the depender.

Each tote lists only direct dependencies. Transitive dependencies are followed
when checking or running; callers do not restate them. Globs appear only in
`workspace.members`, not as a dependency form.

## Membership versus what is checked or run

Being a workspace member is not a dependency edge.

| Command | Loads / checks |
|---|---|
| `tauto check` at a workspace root | every member of that workspace, and each member's transitive dependencies |
| `tauto check --tote a` | member `a` (`package.name`) and its transitive dependencies |
| `tauto check` in a standalone tote | that tote and its transitive dependencies |
| `tauto run` / `tauto dev` | the selected entrypoint's tote and its transitive dependencies |

- `--tote a` accepts only a member `package.name` of the workspace in force.
  It does not accept a path, a standalone tote's own name, or a tote of
  another workspace. Outside a workspace, name the entry with a file or
  directory path instead.
- There is no `tauto check --workspace`.
- Shared dependencies are read once.
- Checking an outer workspace does not expand into every member of a nested
  workspace. Outer members and totes reached as their dependencies are in
  scope; nested siblings that are never depended on are not.
- Checking one member never triggers a check of the whole workspace by itself.
- `tauto dev` updates what it loads when dependency declarations change.

Manifests of the workspace root (and member manifests as needed for
affiliation and name resolution) may be read without making those totes check
targets.

## Relative paths with `..`

Affiliation paths, `workspace.parent`, `members` entries, and path
dependencies may use `..`. Leaving the depending tote's directory for that
reason alone is not an error.

## Git trees

The same affiliation and dependency rules apply inside a tree fetched for a
Git dependency.

Ordinary Git fetch takes and hashes the whole repository. `dir` selects which
tote to use; it does not confine readable paths to that directory. A tote at
`dir = "totes/a"` may set `workspace = "../.."`, depend on `b: workspace` or
`path = "../b"`, and load transitive members such as `c` inside that
repository.

References that resolve (after path and symlink resolution) outside the
fetched repository are refused. With `sparse = true`, fetch stays limited to
`dir` as today; needing the workspace root or sibling totes requires a
non-sparse fetch. Resolution never widens a sparse fetch.

## Lock

- The project lock is always the `Tauto.lock` beside the tote's **affiliated**
  workspace root. Starting in a nested root that declares `parent` still uses
  that parent's lock (following `parent` until there is none). A `parent` cycle
  is an error. Declaring `members` on a nested root does not switch the lock
  to that nested root.
- Workspace dependencies do not appear in `Tauto.lock` (same as path).
- Git dependencies reached through workspace or path edges still use the
  existing lock, verification, and adoption rules.
- Reaching another workspace as a dependency does not switch the lock in use.
- `check`, `run`, and `dev` never adopt an unlocked Git revision.

## Errors

| Situation | Result |
|---|---|
| `members` element that is a `Tauto.eure` file path | error |
| Absolute `members` / affiliation path, or empty path segment | error |
| Plain `members` path with missing tote, no affiliation, or other root | membership mismatch error |
| Illegal or unreadable affiliation (including syntax errors on the candidate) | error (not silent drop) |
| Duplicate `package.name` among members | error |
| `workspace.parent` cycle (self or A → … → A) | error |
| `NAME: workspace` with no such member, or from a non-member | error |
| Path, Git, and workspace combined on one entry | error |
| `--tote` that is a path, a non-member, another workspace's name, or used outside a workspace | error |
| Path or workspace edge that leaves a fetched Git tree | error |

## Examples

### Monorepo

```eure
# repository root Tauto.eure
workspace {
  members = [glob`totes/*`]
}
```

```eure
# totes/totebag-io/Tauto.eure
package {
  name = "totebag-io"
  version = "0.1.0"
}

workspace = "../.."

dependencies {
  index: workspace
  eure: workspace
  sha256: workspace
  totebag: workspace
  unicode: workspace
}
```

### Nested workspace under an outer member

```eure
# totes/vm/Tauto.eure — outer member and nested root; lock is ../.. 
package {
  name = "vm"
  version = "0.1.0"
}

workspace {
  parent = "../.."
  members = ["demo", "refusals"]
}
```

```eure
# totes/vm/demo/Tauto.eure
package { name = "demo", version = "0.1.0" }
workspace = ".."
```

An outer tote depends on `demo` with `demo { path = "totes/vm/demo" }` (or an
equivalent relative path). That does not make `refusals` a dependency.

### Game-style tree

```eure
# game-root/Tauto.eure
workspace {
  members = [
    "game",
    "engine",
    glob`plugins/*`,
  ]
}
```

```eure
# game/Tauto.eure
package { name = "game", version = "0.1.0" }
workspace = ".."
dependencies {
  engine: workspace
  fire: workspace
}
```

A plugin that should not belong simply omits affiliation to this root (and,
if listed only by a glob, is dropped; if listed by a plain path, that is a
mismatch error).

## Interaction with other “workspace” wording

Some documents call the outermost project directory a workspace when bounding
`include_text!` and `include-from` ([`macro.md`](macro.md),
[`macro-security.md`](macro-security.md)). That boundary is the project tree,
not this member set.
