# Tote commands (`tauto NAME`)

A tote can declare named entry points in `Tauto.eure`. Commands of the
project and its direct dependencies run as `tauto NAME ARGS…`: checked like
`tauto run`, run on the machine written in Tauto (`totes/vm`), with no host permissions unless the
project's `trust.commands` grants them.

## Declaring

```eure
commands {
  bk {
    main = "cmd/bk.taut"
    about = "Scaffold an app and run the dev server"
  }
}
```

- Names follow tote naming (lowercase, digits, `-`, starting with a letter).
- `main` is a `.taut`/`.tauto` file of this tote, written from its root
  without `.` or `..`, and outside its sources (`src`,
  `package.additional-sources`), so dependents never load it.
- `about` is one line shown by `tauto --help` and `tauto audit`.
- Required permissions are derived from the effect row, not written.

`main` is a program with top-level statements, resolved against the tote's
sources and dependencies. Every source of the tote is checked, and only what
`main` reaches is extracted to run, as for the files an import reads: a proof
of the tote that the command does not use is not on its path. All arguments after `NAME` are `argv()`. The working
directory is where `tauto` was run; `--offline` and `--fresh` before `NAME`
belong to `tauto`.

## Resolution

1. Built-in commands always win (`tauto --help` flags shadowed ones).
2. The tote named by the project's `trust.commands.NAME.tote` (an error if it
   lacks the command).
3. The project's own commands.
4. Direct dependencies' commands; a name in two totes is an error asking for
   `trust.commands`.

Transitive dependencies contribute nothing. The project is the nearest
`Tauto.eure` above the working directory.

## Permissions

```eure
trust {
  commands {
    bk {
      tote = "myapp"
      read = ["src", "public"]
      write = ["dist"]
      net = ["127.0.0.1:3000"]
    }
  }
}
```

- The grant binds the pair of `tote` (required) and command name.
- Other keys mean what they mean in `trust.run`
  ([`host-effects.md`](host-effects.md)): `read`, `write`, `env`, `net`, `run`,
  `clipboard`, each `true` or a list; `all` is not accepted. Relative paths are
  from the manifest's directory.
- Only the project's `trust` counts: a command is not asked about at its
  start, and every argument after its name is the command's own, so widening
  a grant means changing the committed manifest. The project's own commands are granted the same way.
- The project's `trust` section is approved as for `tauto run` before the
  command is granted anything, and the grant is read from the same text that
  was approved (`tauto --approve-trust NAME` approves without asking).

After checking, the permission kinds the command's row needs (as in
`tauto run`) must all be granted, or it fails before running and prints the
`trust.commands` entry to add. Scopes come only from the grant; requests
outside them return `Err(Denied(..))` with no prompt. Externs in the command's
tote need the project's `trust.extern` as for any dependency. Command code is
pinned by `Tauto.lock` ([`totebag.md`](totebag.md)).

## Running

`tauto NAME` is `tauto run` with the command's `main` as entry: dependencies
come from the project's lock (which is not changed); only the tote's sources,
its dependencies and `main` are read (the project's sources only for its own
commands); everything is checked (no holes); output is written immediately;
there is no step limit; the exit status is `exit`'s value.
`tauto check --tote DIR` also checks each command's `main` and its
declaration.

## Discovery

Without running or fetching anything: `tauto --help` lists project commands
with tote, `about` and status (granted kinds, collisions, shadowed);
`tauto audit [--json]` lists each tote's `commands` with granted kinds;
`tauto add` lists the added tote's commands. `tauto NAME --help` goes to the
command.

## Undecided

- Running commands from a Rust build (cache location and key, Rust crate
  dependencies).
- `tauto update` reporting newly required permission kinds.
- Renaming colliding commands (today: wrap one in a project command).
- Locks and grants for tools used outside a project.
- Restarting commands on change, as `tauto dev` does.
