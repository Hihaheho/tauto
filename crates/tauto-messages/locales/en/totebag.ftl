# The messages of the totebag and totebag-index crates: fetching from Git,
# the cache, Tauto.lock, and the files and state of the distributed index.
# Paths, URLs, refs, IDs, keys and quoted values are passed as they are.

# One thing that went wrong at a place: a file, a key, a command.
totebag-at = { $place }: { $error }

# Fetching

totebag-locked-tree-differs = { $name }: the commit { $rev } of { $url } holds { $found }, but Tauto.lock says { $locked }
totebag-source-at-rev = { $source } at { $rev }: { $error }
totebag-no-directory = { $url } at { $rev } has no directory { $dir }
totebag-git-could-not-run = could not run git: { $error }
totebag-git-could-not-run-for = { $what }: could not run git: { $error }
totebag-asking-default-branch = asking { $url } for its default branch
totebag-no-default-branch = { $url } names no default branch; choose one with --branch or --tag
totebag-fetching = fetching { $source }
totebag-fetching-from = fetching { $reference } from { $url }
totebag-finding = finding { $name }
totebag-reading-commit = reading the commit { $rev }
totebag-no-commit = { $url } has no commit { $rev }
totebag-no-commit-because = { $url } has no commit { $rev } ({ $error })
totebag-ls-tree-no-path = git ls-tree: a line without a path
totebag-ls-tree-cannot-read = git ls-tree: cannot read { $head }
totebag-path-not-utf8 = { $place }: a path that is not UTF-8
totebag-name-not-utf8 = { $place }: a name that is not UTF-8
totebag-symbolic-link = { $path } is a symbolic link
totebag-submodule = { $path } is a submodule
totebag-not-regular-file = { $path } is not a regular file (mode { $mode })
totebag-not-file-or-directory = { $path } is not a regular file or directory
totebag-too-many-files = more than { $max } files
totebag-too-many-bytes = more than { $max } bytes
totebag-cat-file-blob-missing = git cat-file: a blob is missing
totebag-cat-file-not-a-size = git cat-file -s: not a size
totebag-cat-file-not-a-blob = git cat-file: not a blob, or more than { $max } bytes
totebag-cat-file-failed = git cat-file failed
totebag-writer-panicked = { $command }: the writer panicked
totebag-commit-hash-mismatch = the commit { $rev } does not hash to its ID
totebag-blob-too-large = the blob { $oid } is more than { $max } bytes
totebag-blob-hash-mismatch = the blob { $oid } does not hash to its ID

# The cache and source trees

totebag-no-cache-place = no place for fetched totes: set TAUTO_TOTES or HOME
totebag-written-tree-differs = the files written under { $dir } are not the tree { $id }
totebag-tree-changed = { $dir } was changed: it holds { $found }, not { $id }. Remove { $dir } and run the command again to fetch it anew
totebag-path-length = a path is 1 to 4096 bytes
totebag-path-characters = a path has no backslash or control character
totebag-path-relative = a path is relative
totebag-path-components = a path has no empty, . or .. component
totebag-path-twice = { $path } is in the tree twice
totebag-path-case-clash = { $other } and { $path } are one file where case is not told apart
totebag-file-and-directory = { $file } is a file and a directory of { $path }

# Where a tote comes from

totebag-bad-url = { $url } is not a Git URL a tote is fetched from: { $why }
totebag-url-characters = printable ASCII without spaces, quotes or backslashes, at most 2048 bytes
totebag-url-query = a query or fragment is not allowed
totebag-url-no-host = no host
totebag-url-credentials = credentials are not written in the URL
totebag-url-file-path = a file URL names an absolute path without ..
totebag-url-scheme = only https:// and file:/// are fetched
totebag-url-not-normal = the URL Standard writes this URL another way; write it as it is fetched
totebag-bad-ref = { $reference } is not a full ref (refs/heads/NAME or refs/tags/NAME)
totebag-bad-dir = { $dir } is not a directory in a repository (relative, letters, digits, . _ -)
totebag-bad-rev = { $rev } is not a full commit ID (sha1:<40 hex> or sha256:<64 hex>)
totebag-bad-git-rev = { $rev } is not a full commit ID
totebag-bad-source-id = { $id } is not a source ID (sha256:<64 hex>)

# Tauto.lock

totebag-lock-too-large = a lock is at most 4 MiB
totebag-lock-format = format is 1
totebag-lock-no-format = no format
totebag-lock-totes-list = totes is a list of `@ totes[]` blocks
totebag-locked-twice = { $name } is locked twice
totebag-unknown-key = unknown key { $key }
totebag-lock-unknown-key = unknown key { $key } in a locked tote
totebag-lock-missing = a locked tote has no { $key }
totebag-not-a-tote-name = { $name } is not a tote name
totebag-expected-block = expected a block
totebag-expected-text = expected a text

# Reading index files strictly

totebag-file-too-large = { $name }: more than { $max } bytes
totebag-file-not-utf8 = { $name }: not UTF-8
totebag-too-deep = nested more than { $max } levels
totebag-no-extension = an extension ($…) is not allowed
totebag-no-hole = a hole (!) is not a value
totebag-unread-value = only blocks, lists, texts and integers are read
totebag-is-a-block = { $what } is a block
totebag-key-is-a-name = { $what }: a key is a name
totebag-expected-quoted-text = expected a text "…"
totebag-integer-range = an integer from 0 below 2^64
totebag-expected-integer = expected an integer
totebag-too-many-items = more than { $max } items
totebag-expected-list = expected a list
totebag-has-no = { $what } has no { $key }
totebag-unknown-key-in = unknown key { $key } in { $what }
totebag-bad-sha256 = { $value } is not sha256:<64 lowercase hex>
totebag-bad-time = { $value } is not a UTC time YYYY-MM-DDTHH:MM:SSZ
totebag-too-many-seconds = { $n } seconds is more than ten years
totebag-bad-alias = { $value } is not an alias (lowercase letters, digits and -, starting with a letter)
totebag-reason-length = a reason is 1 to 4096 bytes
totebag-bad-package-rev = { $value } is not a revision (1 to 256 of A-Z a-z 0-9 . _ : + -)
totebag-index-https = { $value }: an index is fetched over https
totebag-index-branch = { $value }: an index is a branch, refs/heads/NAME
totebag-unknown-format = format { $format } is not known (1 is)
totebag-expected-value = { $value }: expected { $want }

# An index's history and batches

totebag-commit-no-tree = the commit { $rev } has no tree
totebag-root-not-regular = { $name } at { $rev } is not a regular file (mode { $mode })
totebag-history-too-long = the history is longer than { $max } commits
totebag-history-merge = { $rev } is a merge; an index's history is a line
totebag-object-format-differs = { $file } says its commits are { $said }, but they are { $found }
totebag-config-changed = { $file } changed at { $rev }
totebag-at-rev = at { $rev }: { $error }
totebag-root-not-empty = the root { $rev } does not hold an empty batch numbered 0
totebag-root-invalid = the root { $rev } is not a valid root
totebag-name-length = a name is 1 to 128 bytes
totebag-only-history = { $value }: the only history is "commit-batches"
totebag-not-object-format = { $value } is not sha1 or sha256
totebag-valid-until-early = { $file }: valid_until is not after issued_at
totebag-after-retirement = { $what }: nothing comes after a retirement
totebag-not-commit-of-format = { $value } is not a { $format } commit ID
totebag-not-verdict = { $value } is not accept or reject
totebag-not-event-kind = { $value } is not a kind of event

# Trust policies and the index state

totebag-one-rule = { $what }: a project has one rule
totebag-local-not-index = { $what }: local is this machine, not an index
totebag-not-transport = { $value } is not https or local-owned
totebag-local-owned-file = { $value }: a local-owned index is a file:/// repository
totebag-alias-twice = { $what }: the alias { $alias } is defined twice
totebag-index-twice = { $what }: sha256:{ $index } is already the index { $alias }
totebag-names-no-index = { $key } names at least one index
totebag-names-twice = { $key } names { $name } twice
totebag-limits-positive = max_checkpoint_lifetime_seconds and max_source_check_age_seconds are more than 0
totebag-no-such-index = no index is called { $alias }
totebag-local-does-not-observe = observers: local witnesses, it does not observe
totebag-witness-local-owned = age_witnesses: { $alias } is local-owned; a remote witness is read over https
totebag-witness-not-independent = age_witnesses: { $witness } is not independent of the observer { $observer }
totebag-user-changes-index = the index { $alias } (sha256:{ $index }) is read from { $url } { $reference } pinned at { $pin } here, and from { $project_url } { $project_reference } pinned at { $project_pin } as { $project_alias } in the project's policy; the user policy may add to it, not change it
totebag-user-alias-taken = the alias { $alias } is the index sha256:{ $index } in the project's policy; call sha256:{ $other } something else
totebag-rule-for = the rule for sha256:{ $project }: { $error }
totebag-state-index-twice = { $what }: the index is written twice
totebag-no-state-place = no place for the index state: set TAUTO_INDEX_STATE or HOME

# Syncing and evaluating

totebag-index-unused = { $alias } ({ $url }): { $error }; nothing from it is used
totebag-index-other-id = { $alias } ({ $url }) is the index sha256:{ $found }, not the sha256:{ $trusted } the policy trusts
totebag-pin-not-in-history = { $alias }: the history at { $head } does not hold the pinned checkpoint { $pin }
totebag-index-read-elsewhere = { $alias }: this machine reads the index from { $url } { $reference }, not { $other_url } { $other_reference }
totebag-clock-behind = the clock says { $now }, before the last evaluation at { $last }
totebag-clock-behind-adopting-nothing = the clock says { $now }, before the last evaluation at { $last }; adopting nothing until it is later

# Why a revision may not be adopted

totebag-why-not-taken-in = { $alias }: not taken in yet; run `tauto index sync`
totebag-why-stopped = { $alias }: stopped at { $rev }: { $why }
totebag-why-origin-unchecked = { $alias }: its origin has not been checked; run `tauto index sync`
totebag-why-origin-future = { $alias }: its origin was checked at { $time }, after now
totebag-why-origin-stale = { $alias }: its origin was checked { $ago } ago, more than the { $allowed } allowed; run `tauto index sync`
totebag-why-origin-ahead = { $alias }: its origin is at { $rev }, which was not taken in
totebag-why-retired = { $alias }: the index has retired
totebag-why-batch-not-valid-now = { $alias }: its latest batch is valid from { $from } until { $until }, not now; it has to publish again
totebag-why-batch-too-long = { $alias }: its latest batch is valid for { $valid }, longer than the { $allowed } allowed
totebag-why-withdrew = { $alias }: withdrew it
totebag-why-not-observed = { $alias }: has not observed it
totebag-why-not-decided = { $alias }: has not decided on it
totebag-why-rejected = { $alias }: rejected it
totebag-why-conflict = { $alias }: observed another source tree for it; this is a conflict
totebag-why-not-yet = { $who }: { $what } not yet
totebag-why-waits = { $who }: { $what } at { $time }; it waits until { $until }
totebag-this-machine = this machine
totebag-observed-it = observed it
totebag-has-had-record = has had { $alias }'s record of it
totebag-recorded-record = recorded { $alias }'s record of it
