# The messages of `tauto index new / observe / decide / withdraw / publish`
# and of `tauto publish-crates`.

publish-not-understood = { $command }: { $args } is not understood
publish-needs-reason = { $command } needs --reason TEXT: why, for whoever reads the index
publish-decide-takes = decide takes accept or reject
publish-valid-for = --valid-for { $value }: seconds, 1 to ten years
publish-no-name = publish takes no NAME
publish-git-needs-project = --git names a project with --project ID
publish-name-target = name a Git dependency, or a project with --project ID
publish-branch-or-tag = give --branch or --tag, not both
publish-branch-tag-need-git = --branch and --tag are for --git
publish-needs-value = { $flag } needs a value
publish-usage = usage: tauto index { $what }
publish-git-not-run = could not run git: { $error }
publish-not-empty = { $path } is not empty
publish-started = Started the index { $name } in { $path }
publish-trust-hint = To trust it, add this to Trust.eure (and name it in `observers` or `age_witnesses`):
publish-draft-invalid = the batch being written: { $error }
publish-draft-sequence = { $path } is numbered { $found }, but the next batch is { $next }
publish-no-policy = { $path } has no { $file }
publish-not-local-owned = { $alias } is not a local-owned index in { $file }
publish-no-local-owned = { $file } names no local-owned index; `tauto index new DIR` starts one
publish-several-local-owned = { $file } names several local-owned indexes; choose one with --index { $aliases }
publish-wrong-index = { $path } holds the index sha256:{ $id }, not the { $alias } Trust.eure names
publish-no-project = { $name } names no project; add `project = "sha256:…"` to it in Tauto.eure
publish-not-git = { $name } is not a Git dependency
publish-not-dependency = { $name } is not a dependency of { $package }
publish-not-locked = { $name } is not locked; `tauto lock` locks it
publish-observe-what = observe a project's commit with --git URL (and --branch or --tag), or a dependency by NAME
publish-fetching = Fetching { $url } { $reference }
publish-observed = Observed { $name } { $rev } (source { $source }) in the batch being written for { $alias }
publish-not-observed = { $alias } has not observed { $name }; `tauto index observe { $name }` first
publish-judged = { $what ->
        [accepted] Accepted
        [rejected] Rejected
       *[withdrew] Withdrew
    } { $name } { $rev } in the batch being written for { $alias }
publish-published = Published batch { $sequence } of { $alias } at { $rev } ({ $n ->
        [one] { $n } event
       *[other] { $n } events
    }), valid until { $until }

# `tauto publish-crates`

publish-crates-help =
    usage: tauto publish-crates plan --manifest-path Cargo.toml --registry NAME (--workspace | -p NAME...) --out PLAN
    {"       "}tauto publish-crates check PLAN
    {"       "}tauto publish-crates apply PLAN --confirm HASH
    {"       "}tauto publish-crates resume PLAN --confirm HASH
    plan is offline; check runs Cargo package/build scripts offline; apply uploads.
    Versions are unchanged. No commit, tag, push, yank, or automatic upload retry.
publish-crates-invalid-metadata = invalid release metadata: { $error }
publish-crates-not-regular = expected a regular file: { $path }
publish-crates-env-not-absolute = { $variable } must be an absolute path for release operations
publish-crates-tool-not-absolute = { $variable } must be an absolute path or a command name
publish-crates-cargo-failed = Cargo { $command } failed ({ $status }); output withheld because it may contain credentials or build-script secrets
publish-crates-checked = checked { $n } packages offline; no uploads. Confirmation hash: { $hash }
publish-crates-submitted-unknown = { $error }; release state is submitted-unknown; do not retry blindly
publish-crates-confirmed = Cargo confirmed { $n } packages to registry { $registry }; no version, tag, or Git ref changed
publish-crates-publish-false = { $name } has publish = false
publish-crates-registry-not-permitted = { $name } does not permit selected registry { $registry }
publish-crates-path-dependency = { $name } depends on a path outside the workspace
publish-crates-planned = planned { $n } packages for registry { $registry } using Cargo offline mode; no publish invocation.
    Review package file inventories in { $path }.
    Plan hash: { $hash }
    Run check before apply; check executes package build scripts.
publish-crates-release-metadata-exceeds-16-mib = release metadata exceeds 16 MiB
publish-crates-release-paths-must-be-nonempty = release paths must be nonempty, portable relative paths
publish-crates-package-and-registry-names-must = package and registry names must contain only letters, digits, '-' or '_'
publish-crates-path-entries-must-be-absolute = PATH entries must be absolute for release operations
publish-crates-cargo-config-includes-and-quoted = Cargo config includes and quoted/escaped keys are unsupported for release plans
publish-crates-invalid-snapshot-path = invalid snapshot path
publish-crates-snapshot-includes-a-credential-like = snapshot includes a credential-like file; exclude it from the release source
publish-crates-cannot-enumerate-tracked-release-files = cannot enumerate tracked release files
publish-crates-release-snapshots-do-not-accept = release snapshots do not accept symlinks or special files
publish-crates-source-checkout-must-be-clean = source checkout must be clean, including untracked files
publish-crates-release-directory-is-missing-or = release directory is missing or not a directory
publish-crates-unsupported-or-empty-release-plan = unsupported or empty release plan
publish-crates-source-root-must-be-absolute = source root must be absolute
publish-crates-duplicate-release-package = duplicate release package
publish-crates-active-workspace-cargo-configuration-is = active workspace Cargo configuration is not included in the snapshot
publish-crates-ancestor-cargo-configuration-outside-the = ancestor Cargo configuration outside the workspace is unsupported
publish-crates-snapshot-cannot-be-a-symlink = snapshot cannot be a symlink
publish-crates-snapshot-changed-create-and-review = snapshot changed; create and review a new plan
publish-crates-source-changed-since-planning-create = source changed since planning; create and review a new plan
publish-crates-cargo-identity-or-configuration-changed = Cargo identity or configuration changed since planning
publish-crates-cargo-package-inventory-differs-from = Cargo package inventory differs from the reviewed plan
publish-crates-package-output-directories-must-not = package output directories must not be symlinks or special files
publish-crates-verification-changed-the-snapshot-no = verification changed the snapshot; no upload is allowed
publish-crates-a-submitted-release-cannot-be = a submitted release cannot be reset by check
publish-crates-checked-plan-or-archive-changed = checked plan or archive changed; existing verification is not overwritten
publish-crates-confirm-must-equal-the-complete = {"-"}-confirm must equal the complete reviewed plan hash
publish-crates-checked-plan-hash-differs-no = checked plan hash differs; no upload is allowed
publish-crates-release-already-submitted-use-resume = release already submitted; use resume to inspect it
publish-crates-cargo-may-have-uploaded-some = Cargo may have uploaded some or all packages. Automatic retry is forbidden. Inspect the named registry read-only, compare package checksums, and prepare a separately reviewed plan for only proven-unsubmitted packages. Do not reset this journal.
publish-crates-packaged-artifacts-differ-from-check = packaged artifacts differ from check; no upload is allowed
publish-crates-cargo-returned-success-but-release = Cargo returned success but release contents changed; upload may have occurred. State remains submitted-unknown; inspect the registry.
publish-crates-duplicate-workspace = duplicate --workspace
publish-crates-duplicate-package-selection = duplicate package selection
publish-crates-select-exactly-one-of-workspace = select exactly one of --workspace or explicit -p packages
publish-crates-plan-or-release-directory-already = plan or release directory already exists; refusing to overwrite
publish-crates-write-the-release-plan-outside = write the release plan outside the source workspace
publish-crates-unsupported-package-version = unsupported package version
publish-crates-selected-package-is-not-a = selected package is not a workspace member
publish-crates-no-publishable-packages-selected = no publishable packages selected
publish-crates-planning-changed-workspace-files-no = planning changed workspace files; no plan was created
publish-crates-snapshot-package-inventory-differs-from = snapshot package inventory differs from source; no plan created
publish-crates-snapshot-copy-differs-from-source = snapshot copy differs from source; no plan created
publish-crates-path-is-required = PATH is required
publish-crates-cargo-executable-not-found = Cargo executable not found
publish-crates-release-environment-must-be-utf = release environment must be UTF-8
publish-crates-non-utf-8-release-path = non-UTF-8 release path
publish-crates-registry-is-required-no-implicit = {"-"}-registry is required; no implicit registry destination
publish-crates-plan-must-name-a-file = plan must name a file
publish-crates-manifest-has-no-parent = manifest has no parent
publish-crates-cargo-metadata-lacks-workspace-root = Cargo metadata lacks workspace root
publish-crates-missing-workspace-members = missing workspace members
publish-crates-missing-packages = missing packages
publish-crates-package-lacks-id = package lacks id
publish-crates-package-lacks-name = package lacks name
publish-crates-missing-package-dependencies = missing package dependencies
publish-crates-package-lacks-manifest = package lacks manifest
publish-crates-non-utf-8-manifest-path = non-UTF-8 manifest path
publish-crates-package-lacks-version = package lacks version
publish-crates-snapshot-path-lacks-parent = snapshot path lacks parent
publish-crates-invalid-cargo-identity = invalid Cargo identity
publish-crates-cargo-configuration-must-be-utf = Cargo configuration must be UTF-8
publish-crates-non-utf-8-tracked-path = non-UTF-8 tracked path
publish-crates-release-is-locked-an-interrupted = release is locked; an interrupted operation requires manual inspection before removing the lock
publish-crates-non-utf-8-package-inventory = non-UTF-8 package inventory
publish-crates-run-check-successfully-before-apply = run check successfully before apply
publish-crates-invalid-cargo-workspace-metadata = invalid Cargo workspace metadata
publish-crates-package-manifest-escapes-workspace = package manifest escapes workspace
publish-crates-manifest-is-outside-workspace = manifest is outside workspace
publish-crates-cargo-already-confirmed-this-release = Cargo already confirmed this release; no upload repeated
publish-crates-error = publish-crates: { $error }
