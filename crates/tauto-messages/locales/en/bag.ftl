# The messages of Totebag's commands: add, remove, update, lock, fetch, deps.

bag-help =
    usage: tauto add (--git URL [--branch NAME | --tag NAME] [--dir DIR] [--project ID] | --path DIR) [NAME] [--tote DIR]
    {"       "}tauto remove NAME [--tote DIR]
    {"       "}tauto update [NAME…] [--dry-run] [--tote DIR]
    {"       "}tauto lock [--check] [--tote DIR]
    {"       "}tauto fetch [--verify] [--tote DIR]
    {"       "}tauto deps [--tote DIR]
    {"       "}tauto audit [--json] [--tote DIR]

    {"  "}add      depend on a tote: write it in Tauto.eure, lock it and fetch it.
    {"           "}Without --branch or --tag, the repository's default branch; without
    {"           "}--dir, the tote at the repository's root or in the directory NAME;
    {"           "}without NAME, the tote's own name. --project names the project
    {"           "}its revisions are known as in the indexes Trust.eure trusts.
    {"  "}remove   no longer depend on NAME.
    {"  "}update   move the named Git dependencies (all without a name) to the newest
    {"           "}commit of their ref, and show what changed.
    {"  "}lock     lock the Git dependencies Tauto.lock does not have yet, and forget
    {"           "}the ones no longer used. --check changes nothing, uses no network,
    {"           "}and fails when Tauto.lock is not up to date.
    {"  "}fetch    fetch what Tauto.lock fixes. --verify reads the fetched trees again.
    {"  "}deps     show the totes the tote depends on.
    {"  "}audit    for the tote and each tote it depends on: the extern functions,
    {"           "}axioms and effects its sources declare, the host code it
    {"           "}brings (a Rust bridge and its crates, JavaScript sources), and
    {"           "}the commands it gives with what the project grants them. Read
    {"           "}from the files only; nothing is checked, run or fetched.

    With Trust.eure beside Tauto.eure, add, update and lock take a new commit
    only when the indexes it trusts allow it (see `tauto index --help`); update
    keeps a dependency at its locked commit until they do.

    The tote is the one in the current directory, or in --tote DIR. Fetched totes
    are kept in $TAUTO_TOTES (else ~/.cache/tauto/totes). check, run, build, test
    and doc fetch what Tauto.lock fixes when it is missing; --offline forbids it.
bag-unknown-command = unknown command { $name }
bag-failed = tauto { $name }: { $error }
bag-needs-value = { $flag } needs a value
bag-unknown-option = unknown option { $flag }
bag-no-manifest = no Tauto.eure in { $dir }; run this in a tote's directory, or name one with --tote DIR (`tauto init` makes one)
bag-add-one-name = add takes one NAME
bag-bad-name = { $name } is not a tote name (lowercase letters, digits and -, starting with a letter)
bag-already = { $name } is already a dependency; `tauto update { $name }` moves it to a newer commit, `tauto remove { $name }` drops it
bag-branch-and-tag = give --branch or --tag, not both
bag-fetching-ref = Fetching { $what } { $reference }
bag-fetching-rev = Fetching { $name } { $rev } from { $url }
bag-git-only-flags = --branch, --tag, --dir and --project are for --git
bag-path-no-manifest = { $path } has no Tauto.eure, seen from { $from }
bag-add-needs-source = add needs --git URL or --path DIR
bag-self = { $name } is this tote itself
bag-edit-unreadable = the edited Tauto.eure does not read back: { $error }
bag-added = Added { $name } to { $file }
bag-gives-commands = { $name } gives commands, run with no permissions until trust.commands in Tauto.eure grants them:
bag-url-no-manifest-in = { $url } has no Tauto.eure in { $dir }
bag-url-no-tote = { $url } has no tote (no Tauto.eure)
bag-url-many-totes = { $url } has { $n } totes; choose one with --dir: { $totes }
bag-remove-one-name = remove takes one NAME
bag-not-dependency = { $name } is not a dependency of { $tote }
bag-could-not-remove = could not take { $name } out of { $file }
bag-removed = Removed { $name } from { $file }
bag-not-git-dependency = { $name } is not a Git dependency of this tote
bag-lock-no-name = lock takes no NAME; `tauto update NAME` moves one
bag-lock-up-to-date = Tauto.lock is up to date
bag-lock-not-up-to-date = Tauto.lock is not up to date; run `tauto lock`
bag-fetch-no-name = fetch takes no NAME
bag-nothing-to-fetch = no Tauto.lock: nothing to fetch
bag-offline = the network is off (--offline)
bag-verified = { $name } { $id }: ok
bag-fetched = { $n } { $n ->
        [one] tote
       *[other] totes
    } fetched
bag-deps-no-name = deps takes no NAME
bag-deps-path = path { $path }
bag-deps-locked = { $url } { $reference } at { $rev }
bag-deps-not-fetched = { $url } { $reference } at { $rev }, not fetched
bag-deps-not-locked = { $url } { $reference }, not locked
bag-deps-entry = { $name } ({ $what })
bag-deps-entry-again = { $name } ({ $what }) (shown above)
bag-not-fetched = { $name } is not locked and fetched; run `tauto lock` and `tauto fetch` first
bag-report-up-to-date = Tauto.lock is up to date ({ $n } Git { $n ->
        [one] dependency
       *[other] dependencies
    })
# The words that start a line of the report, when it is done and when it
# would be (--dry-run). The report pads them to 9 columns.
bag-word-locked = Locked
bag-word-lock = lock
bag-word-moved = Moved
bag-word-move = move
bag-word-updated = Updated
bag-word-update = update
bag-word-unlocked = Unlocked
bag-word-unlock = unlock
bag-word-held = Held
bag-word-hold = hold
bag-word-to-lock = to lock
bag-report-source = source { $old } -> { $new }
bag-report-held = { $rev } may not be adopted yet
bag-report-dry-run = Tauto.lock would be changed ({ $n } { $n ->
        [one] change
       *[other] changes
    }); nothing was written
bag-path-leads-out = { $tote }: dependency { $name }: { $path } leads out of what was fetched
bag-path-error = { $tote }: dependency { $name }: { $path }: { $error }
bag-fetched-local = { $tote }: dependency { $name }: a fetched tote may not name a file:// repository
bag-dependency-of-error = dependency { $name } of { $tote }: { $error }
bag-dependency-error = dependency { $name }: { $error }
bag-wrong-name = { $tote } depends on { $name }, but the tote there is named { $found }
bag-the-directory = the directory { $path }
bag-asked-twice = { $name } is asked for twice, differently: { $first_by } asks for { $first }, { $by } for { $second }; a project has one { $name }
bag-locked-not-fetched = { $name } is locked but not fetched, and the network is off; run `tauto fetch`
bag-needs-network = { $name } needs the network to be locked, and it is off
bag-not-adopted =
    { $name } { $rev } may not be adopted under { $policy }:
    {"  "}{ $why }
    The indexes it trusts have to observe and accept it first; `tauto index --help`
    shows how to do that in your own.
bag-no-dependencies-block = Tauto.eure has no dependencies block
bag-not-in-block = { $name } is not written in the dependencies block
