# Totebag のコマンド（add, remove, update, lock, fetch, deps）のメッセージ。

bag-help =
    使い方: tauto add (--git URL [--branch NAME | --tag NAME] [--dir DIR] [--project ID] | --path DIR) [NAME] [--tote DIR]
    {"       "}tauto remove NAME [--tote DIR]
    {"       "}tauto update [NAME…] [--dry-run] [--tote DIR]
    {"       "}tauto lock [--check] [--tote DIR]
    {"       "}tauto fetch [--verify] [--tote DIR]
    {"       "}tauto deps [--tote DIR]
    {"       "}tauto audit [--json] [--tote DIR]

    {"  "}add      トートに依存する。`Tauto.eure` に書き、ロックし、取得する。
    {"           "}--branch も --tag もなければリポジトリの既定ブランチ。--dir が
    {"           "}なければリポジトリのルートか、ディレクトリ NAME にあるトート。
    {"           "}NAME がなければトート自身の名前。--project は、`Trust.eure` が
    {"           "}信頼するインデックスでそのリビジョンが知られているプロジェクトを指す。
    {"  "}remove   NAME への依存をやめる。
    {"  "}update   指定した Git 依存（名前がなければすべて）を ref の最新コミットへ
    {"           "}進め、変わったものを示す。
    {"  "}lock     `Tauto.lock` にまだない Git 依存をロックし、使われなくなったものを
    {"           "}外す。--check は何も変えず、ネットワークを使わず、`Tauto.lock` が
    {"           "}最新でなければ失敗する。
    {"  "}fetch    `Tauto.lock` が固定するものを取得する。--verify は取得したツリーを読み直す。
    {"  "}deps     トートが依存するトートを示す。
    {"  "}audit    トートとその依存の各トートについて、ソースが宣言する extern 関数・
    {"           "}公理・効果、持ち込むホストコード（Rust ブリッジとそのクレート、
    {"           "}JavaScript ソース）、与えるコマンドとプロジェクトがそれに与える許可を
    {"           "}示す。ファイルを読むだけで、検査も実行も取得もしない。

    `Tauto.eure` の隣に `Trust.eure` があれば、add, update, lock は、それが信頼する
    インデックスが認めたときだけ新しいコミットを取る（`tauto index --help` を参照）。
    update は、認められるまで依存をロック済みのコミットに留める。

    対象のトートは現在のディレクトリか --tote DIR にあるもの。取得したトートは
    $TAUTO_TOTES（なければ ~/.cache/tauto/totes）に置かれる。check, run, build, test,
    doc は `Tauto.lock` が固定するものがなければ取得する。--offline はこれを禁じる。
bag-unknown-command = 不明なコマンド { $name }
bag-failed = tauto { $name }: { $error }
bag-needs-value = { $flag } には値が必要である
bag-unknown-option = 不明なオプション { $flag }
bag-no-manifest = { $dir } に `Tauto.eure` がない。トートのディレクトリで実行するか、--tote DIR で指定する（`tauto init` で作れる）
bag-add-one-name = add が取る NAME はひとつだけである
bag-bad-name = { $name } はトート名ではない（英小文字・数字・`-` を使い、英小文字で始める）
bag-already = { $name } はすでに依存である。`tauto update { $name }` で新しいコミットへ進め、`tauto remove { $name }` で外せる
bag-branch-and-tag = --branch と --tag はどちらかひとつを指定する
bag-fetching-ref = { $what } { $reference } を取得中
bag-fetching-rev = { $name } { $rev } を { $url } から取得中
bag-git-only-flags = --branch, --tag, --dir, --project は --git 用である
bag-path-no-manifest = { $from } から見た { $path } に `Tauto.eure` がない
bag-add-needs-source = add には --git URL か --path DIR が必要である
bag-self = { $name } はこのトート自身である
bag-edit-unreadable = 編集した `Tauto.eure` を読み直せない: { $error }
bag-added = { $name } を { $file } に追加した
bag-gives-commands = { $name } はコマンドを与える。`Tauto.eure` の `trust.commands` が許可するまで、権限なしで実行される:
bag-url-no-manifest-in = { $url } の { $dir } に `Tauto.eure` がない
bag-url-no-tote = { $url } にトートがない（`Tauto.eure` がない）
bag-url-many-totes = { $url } には { $n } 個のトートがある。--dir でひとつを選ぶ: { $totes }
bag-remove-one-name = remove が取る NAME はひとつだけである
bag-not-dependency = { $name } は { $tote } の依存ではない
bag-could-not-remove = { $file } から { $name } を外せなかった
bag-removed = { $name } を { $file } から外した
bag-not-git-dependency = { $name } はこのトートの Git 依存ではない
bag-lock-no-name = lock は NAME を取らない。ひとつを進めるには `tauto update NAME` を使う
bag-lock-up-to-date = `Tauto.lock` は最新である
bag-lock-not-up-to-date = `Tauto.lock` が最新でない。`tauto lock` を実行する
bag-fetch-no-name = fetch は NAME を取らない
bag-nothing-to-fetch = `Tauto.lock` がない。取得するものはない
bag-offline = ネットワークがオフである（--offline）
bag-verified = { $name } { $id }: ok
bag-fetched = { $n } 個のトートを取得した
bag-deps-no-name = deps は NAME を取らない
bag-deps-path = パス { $path }
bag-deps-locked = { $url } { $reference } の { $rev }
bag-deps-not-fetched = { $url } { $reference } の { $rev }、未取得
bag-deps-not-locked = { $url } { $reference }、未ロック
bag-deps-entry = { $name }（{ $what }）
bag-deps-entry-again = { $name }（{ $what }）（上に示した）
bag-not-fetched = { $name } はロックも取得もされていない。先に `tauto lock` と `tauto fetch` を実行する
bag-report-up-to-date = `Tauto.lock` は最新である（Git 依存 { $n } 個）
bag-word-locked = ロック
bag-word-lock = ロック予定
bag-word-moved = 移動
bag-word-move = 移動予定
bag-word-updated = 更新
bag-word-update = 更新予定
bag-word-unlocked = 解除
bag-word-unlock = 解除予定
bag-word-held = 保留
bag-word-hold = 保留予定
bag-word-to-lock = 要ロック
bag-report-source = ソース { $old } -> { $new }
bag-report-held = { $rev } はまだ採用できない
bag-report-dry-run = `Tauto.lock` は変わる（{ $n } 件）。何も書き込んでいない
bag-path-leads-out = { $tote }: 依存 { $name }: { $path } は取得したものの外を指す
bag-path-error = { $tote }: 依存 { $name }: { $path }: { $error }
bag-fetched-local = { $tote }: 依存 { $name }: 取得したトートは file:// のリポジトリを指せない
bag-dependency-of-error = { $tote } の依存 { $name }: { $error }
bag-dependency-error = 依存 { $name }: { $error }
bag-wrong-name = { $tote } は { $name } に依存するが、そこにあるトートの名前は { $found } である
bag-the-directory = ディレクトリ { $path }
bag-asked-twice = { $name } が異なる形で二度求められている: { $first_by } は { $first } を、{ $by } は { $second } を求める。プロジェクトに { $name } はひとつしか置けない
bag-locked-not-fetched = { $name } はロック済みだが未取得で、ネットワークはオフである。`tauto fetch` を実行する
bag-needs-network = { $name } のロックにはネットワークが必要だが、オフである
bag-not-adopted =
    { $name } { $rev } は { $policy } のもとでは採用できない:
    {"  "}{ $why }
    信頼するインデックスが先にそれを観測し、受け入れる必要がある。自分のインデックスでの
    やり方は `tauto index --help` が示す。
bag-no-dependencies-block = `Tauto.eure` に dependencies ブロックがない
bag-not-in-block = { $name } は dependencies ブロックに書かれていない
