# `tauto index new / observe / decide / withdraw / publish` と
# `tauto publish-crates` のメッセージ。

publish-not-understood = { $command }: { $args } は解釈できない
publish-needs-reason = { $command } には --reason TEXT が要る。索引を読む人のための理由である
publish-decide-takes = decide には accept か reject を与える
publish-valid-for = --valid-for { $value }: 1 秒から 10 年までの秒数を与える
publish-no-name = publish は NAME を取らない
publish-git-needs-project = --git は --project ID でプロジェクトを指定するときに使う
publish-name-target = Git 依存の名前か、--project ID でプロジェクトを指定する
publish-branch-or-tag = --branch と --tag はどちらか一方だけを与える
publish-branch-tag-need-git = --branch と --tag は --git とともに使う
publish-needs-value = { $flag } には値が要る
publish-usage = 使い方: tauto index { $what }
publish-git-not-run = git を実行できない: { $error }
publish-not-empty = { $path } は空ではない
publish-started = 索引 { $name } を { $path } に作成した
publish-trust-hint = 信頼するには、次を Trust.eure に加える（`observers` か `age_witnesses` にも名前を挙げる）:
publish-draft-invalid = 書きかけのバッチ: { $error }
publish-draft-sequence = { $path } の番号は { $found } だが、次のバッチは { $next } である
publish-no-policy = { $path } に { $file } がない
publish-not-local-owned = { $alias } は { $file } の local-owned な索引ではない
publish-no-local-owned = { $file } に local-owned な索引がない。`tauto index new DIR` で作成できる
publish-several-local-owned = { $file } に local-owned な索引が複数ある。--index { $aliases } で一つを選ぶ
publish-wrong-index = { $path } の索引は sha256:{ $id } であり、Trust.eure の { $alias } ではない
publish-no-project = { $name } にプロジェクトがない。Tauto.eure のその依存に `project = "sha256:…"` を加える
publish-not-git = { $name } は Git 依存ではない
publish-not-dependency = { $name } は { $package } の依存ではない
publish-not-locked = { $name } はロックされていない。`tauto lock` でロックできる
publish-observe-what = プロジェクトのコミットは --git URL（と --branch か --tag）で、依存は NAME で観測する
publish-fetching = { $url } { $reference } を取得中
publish-observed = { $name } { $rev }（ソース { $source }）を { $alias } の書きかけのバッチに観測として加えた
publish-not-observed = { $alias } は { $name } をまだ観測していない。先に `tauto index observe { $name }` を実行する
publish-judged = { $name } { $rev } の{ $what ->
        [accepted] 受理
        [rejected] 却下
       *[withdrew] 取り下げ
    }を { $alias } の書きかけのバッチに加えた
publish-published = { $alias } のバッチ { $sequence } を { $rev } に公開した（イベント { $n } 件）。有効期限は { $until }

# `tauto publish-crates`

publish-crates-help =
    使い方: tauto publish-crates plan --manifest-path Cargo.toml --registry NAME (--workspace | -p NAME...) --out PLAN
    {"       "}tauto publish-crates check PLAN
    {"       "}tauto publish-crates apply PLAN --confirm HASH
    {"       "}tauto publish-crates resume PLAN --confirm HASH
    plan はオフラインで動く。check は Cargo の package とビルドスクリプトをオフラインで実行する。apply がアップロードする。
    バージョンは変えない。コミット、タグ、push、yank、アップロードの自動再試行はしない。
publish-crates-invalid-metadata = リリースのメタデータが不正: { $error }
publish-crates-not-regular = 通常のファイルでない: { $path }
publish-crates-env-not-absolute = リリース操作では { $variable } が絶対パスでなければならない
publish-crates-tool-not-absolute = { $variable } は絶対パスかコマンド名でなければならない
publish-crates-cargo-failed = Cargo { $command } が失敗した（{ $status }）。認証情報やビルドスクリプトの秘密を含みうるので出力は表示しない
publish-crates-checked = { $n } 個のパッケージをオフラインで検査した。アップロードはしていない。確認用ハッシュ: { $hash }
publish-crates-submitted-unknown = { $error }。リリースの状態は submitted-unknown である。やみくもに再試行しないこと
publish-crates-confirmed = Cargo がレジストリ { $registry } への { $n } 個のパッケージを確認した。バージョン、タグ、Git の ref は変えていない
publish-crates-publish-false = { $name } は publish = false である
publish-crates-registry-not-permitted = { $name } は選択したレジストリ { $registry } を許可していない
publish-crates-path-dependency = { $name } はワークスペース外のパスに依存している
publish-crates-planned = Cargo のオフラインモードで、レジストリ { $registry } 向けに { $n } 個のパッケージを計画した。publish は呼んでいない。
    パッケージのファイル一覧を { $path } で確認すること。
    計画ハッシュ: { $hash }
    apply の前に check を実行すること。check はパッケージのビルドスクリプトを実行する。
publish-crates-release-metadata-exceeds-16-mib = リリースのメタデータが 16 MiB を超えている
publish-crates-release-paths-must-be-nonempty = リリースのパスは空でない、移植可能な相対パスでなければならない
publish-crates-package-and-registry-names-must = パッケージ名とレジストリ名に使えるのは英字、数字、'-'、'_' だけである
publish-crates-path-entries-must-be-absolute = リリース操作では PATH の各要素が絶対パスでなければならない
publish-crates-cargo-config-includes-and-quoted = リリース計画では Cargo 設定の include と、引用符やエスケープを含むキーに対応していない
publish-crates-invalid-snapshot-path = スナップショットのパスが不正
publish-crates-snapshot-includes-a-credential-like = スナップショットに認証情報らしいファイルがある。リリースのソースから除外すること
publish-crates-cannot-enumerate-tracked-release-files = 追跡されているリリースファイルを列挙できない
publish-crates-release-snapshots-do-not-accept = リリースのスナップショットにはシンボリックリンクや特殊ファイルを含められない
publish-crates-source-checkout-must-be-clean = ソースのチェックアウトは、追跡外のファイルも含めてクリーンでなければならない
publish-crates-release-directory-is-missing-or = リリースディレクトリがないか、ディレクトリではない
publish-crates-unsupported-or-empty-release-plan = 未対応または空のリリース計画
publish-crates-source-root-must-be-absolute = ソースのルートは絶対パスでなければならない
publish-crates-duplicate-release-package = リリースパッケージが重複している
publish-crates-active-workspace-cargo-configuration-is = 有効なワークスペースの Cargo 設定がスナップショットに含まれていない
publish-crates-ancestor-cargo-configuration-outside-the = ワークスペース外の祖先ディレクトリにある Cargo 設定には対応していない
publish-crates-snapshot-cannot-be-a-symlink = スナップショットはシンボリックリンクであってはならない
publish-crates-snapshot-changed-create-and-review = スナップショットが変わった。新しい計画を作成して確認すること
publish-crates-source-changed-since-planning-create = 計画後にソースが変わった。新しい計画を作成して確認すること
publish-crates-cargo-identity-or-configuration-changed = 計画後に Cargo の実体か設定が変わった
publish-crates-cargo-package-inventory-differs-from = Cargo のパッケージ内容が確認済みの計画と異なる
publish-crates-package-output-directories-must-not = パッケージの出力ディレクトリはシンボリックリンクや特殊ファイルであってはならない
publish-crates-verification-changed-the-snapshot-no = 検証でスナップショットが変わった。アップロードは許されない
publish-crates-a-submitted-release-cannot-be = 提出済みのリリースは check でリセットできない
publish-crates-checked-plan-or-archive-changed = 検査済みの計画かアーカイブが変わった。既存の検証は上書きしない
publish-crates-confirm-must-equal-the-complete = {"-"}-confirm には確認済みの計画ハッシュ全体を与える
publish-crates-checked-plan-hash-differs-no = 検査済みの計画ハッシュが異なる。アップロードは許されない
publish-crates-release-already-submitted-use-resume = リリースは提出済みである。resume で状態を確認すること
publish-crates-cargo-may-have-uploaded-some = Cargo がパッケージの一部または全部をアップロードした可能性がある。自動の再試行は禁止である。指定したレジストリを読み取り専用で調べ、パッケージのチェックサムを比べ、未提出と確かめられたパッケージだけについて別途確認した計画を用意すること。このジャーナルはリセットしないこと。
publish-crates-packaged-artifacts-differ-from-check = パッケージ化した成果物が check のときと異なる。アップロードは許されない
publish-crates-cargo-returned-success-but-release = Cargo は成功を返したが、リリースの内容が変わった。アップロードされた可能性がある。状態は submitted-unknown のままである。レジストリを調べること。
publish-crates-duplicate-workspace = {"-"}-workspace が重複している
publish-crates-duplicate-package-selection = パッケージの選択が重複している
publish-crates-select-exactly-one-of-workspace = {"-"}-workspace か、-p によるパッケージ指定のどちらか一方だけを選ぶ
publish-crates-plan-or-release-directory-already = 計画かリリースディレクトリがすでに存在する。上書きはしない
publish-crates-write-the-release-plan-outside = リリース計画はソースのワークスペースの外に書くこと
publish-crates-unsupported-package-version = 未対応のパッケージバージョン
publish-crates-selected-package-is-not-a = 選択したパッケージはワークスペースのメンバーではない
publish-crates-no-publishable-packages-selected = 公開できるパッケージが選択されていない
publish-crates-planning-changed-workspace-files-no = 計画中にワークスペースのファイルが変わった。計画は作成していない
publish-crates-snapshot-package-inventory-differs-from = スナップショットのパッケージ内容がソースと異なる。計画は作成していない
publish-crates-snapshot-copy-differs-from-source = スナップショットの複製がソースと異なる。計画は作成していない
publish-crates-path-is-required = PATH が必要である
publish-crates-cargo-executable-not-found = Cargo の実行ファイルが見つからない
publish-crates-release-environment-must-be-utf = リリースの環境変数は UTF-8 でなければならない
publish-crates-non-utf-8-release-path = UTF-8 でないリリースのパス
publish-crates-registry-is-required-no-implicit = {"-"}-registry が必要である。暗黙の公開先レジストリはない
publish-crates-plan-must-name-a-file = 計画にはファイルを指定する
publish-crates-manifest-has-no-parent = マニフェストに親ディレクトリがない
publish-crates-cargo-metadata-lacks-workspace-root = Cargo のメタデータにワークスペースのルートがない
publish-crates-missing-workspace-members = ワークスペースのメンバーがない
publish-crates-missing-packages = パッケージがない
publish-crates-package-lacks-id = パッケージに id がない
publish-crates-package-lacks-name = パッケージに名前がない
publish-crates-missing-package-dependencies = パッケージの依存がない
publish-crates-package-lacks-manifest = パッケージにマニフェストがない
publish-crates-non-utf-8-manifest-path = UTF-8 でないマニフェストのパス
publish-crates-package-lacks-version = パッケージにバージョンがない
publish-crates-snapshot-path-lacks-parent = スナップショットのパスに親ディレクトリがない
publish-crates-invalid-cargo-identity = Cargo の実体情報が不正
publish-crates-cargo-configuration-must-be-utf = Cargo の設定は UTF-8 でなければならない
publish-crates-non-utf-8-tracked-path = UTF-8 でない追跡パス
publish-crates-release-is-locked-an-interrupted = リリースはロックされている。中断された操作があるので、ロックを外す前に手作業で確認すること
publish-crates-non-utf-8-package-inventory = UTF-8 でないパッケージ内容
publish-crates-run-check-successfully-before-apply = apply の前に check を成功させること
publish-crates-invalid-cargo-workspace-metadata = Cargo のワークスペースのメタデータが不正
publish-crates-package-manifest-escapes-workspace = パッケージのマニフェストがワークスペースの外にある
publish-crates-manifest-is-outside-workspace = マニフェストがワークスペースの外にある
publish-crates-cargo-already-confirmed-this-release = Cargo はこのリリースをすでに確認済みである。アップロードは繰り返さない
publish-crates-error = publish-crates: エラー: { $error }
