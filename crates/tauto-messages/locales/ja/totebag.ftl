# totebag と totebag-index クレートのメッセージ：Git からの取得、キャッシュ、
# Tauto.lock、分散インデックスのファイルと状態。パス、URL、ref、ID、キー、
# 引用された値はそのまま渡される。

# ある場所（ファイル、キー、コマンド）で起きた一つの問題。
totebag-at = { $place }: { $error }

# 取得

totebag-locked-tree-differs = { $name }: { $url } のコミット { $rev } は { $found } を持つが、Tauto.lock は { $locked } としている
totebag-source-at-rev = { $rev } の { $source }: { $error }
totebag-no-directory = { $rev } の { $url } にディレクトリ { $dir } がない
totebag-git-could-not-run = git を実行できない: { $error }
totebag-git-could-not-run-for = { $what }: git を実行できない: { $error }
totebag-asking-default-branch = { $url } に既定のブランチを問い合わせ中
totebag-no-default-branch = { $url } は既定のブランチを示していない。--branch か --tag で選ぶこと
totebag-fetching = { $source } を取得中
totebag-fetching-from = { $url } から { $reference } を取得中
totebag-finding = { $name } を探索中
totebag-reading-commit = コミット { $rev } を読み込み中
totebag-no-commit = { $url } にコミット { $rev } がない
totebag-no-commit-because = { $url } にコミット { $rev } がない（{ $error }）
totebag-ls-tree-no-path = git ls-tree: パスのない行がある
totebag-ls-tree-cannot-read = git ls-tree: { $head } を読めない
totebag-path-not-utf8 = { $place }: UTF-8 でないパスがある
totebag-name-not-utf8 = { $place }: UTF-8 でない名前がある
totebag-symbolic-link = { $path } はシンボリックリンクである
totebag-submodule = { $path } はサブモジュールである
totebag-not-regular-file = { $path } は通常のファイルではない（モード { $mode }）
totebag-not-file-or-directory = { $path } は通常のファイルでもディレクトリでもない
totebag-too-many-files = ファイルが { $max } 個を超える
totebag-too-many-bytes = { $max } バイトを超える
totebag-cat-file-blob-missing = git cat-file: blob が欠けている
totebag-cat-file-not-a-size = git cat-file -s: サイズではない
totebag-cat-file-not-a-blob = git cat-file: blob でないか、{ $max } バイトを超える
totebag-cat-file-failed = git cat-file が失敗した
totebag-writer-panicked = { $command }: 書き込み側がパニックした
totebag-commit-hash-mismatch = コミット { $rev } のハッシュがその ID と一致しない
totebag-blob-too-large = blob { $oid } は { $max } バイトを超える
totebag-blob-hash-mismatch = blob { $oid } のハッシュがその ID と一致しない

# キャッシュとソースツリー

totebag-no-cache-place = 取得したトートの置き場所がない。TAUTO_TOTES か HOME を設定すること
totebag-written-tree-differs = { $dir } に書き込んだファイルがツリー { $id } と一致しない
totebag-tree-changed = { $dir } は変更されている。{ $id } ではなく { $found } を持つ。{ $dir } を削除してもう一度実行すれば、取得し直す
totebag-path-length = パスは 1 から 4096 バイトである
totebag-path-characters = パスにバックスラッシュや制御文字は使えない
totebag-path-relative = パスは相対パスである
totebag-path-components = パスに空の要素、. や .. は使えない
totebag-path-twice = { $path } がツリーに二度ある
totebag-path-case-clash = { $other } と { $path } は大文字と小文字を区別しないと同じファイルになる
totebag-file-and-directory = { $file } はファイルであり、{ $path } のディレクトリでもある

# トートの取得元

totebag-bad-url = { $url } はトートを取得する Git URL ではない: { $why }
totebag-url-characters = 空白・引用符・バックスラッシュを含まない印字可能な ASCII で、2048 バイト以下
totebag-url-query = クエリやフラグメントは使えない
totebag-url-no-host = ホストがない
totebag-url-credentials = 認証情報は URL に書かない
totebag-url-file-path = file URL は .. を含まない絶対パスを指す
totebag-url-scheme = 取得するのは https:// と file:/// だけである
totebag-url-not-normal = URL Standard ではこの URL を別の形に書く。取得される形で書く
totebag-bad-ref = { $reference } は完全な ref（refs/heads/NAME または refs/tags/NAME）ではない
totebag-bad-dir = { $dir } はリポジトリ内のディレクトリ（相対パス、英字、数字、. _ -）ではない
totebag-bad-rev = { $rev } は完全なコミット ID（sha1:<40 hex> または sha256:<64 hex>）ではない
totebag-bad-git-rev = { $rev } は完全なコミット ID ではない
totebag-bad-source-id = { $id } はソース ID（sha256:<64 hex>）ではない

# Tauto.lock

totebag-lock-too-large = ロックは 4 MiB 以下である
totebag-lock-format = format は 1 である
totebag-lock-no-format = format がない
totebag-lock-totes-list = totes は `@ totes[]` ブロックのリストである
totebag-locked-twice = { $name } が二度ロックされている
totebag-unknown-key = 不明なキー { $key }
totebag-lock-unknown-key = ロックされたトートに不明なキー { $key } がある
totebag-lock-missing = ロックされたトートに { $key } がない
totebag-not-a-tote-name = { $name } はトート名ではない
totebag-expected-block = ブロックが必要である
totebag-expected-text = テキストが必要である

# インデックスのファイルの厳密な読み込み

totebag-file-too-large = { $name }: { $max } バイトを超える
totebag-file-not-utf8 = { $name }: UTF-8 ではない
totebag-too-deep = 入れ子が { $max } 段を超える
totebag-no-extension = 拡張（$…）は使えない
totebag-no-hole = ホール（!）は値ではない
totebag-unread-value = 読むのはブロック、リスト、テキスト、整数だけである
totebag-is-a-block = { $what } はブロックである
totebag-key-is-a-name = { $what }: キーは名前である
totebag-expected-quoted-text = テキスト "…" が必要である
totebag-integer-range = 0 以上 2^64 未満の整数である
totebag-expected-integer = 整数が必要である
totebag-too-many-items = 要素が { $max } 個を超える
totebag-expected-list = リストが必要である
totebag-has-no = { $what } に { $key } がない
totebag-unknown-key-in = { $what } に不明なキー { $key } がある
totebag-bad-sha256 = { $value } は sha256:<64 lowercase hex> ではない
totebag-bad-time = { $value } は UTC 時刻 YYYY-MM-DDTHH:MM:SSZ ではない
totebag-too-many-seconds = { $n } 秒は十年を超える
totebag-bad-alias = { $value } は別名（小文字の英字、数字、- で、英字で始まる）ではない
totebag-reason-length = 理由は 1 から 4096 バイトである
totebag-bad-package-rev = { $value } はリビジョン（A-Z a-z 0-9 . _ : + - の 1 から 256 文字）ではない
totebag-index-https = { $value }: インデックスは https で取得する
totebag-index-branch = { $value }: インデックスはブランチ refs/heads/NAME である
totebag-unknown-format = format { $format } は不明である（1 なら分かる）
totebag-expected-value = { $value }: { $want } が必要である

# インデックスの履歴とバッチ

totebag-commit-no-tree = コミット { $rev } にツリーがない
totebag-root-not-regular = { $rev } の { $name } は通常のファイルではない（モード { $mode }）
totebag-history-too-long = 履歴が { $max } コミットより長い
totebag-history-merge = { $rev } はマージである。インデックスの履歴は一直線である
totebag-object-format-differs = { $file } はコミットが { $said } だとしているが、実際は { $found } である
totebag-config-changed = { $file } が { $rev } で変わっている
totebag-at-rev = { $rev }: { $error }
totebag-root-not-empty = ルート { $rev } は番号 0 の空のバッチを持たない
totebag-root-invalid = ルート { $rev } は正しいルートではない
totebag-name-length = 名前は 1 から 128 バイトである
totebag-only-history = { $value }: 履歴は "commit-batches" だけである
totebag-not-object-format = { $value } は sha1 でも sha256 でもない
totebag-valid-until-early = { $file }: valid_until が issued_at より後ではない
totebag-after-retirement = { $what }: 引退の後には何も来ない
totebag-not-commit-of-format = { $value } は { $format } のコミット ID ではない
totebag-not-verdict = { $value } は accept でも reject でもない
totebag-not-event-kind = { $value } はイベントの種類ではない

# 信頼ポリシーとインデックスの状態

totebag-one-rule = { $what }: 一つのプロジェクトに規則は一つである
totebag-local-not-index = { $what }: local はこのマシンであり、インデックスではない
totebag-not-transport = { $value } は https でも local-owned でもない
totebag-local-owned-file = { $value }: local-owned のインデックスは file:/// のリポジトリである
totebag-alias-twice = { $what }: 別名 { $alias } が二度定義されている
totebag-index-twice = { $what }: sha256:{ $index } はすでにインデックス { $alias } である
totebag-names-no-index = { $key } はインデックスを少なくとも一つ挙げる
totebag-names-twice = { $key } が { $name } を二度挙げている
totebag-limits-positive = max_checkpoint_lifetime_seconds と max_source_check_age_seconds は 0 より大きい
totebag-no-such-index = { $alias } というインデックスはない
totebag-local-does-not-observe = observers: local は証人であり、観測はしない
totebag-witness-local-owned = age_witnesses: { $alias } は local-owned である。リモートの証人は https で読む
totebag-witness-not-independent = age_witnesses: { $witness } は観測者 { $observer } から独立していない
totebag-user-changes-index = インデックス { $alias }（sha256:{ $index }）は、ここでは { $url } { $reference } から読まれ { $pin } にピン留めされているが、プロジェクトのポリシーでは { $project_alias } として { $project_url } { $project_reference } から読まれ { $project_pin } にピン留めされている。ユーザーポリシーはそれに追加できるが、変えることはできない
totebag-user-alias-taken = 別名 { $alias } はプロジェクトのポリシーではインデックス sha256:{ $index } である。sha256:{ $other } には別の名前を付けること
totebag-rule-for = sha256:{ $project } の規則: { $error }
totebag-state-index-twice = { $what }: インデックスが二度書かれている
totebag-no-state-place = インデックスの状態の置き場所がない。TAUTO_INDEX_STATE か HOME を設定すること

# 同期と評価

totebag-index-unused = { $alias }（{ $url }）: { $error }。ここからは何も使わない
totebag-index-other-id = { $alias }（{ $url }）はインデックス sha256:{ $found } であり、ポリシーが信頼する sha256:{ $trusted } ではない
totebag-pin-not-in-history = { $alias }: { $head } の履歴はピン留めされたチェックポイント { $pin } を含まない
totebag-index-read-elsewhere = { $alias }: このマシンはインデックスを { $other_url } { $other_reference } ではなく { $url } { $reference } から読んでいる
totebag-clock-behind = 時計は { $now } を示しており、前回の評価 { $last } より前である
totebag-clock-behind-adopting-nothing = 時計は { $now } を示しており、前回の評価 { $last } より前である。それより後になるまで何も採用しない

# リビジョンを採用できない理由

totebag-why-not-taken-in = { $alias }: まだ取り込まれていない。`tauto index sync` を実行すること
totebag-why-stopped = { $alias }: { $rev } で止まっている: { $why }
totebag-why-origin-unchecked = { $alias }: origin がまだ確かめられていない。`tauto index sync` を実行すること
totebag-why-origin-future = { $alias }: origin を確かめた時刻 { $time } が現在より後である
totebag-why-origin-stale = { $alias }: origin を確かめたのは { $ago } 前で、許される { $allowed } を超える。`tauto index sync` を実行すること
totebag-why-origin-ahead = { $alias }: origin は { $rev } にあり、それは取り込まれていない
totebag-why-retired = { $alias }: インデックスは引退した
totebag-why-batch-not-valid-now = { $alias }: 最新のバッチは { $from } から { $until } まで有効で、現在は有効でない。公開し直す必要がある
totebag-why-batch-too-long = { $alias }: 最新のバッチの有効期間 { $valid } が許される { $allowed } より長い
totebag-why-withdrew = { $alias }: 取り下げた
totebag-why-not-observed = { $alias }: まだ観測していない
totebag-why-not-decided = { $alias }: まだ判断していない
totebag-why-rejected = { $alias }: 却下した
totebag-why-conflict = { $alias }: 別のソースツリーを観測している。これは衝突である
totebag-why-not-yet = { $who }: { $what }ことはまだない
totebag-why-waits = { $who }: { $time } に{ $what }。{ $until } まで待つ
totebag-this-machine = このマシン
totebag-observed-it = 観測した
totebag-has-had-record = { $alias } の記録を持った
totebag-recorded-record = { $alias } の記録を記録した
