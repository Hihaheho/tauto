# `trust.run`（`permission_file`）のメッセージ。

permissions-too-large = 権限ファイルは 1 MiB までである
permissions-expected-keys = `read = ["data"]` のようなキーが必要である
permissions-unknown-key = 未知のキー { $key }: キーは read、write、env、net、run、clipboard、div、all である
permissions-key-error = { $kind }: { $error }
permissions-true-names-nothing = { $kind } が `true` である。これは何も指さない
permissions-false-default = `false` は既定値である。キーごと省くこと
permissions-expected-texts = テキストのリストが必要である
permissions-bad-name = { $name } はフラグに書ける名前ではない
permissions-empty-list = 空のリストは何も許さない。キーごと省くこと
permissions-expected-value = `true` かテキストのリストが必要である

# 実行の開始時に尋ねる権限（`run_prompt`）。

run-prompt-title = { $path } の実行には次の権限が要る（+ はまだ許可していないもの）:
run-prompt-question = 許可するか? [a] 以後許可 / [y] 今回だけ許可 / [N] 実行しない:
run-prompt-no-terminal = 実行していない: 尋ねる端末がない。上の内容を確認し、この実行だけ許可するなら --yes を付けること
run-prompt-not-allowed = 許可されていない。何も実行していない
run-prompt-no-home = 答えを保存するホームフォルダがない。HOME か TAUTO_HOME を設定すること
run-prompt-kind-read = ファイルを読む
run-prompt-kind-write = ファイルを書く
run-prompt-kind-env = 環境変数を読む
run-prompt-kind-net = ネットワークにつなぐ
run-prompt-kind-run = 他のプログラムを起動する
run-prompt-kind-clipboard = クリップボードを読む
run-prompt-kind-div = ステップ上限なしで動かす
run-flag-removed = { $flag } はなくなった: 実行は effect が必要とする権限を開始時に尋ねる。尋ねずに許可するなら --yes を付けること
run-grant-needs-list = { $kind } は、プロジェクトの Tauto.eure の `trust.run` に書いた名前にだけ許される。そこに `{ $kind } = [...]` と書く
permissions-needs-list = { $kind } は書いたものにだけ許される。`{ $kind } = [...]` と書く
