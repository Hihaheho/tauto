# `tauto init` のメッセージ。

init-help =
    使い方: tauto init [PATH]
    `Tauto.eure` と `src/main.taut` を作る。既存のファイルは上書きしない。
    PATH を省くと現在のディレクトリになる。その親ディレクトリは存在しなければならない。
    ディレクトリ名には英小文字・数字・`-` を使い、英小文字で始める。
    依存の解決、バージョン管理、ツールの実行は行わない。
init-created = { $path } を作成した
init-run-hint = そのディレクトリで `tauto run --tote .` を実行する
init-failed = tauto init: { $error }
init-not-plain-directory = { $path } は通常のディレクトリではない
init-bad-path = PATH は空にできず、`..` を含められない
init-parent-missing = 親ディレクトリ { $path } が存在しない
init-no-name = ディレクトリからパッケージ名を決められない
init-bad-name = ディレクトリ名は英小文字で始め、英小文字・数字・`-` だけを使う必要がある
init-refuse-overwrite = { $path } は上書きしない
init-cleanup-failed = { $error }。作成したパスを片付けられなかった: { $paths }
