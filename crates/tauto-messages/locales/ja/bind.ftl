# `tauto bind` (`tauto-bind`). The report it writes stays in English.

bind-unexpected = tauto bind: 予期しない引数 { $arg }
bind-usage = 使い方: { $usage }
bind-crate-mismatch = { $file }: crate は { $found } であり、{ $wanted } ではない
bind-format-version = エラー: rustdoc JSON の format_version は { $found } だが、tauto bind が読むのは { $wanted } である (rust-toolchain.toml の nightly を使うこと)
bind-out-of-date = { $file } が古い ({ $command } を実行すること)
bind-not-regular = { $file }: 通常のファイルである必要がある
bind-recovery = 復旧用のファイルを { $path } に保存している
bind-rustdoc-failed =
    エラー: cargo rustdoc が失敗した:
    { $stderr }
bind-expected-block-containing = { $file }: { $key } を含むブロックであるべきだ
bind-dependency-texts = { $file }: { $path }: テキストのリストであるべきだ
bind-dependency-unsupported = { $file }: { $path }: 対応していない値
bind-dependency-version = { $file }: { $path }: バージョンかブロックであるべきだ

# The config file.
bind-unknown-key = 不明なキー `{ $key }`
bind-crate-missing = `crate` がない
bind-expected-block = ブロックであるべきだ
bind-expected-text = テキストであるべきだ
bind-expected-texts = テキストのリストであるべきだ
