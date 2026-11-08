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
bind-unbound = { $item }: { $reason }
bind-iterator-item = { $item }: Iterator::Item: { $reason }
bind-not-public = { $item }: { $crate_name } の公開アイテムではありません
bind-only-structs-enums-functions = { $item }: struct、enum、関数だけが束縛できます
bind-type-needs-instances = { $item }: 型引数や const 引数を持つ型は、設定にインスタンスが必要です（まだ未対応）
bind-trait-not-bindable = { $item }: トレイト { $trait_name } は束縛できません
bind-why-unsafe-fn = unsafe fn
bind-why-async-fn = async fn
bind-why-const-generic = const ジェネリクス
bind-why-generic-needs-instance = ジェネリック関数には、設定でインスタンスを与える必要があります
bind-why-instance-count = 設定の型引数は { $given } 個ですが、関数の型引数は { $expected } 個です
bind-why-instance-type-unbound = インスタンスの型 { $type_name } は束縛されていません
bind-why-mut-str = &mut str
bind-why-mut-slice = &mut [T] は未対応です
bind-why-impl-trait-argument = `impl Trait` の引数
bind-why-size-nested = 型の入れ子の中の { $type_name }（変換できるのは、引数、結果、Option の結果だけです）
bind-why-type = 型 { $type_name }
bind-why-large-tuple = 3 つ以上の組
bind-why-self-outside-impl = impl の外の Self
bind-why-type-parameter = 型パラメータ { $name }
bind-why-str-nested = 型の入れ子の中の &str
bind-why-alias-default-parameter = 別名 { $alias } は既定値つきの引数を持ちます
bind-why-type-not-bound = 型 { $type_name } は束縛されていません
bind-why-unsized-slice = サイズ不定のスライス
bind-why-dyn-trait = dyn Trait
bind-why-impl-trait-result = `impl Trait` の結果
bind-why-no-tauto-form = tauto では書けない型
