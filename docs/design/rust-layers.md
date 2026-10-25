# Rust の読み込み層と検査層

`crates/tauto/src/read.rs` は、ソースを読み、マクロとクラスを展開し、展開済みの
`Program` を検査器・評価器へ渡す。ファイルの読み込みは `program.rs` が行い、
`read.rs` がファイルごとの判定と診断の位置を組み立てる。

`lib.rs` の公開モジュールは、実装モジュールと読み込み関数を再エクスポートする。
`tauto::surface::parse_program`、`tauto::check::check_files`、`tauto::types::check_types`、
`tauto::eval::run` などは、ソースを受け取る入口である。`tauto-kernel` には
`check` の実装があり、ファイル名とモジュール名は公開モジュールと対応する。
`tauto-nibcheck` は `types`、`rows`、`lin`、`tauto-eval` は `eval` を持つ。
どちらも構文を `tauto-surface` から受け取り、評価器は検査器と `tauto-rt` を使う。

検査器の本体は `Loaded` を受け取らない。カーネルは `Program` を検査し、
役割の収集は検査済みの `FileEntry` を受け取る。増分検査の公開 `Checker` は
読み込み層のアダプターで、構文マクロの表示を位置と文字列の表にして内部の検査器に渡す。
宣言の判定、チェックポイント、ダイジェストは内部の検査器が扱う。

prelude とカーネルが生成する等式の宣言は、マクロを実行せずに読む。
prelude の文とエラーがマクロ展開を通す読み方と一致することは
`crates/tauto/src/read_tests.rs` が検査する。ライブラリのクラス展開は
`types::prelude` が行う。

`tauto-surface` は `surface`、`syntax`、`nibstd`、`direct`、`generated` と、
`macros` の構文値・スコープ・引用・位置情報を持つ。依存先は `tauto-parol` と
`tauto-syntax` だけである。診断の編集 `Fix` は `surface` に属し、
`generated` と `syntax` と検査器が同じ型を使う。`tauto::check::Fix` もこの型を指す。

## マクロと検査器の境界

`tauto-macro::macros::checker::TypedChecker` は宣言の検査、式のゴール、
接頭の宣言を保持する `PrefixedChecker`、文脈内の `Elaboration` を提供する。
`Elaboration` は推論・型検査・変換・弱頭正規化・名前の型を問い合わせる。
`tauto-kernel::check::KernelChecker` が既存の `check_in`、`goal_of`、`Prefixed`、
`Elaborator` に委譲する。検査規則や受理条件は変えない。

`Diagnostic`、`Mismatch`、`Verdict`、`HoleGoal`、`Entry` は
`tauto-surface::diagnostic` に置き、`tauto::check` からも再エクスポートする。
`Fix` は引き続き `tauto-surface::surface` にある。`Prefixed` はカーネルの状態を
持つため検査器側に残し、マクロからは `PrefixedChecker` を通して使う。

`tauto-macro::macros::expand::Options` は `Limits` と検査器の `Arc` を受け取る。
既存の `tauto::macros::Options` は `Limits` の別名で、従来のフィールドと
`Default` を維持する。`tauto::macros::expand_files` が検査器を接続するため、
既存の呼び出し側を変更する必要はない。`tauto-macro` はカーネルにも読み込み層にも
依存しない。マクロの問い合わせ結果にかかわらず、展開された宣言は受理前に
名前付き検査器と独立カーネルで検査する。

## カーネルの独立

`tauto-kernel` は `check.rs` と `check/*`、`prelude.taut` を持つ。
`tauto-surface` と `tauto-macro`、位置情報とハッシュを扱う基礎 crate に依存し、
ファイル読み込み、抽出、マクロの実行は行わない。`tauto::check` が読み込み関数と
カーネルの公開項目を合わせて再エクスポートする。

読み込み層から呼ぶために公開範囲を広げた項目は `Kernel`、その `new`、`declare_program`、
`library`、`use_cache`、`show_syntax`、および `kernel_prelude`、`declare_prelude`、`checked_entries`。
`declare_program` は通常の宣言だけを検査する。組み込み宣言を指定できる
内部の `declare` は公開しない。カーネルの内部フィールドや検査規則も公開しない。`KernelChecker` とマクロの trait の
接続はカーネル内にある。

カーネル単体テストはマクロ展開の要らない入力を展開なしで読む。
二つの検査器を直接比較する差分テストは `check/differential.rs` に残す。
ファイルを読み、再帰関数の精密化を検査する差分テストは
`crates/tauto/tests/kernel_elaboration.rs` に置く。両方が同じ決定的な生成器を使い、
既定の件数・seed・判定条件を維持する。下位 crate から `tauto` へのテスト依存はない。
