# ケースの検査

`cases/` の Eure 文書は、Tauto の入力と検査する結果を持つ。一つの文書は
トップレベルのケースか、`cases` の名前付きケースを持つ。両方を持つ文書では
トップレベル、名前付きケースの順に実行する。ファイル名とケース名を組み合わせた
名前で絞り込める。

## 入力

`source` はソースの本文。言語タグ `path` を持つテキストなら、ケースファイルの
ディレクトリからの相対パスを読む。参照先の import、include、構文テーブルは
参照先のファイルを基準に解決する。プロセスの作業ディレクトリは変更しない。

`files` は相対パスと本文の対応。一時ディレクトリに書き、`entry` を読み込む。
`entry` を省略したときは `main.nib`。値に `path` タグがあると、そのファイルの
本文を一時ディレクトリへコピーする。コピーした本文の import はコピー先から
解決するので、依存ファイルも `files` に含める。パスに `..`、絶対パス、構文
テーブルを置き換えるパスは使えない。

`imports` は、`path` タグを持つライブラリファイルの一覧。インラインの `source` や
`files` の入口を読む前に読み込む。ライブラリはコピーせず、元のディレクトリで
import、include、文法テーブルを解決する。入口の本文と診断位置は変更しない。

`tote` は、`path` タグを持つ tote のディレクトリ。マニフェストに従ってソースと依存を
読み、証明を検査して実行する。examples の通常出力は、この入口に実行の期待値を
組み合わせて検査する。

`files_tote = "app"` は `files` 内の相対ディレクトリを実際の tote として読む。
そのディレクトリの `Tauto.eure` が entry と依存を決め、依存の entry は実行しない。
`entry`、`imports`、`parses` とは併用しない。単一ファイルへ平坦化する代用ではない。
virtual tote の `javascript.exports` は JavaScript バックエンドの公開関数を指定する。
それ以外の Rust/JavaScript ホスト設定は、backend runner で明示的に拒否する。
設定を既定値で置き換えて成功扱いせず、外部 tote や保持したホスト固有テストを使う。

`source`、`files`、`tote` の期待値は共通。`expands`、`trace`、`macro_error`、
`load_error` は、ファイルとして読み込む入力で使う。

`expands` は、入口のファイルのマクロ展開後の文を表示器 (`print_stmts`) が書き出した
文字列と比べる。表示器の出力が正準な形なので、整形器にはかけず、期待値の前後の
空白を除いたうえで文字列として完全一致を求める。期待値は表示器の出力そのままに書く。
改名された名前 (`tmp#1`) は表示器だけが書く形で、整形器は読めない。

## 宣言

`checks` は宣言名と期待する判定の対応。指定した宣言はちょうど一つ存在しなければ
ならない。同名の宣言が複数のファイルにあるときは、ファイルの相対パス、`::`、
宣言名をつないで指定する。同じファイルの同名宣言については、名前の末尾に `#` と
1 から数えた出現順を付ける。重複宣言を拒否するケースも、それぞれの判定を検査できる。
`declarations` は、インポート先も含む宣言名の一覧を順序も含めて完全一致で検査する。

`checks_all` は `checks` で指定していない全宣言への期待値。宣言が一つもなければ
失敗する。インポート先の宣言も対象になる。判定には次の形式がある。

| 判定 | 条件 |
|---|---|
| `ok` | 検査済みで、公理への依存がない |
| `checked` | 検査済み。公理への依存は問わない |
| `axioms: ` に続く名前の列 | 公理への依存が、順序も含めて一致する |
| `error: ` に続くテキスト | 失敗し、メッセージがそのテキストを含む |
| `incomplete: ` に続く名前の列 | 穴と未完成な宣言への依存が一致する |
| `skipped` | カーネルの検査対象ではない |

`holes` は穴の順序付き一覧。各要素は `declaration`、`name`、`goal`、`context` を
持ち、必要なら `file` でファイルも指定する。ゴールと文脈の型は表示したテキストと
完全一致で比較する。文脈は束縛された順に、変数名、コロン、空白、型をつなぐ。
一覧に書かれない穴があれば失敗する。

## 診断

`diagnostics` は期待する診断の順序付き一覧。空の一覧はカーネルの診断がないことを
検査する。各要素の `stage` は `checks`、`types`、`rows`、`lin` のいずれかで、省略時は
`checks`。一覧が指定した段階の診断をすべて検査し、件数の違いも失敗とする。
段階をまたぐ一覧では、この段階の順に並べ、同じ段階では処理された順に並べる。

| フィールド | 検査するもの |
|---|---|
| `message` | メッセージに含まれるテキスト。必須 |
| `name` | カーネルの宣言名 |
| `file` | 診断の属するファイルのパスの末尾 |
| `span` | 診断範囲を、ソースの一部に `«` と `»` を一組入れて示したもの |
| `fix` | 修正候補の置換テキスト |
| `fix_span` | 修正候補が置き換えるソース本文 |
| `fixed_source` | 修正候補を適用したファイルの全文。挿入位置も検査する |

`span` は、`«` と `»` を取り除いた文字列がソースにちょうど一回だけ現れるように書く。
例: `span = "theorem pt_refl(p: «Pt»)"`。`«` と `»` は一つずつで、`«` が先。空の範囲は `«»`。
取り除いた文字列が現れない、二回以上現れる、ソースが `«` か `»` を含む、のいずれもケースの
誤りで、診断の比較より前に失敗する。位置を数字で書く `start`、`end`、`line`、`column`、
`span_index` は使えない。一意にならないときは、`«»` の前後のソースを増やす。
修正候補はカーネルの診断で検査できる。

`types`、`rows`、`lin` は成功か最初のエラーメッセージを検査する簡略形。
`parses` は構文の受理・拒否を検査し、他の段階を暗黙に要求しない。
`load_error` はファイル欠落や循環 import による読み込み失敗を検査する。
`macro_error` は読み込めたプログラムの最初のマクロエラーを検査する。

`fixes` は `files` の `entry` に `tauto check --fix` の手順（`check-fix.md`「適用の手順」）を
メモリの上で行い、その結果を検査する。ディスクのファイルが変わらないことも検査する。
`files_tote`、`imports` と、プログラムを検査する他の期待値とは併用しない。

| フィールド | 検査するもの |
|---|---|
| `lint` | `true` なら `tauto check --fix` の代わりに `tauto lint --fix` の手順（import の一覧など）を行う |
| `applied` | 適用した編集の見出しの順序付き一覧 |
| `reverted` | 取り消した編集の見出しの順序付き一覧 |
| `files` | 本文が変わったファイルの、`files` での相対パスと最後の全文。書かないファイルは変わらないこと |
| `diff` | `--dry-run` が出す diff。ファイルは `files` での相対パスで示す。行末の空白は比べない |

## 実行

`shows` は `perform show` の出力順、`stdout` と `stderr` は各出力先の全文、`exit` は
終了コードを比較する。終了コードを省略したときは成功を要求する。`tests` は実行した `perform test` の名前の順の一覧で、
すべてが成功し、名前と順が一致することを要求する（`tauto test` が一つのファイルについて確かめることと同じ）。`budget` は実行の
ステップ上限で、省略時は評価器の既定値。`run_error` は実行が失敗してメッセージが
指定したテキストを含むことを要求し、成功時の出力の期待値とは併用しない。

成功する実行は動的所有権検査を有効にした実行とも比較する。`drops` はその実行で
破棄された値の型を順に比較する。インラインのソースは、ファイルに書いて読み込んだ
実行とも比較する。

Rust バックエンドは `shows`、`run_error` と、`rust_shows`、`rust_error`、`build` の
期待値を別のランナーで検査する。外部ソースの import は、元のファイルから読み込む。
バックエンドの期待値しか持たないケースは、評価器では未検査として数える。
バックエンドの期待値は `source`、`files`、`tote` に指定する。`imports` で指定したライブラリも読み込む。

## ケースの妥当性

ケースは Eure の型付き読み取りで検査する。未知フィールド、不正な型、空の
`checks`、検査する期待値のないケース、両立しない入力と期待値は失敗する。
`description` は説明文。

ケースファイルのスキーマ `tools/tauto-test-suite/case.schema.eure` は、ランナーが読む型から
生成する。生成結果とコミットした内容が一致すること、`cases/` のすべてのファイルがスキーマを
満たすことを `cargo test -p tauto-test-suite --test schema` で検査する。型を変えたら
`TAUTO_UPDATE_SCHEMA=1` を付けて実行し、スキーマを書き直す。Eure のスキーマを読むエディターでは、
これで補完と検査が効く。

ケースが何で実行されるかはシナリオとして一か所（`Case::scenarios`）で決め、各ランナーは
それに従う。シナリオは `eval`（評価器と前段）、`rust`、`javascript` の三つ。どのシナリオも
走らないケース（セルフホストの差分検査だけのケースを除く）や、走らないシナリオだけが読む
期待値（例: `backends = ["rust"]` と `javascript_shows`）を持つケースは失敗する。
`scenarios = ["eval", "rust"]` と書くと、そのケースで走るシナリオがちょうどそれらで
なければ失敗する。書き間違いで意図した検査が走らなくなることを防ぐために使う。

`unimplemented` は実行時の失敗を未実装として数える印。ケース形式の誤りには適用
しない。実行が成功した場合は印が古いものとして失敗する。絞り込みに一致する
ケースが一つもないとき、リポジトリのランナーは成功しない。

言語の受理・拒否と出力の具体例はケースに置く。キャッシュを書き換えるテスト、
生成した入力の比較、Rust API の状態や構造を直接扱うテストは Rust で検査する。

## Rust で検査する範囲

言語の受理・拒否、展開、診断、実行結果はケースで検査する。`crates/tauto/tests` は、
Rust API の境界や、入力の一覧だけでは表現しない性質を検査する。

| ファイル | 検査する性質 |
|---|---|
| `certified_state.rs` | 不正な証明の抽出拒否、実装の変更と証明の関係、抽出後の実装 |
| `classes.rs` | クラスの抽出と、instance の法則を埋める API |
| `extract_records.rs` | 証明の消去が実行時の record の抽出結果を変えないこと |
| `holes.rs` | レポートの構造と JSON、候補の受理、元ファイルを変更しないこと |
| `include_cache.rs` | キャッシュを作った後に include 先を書き換えたときの再検証 |
| `kernel_diff.rs` | 生成した項についてのモデルとの比較 |
| `kernel_elaboration.rs` | 生成した宣言の精密化結果を独立カーネルが受理すること |
| `lambda_proofs.rs` | 文法ファイルと構文宣言の本文の一致 |
| `library_mutations.rs` | 実際のライブラリの演算を書き換え、その時点の証明が変更を拒否すること |
| `macros.rs` | レポート API のマクロ履歴と位置情報 |
| `manifest.rs` | マニフェストの構造、bindings の統合と失敗時の状態 |
| `syntax.rs` | 構文のメタデータ API、検索先の隔離、Eure とブロックの読み取りの一致 |


## 共有入力と実装固有の検査

Rust のテストは `cases/` を読まない。ケースと同じことを確かめるテストは置かず、
足りない検査はケースかケースの項目にする。型・行・所有権の内部表現、コード生成された
記号、ABI、キャッシュの無効化、実行器のカウンターなど、ケースで書けない性質を見る
Rust のテストだけが残り、その入力はテストの横に書く。
`fixtures` の名前付き項目には `source` と空でない `reason` が必要で、トップレベルに
だけ置ける。fixture は意味論の成功したケースとして数えない。

セルフホストの部品の差分テストは `selfhost_harness::differential("<部品>")` で
`differential = "<部品>"` の付いたケースを集め、Rust の実装と tote の出力を比べる。
`selfhost_entry` を持つケースは `selfhost_harness::selfhost_cases` で読み、
`selfhost_stdout`・`selfhost_compile_error`・`selfhost_run_error` を期待値にする。

`inferred_types` は束縛名と表示された型、`inferred_rows` は関数名と効果の集合、
`inferred_kinds` はデータ型名と所有権種別 (`copy`、`shared`、`affine`、`linear`) を
照合する。対象名がない場合や一意でない場合も失敗する。
`tote_warnings` は `tote` か `files_tote` の検査（`tauto check --tote`）が出す警告のメッセージ（部分文字列）の順序付きの一覧で、件数も一致しなければ失敗する。
`tote_errors` は同じ検査が失敗とした宣言の診断（プログラムの Nib の検査の誤りを含む）のメッセージ（部分文字列）の順序付きの一覧で、件数も一致しなければ失敗する。
`rows_javascript` は JavaScript 向けの行検査を指定する。`format` は整形結果の全文、
`format_error` は整形失敗のメッセージ、`lint` は順序付きの lint メッセージを検査する。

`format_literals` は `files` と `entry` を持つケースで、構文リテラルの本体とコメント内の
フェンスをその構文が登録した `fmt` 関数で整えた `entry` の全文を照合する。ファイルは
import と構文の表を含めて読み、`tauto fmt` と同じ `format_literals` を通す。整えた結果をもう一度
通しても同じ全文になることも検査する。`format_literals_warnings` は、整えられなかった
リテラルについて出る警告のメッセージ（部分文字列）の順序付きの一覧で、省くと警告が一つも
出ないことを要求する。

`editor_tokens` も `files` と `entry` を持つケースで、エディターが構文リテラルとコメント内の
フェンスに与える色（`tauto_analyzer::editor::dsl_tokens`）を、`entry` の中の位置順に
`行:列 種別 テキスト` で並べて照合する。行と列は 1 から数え、列は文字単位で、テキストは
トークンが覆う `entry` の部分である。複数行にまたがるトークンは行ごとに分かれる。`editor_token_warnings`
（`editor_tokens` と一緒に書く）は、登録された `tokens` の関数を使えなかったテキストについて出る警告の
メッセージ（部分文字列）の順序付きの一覧で、省くと警告が一つも出ないことを要求する。

`extract = true` は実際の tote 読み込み・証明検査を通ってから抽出する。単に抽出印を
付けて証明済みとして扱う経路はない。`extract_source = true` を併記すると、抽出した構文木を
ソースへ書き出して読み直し、そのプログラムを検査・実行する。書き出したソースには終了性の
検査結果は引き継がれない。
`extracted_nib` は抽出後の宣言を選び、Nib の
プリンターで文字列にして期待値と照合する表である。キーは宣言の完全な名前、
一意な短い名前、または末尾に `*` を付けた名前の接頭辞。接頭辞で選んだ宣言は
名前順に並べる。前後の空白だけを無視し、本文は完全一致を要求する。
元の入力からの抽出と実行を同じケースで検査できる。
`args` は評価器と両バックエンドに渡す引数。
`permissions` は評価器に与える `--allow-*`（`host-effects.md`）、`links` は `files` の隣に作るシンボリックリンクと
そのリンク先。`args` と `permissions` の `{dir}` は `files` を置いたディレクトリの絶対パスになる。

## バックエンドの要求と失敗

`backends = ["rust", "javascript"]` は実行を要求する経路を明示する。明示した経路で
コンパイラーが未対応を返しても、暗黙の skip や成功にはしない。
`compile_errors.rust` / `compile_errors.javascript` は `front: メッセージ`、
`unsupported: メッセージ`、`generate: メッセージ`、`build: メッセージ` の形で、
失敗段階と非空の部分文字列の両方を照合する。別の失敗や予期しない成功は失敗する。

既知の実装不足・不具合は `backend_known_failure` のバックエンド別フィールドに
同じ段階指定、または `runtime: メッセージ` で記録する。これは意図した意味論が
保証できているという印ではない。ランナーはその失敗を実際に確認して未検査として
報告し、成功や異なる失敗では古い契約として失敗する。実行の安全制限による強制終了を
期待した意味論の失敗として受け入れない。

共通の `shows`、`stdout`、`stderr`、`exit` を両バックエンドで検査する。
`rust_shows` / `rust_error` と `javascript_shows` / `javascript_error` は、その
表示・失敗契約。JavaScript は `javascript_*`、既存の native 共通契約としての
`rust_*`、共通期待値の順で参照する。ただし `javascript_shows` を明示した場合、
`javascript_error` がなければ JavaScript の成功契約となり、Rust/評価器のエラーを
継承しない。`javascript_error` を併記すれば失敗前の表示と失敗の両方を検査する。
Rust は `rust_*`、共通期待値の順。
バックエンドのエラー期待値は共通の成功時 `shows`
を置き換えるが、明示した stdout・stderr・終了コードやバックエンド固有の表示は
引き続き検査する。コンパイルのみの JavaScript ケースでも Node の構文検査を行う。

`budget` は評価器の命令燃料であり、native/JavaScript のステップと同じ単位ではない。
歩数の数え方は backend ごとに違ってよい。数え方に依る答えは `rust_shows` や
`javascript_shows` のように backend の名前を付けて書く。`rust_budget_steps` は Rust の実行が
budget の燃料検査で数えた歩数（`tauto_rt::budget::STEPS`）で、Rust の実行だけが照合する。
`drops` は評価器の動的所有権計測。バックエンドで出力を検査できても、これらの計測
まで保証したとは数えず partial と報告する。元の計測専用 Rust テストも保持する。

解放の順序のように、どの backend でも観測できる振る舞いは `probe_drops` で書く。
各ランナーは標準の `Probe` 型を用意する。プログラムは `affine struct Probe {}` と
`module Probe { extern { fn new(&name: Text): Probe } }` を宣言し、
`Probe::new("a")` で作った値が解放されるたびに、その名前が順に記録される。
評価器は所有権計測の解放のうち probe のものだけを、Rust は `tauto_rt::probe` の `Drop` を、
JavaScript は最後の所有者が `release` した時点を数える。通常の生成コードは変えない。

### どのテストを case に書くか

言語の意味、つまりどの backend でも同じになるはずの結果は case に書き、各ランナーで実行する。
Rust のテストに残すのは、Rust の実装そのものを見るテストだけである。

- **case に書くもの**: 表示、エラー、解放の順序（`probe_drops`）など、プログラムの観測できる振る舞い。
  backend ごとに違ってよい値（歩数など）は `rust_shows` や `rust_budget_steps` のように backend の名前を付ける。
- **Rust に残すもの**: 生成コードの形、最適化の経路比較、JavaScript ランタイムの内部関数、
  ホストの例外や Promise の扱いなど、一つの backend の実装にしかないもの。
  これらのテストのソースは .eure から読まず、テストの横に直接書く。
- **CLI のテスト**: `tauto` コマンドの引数、出力の書式、ファイル操作（`--steps`、
  doc、lsp、totes、trust bundle など）は CLI という一つの実装の振る舞いなので、
  CLI のテストとしてソースを横に置く。そこで実行するプログラムの意味を確かめたいときは、
  その部分を case に移し、CLI のテストは引数と書式だけを見る。

`cargo run -p tauto-test-suite --bin case-routes -- <filter>` は入力ごとの期待値と
利用可能な経路を一覧にする。この一覧は実行結果ではない。実際のランナーは pass、
partial、未対応、失敗を区別し、選択ゼロや検査成功ゼロを成功にしない。

## 並列実行

`tests/cases.rs`、`tests/backends.rs`、`tests/fuzz.rs` は独自の `main` を持つ一つのテストだが、
中のケースは並列に流す。ワーカーの数は `std::thread::available_parallelism()` で、
環境変数 `TAUTO_TEST_THREADS=<数>` で上書きできる（`1` で直列）。各ワーカーは評価器
と同じ 256 MiB のスタックのスレッドで、ケースは互いに独立に流れる。結果は
ケース名（評価器は`カテゴリ/ファイル`、ファイルの中はケースの順）の順に並べてから
出力し、失敗の判定は全部の結果がそろった後に一度だけ行うので、出力と判定は
ワーカーの数によらない。

ワーカーが共有してはならないものは、ワーカーごとに持つ。Rust バックエンドは
ワーカーごとに `work-<n>` と `target-<n>` を使い（rustc の増分キャッシュと Cargo の
ロックは一つのビルドしか許さない）、JavaScript はワーカーごとの一時ディレクトリ、
VM のバイトコード実行は `work-<n>` を使う。VM の機械は一度だけ作り、全ワーカーが
共有する。ケースの一時ディレクトリは通し番号で一意に決まり、ケースの
基準ディレクトリは各スレッドが持つ。

生成した crate を Cargo で作る処理は、`CARGO_NET_OFFLINE=true` のとき `--offline` を
付けて呼ぶ。ネットワークがない環境では、依存の取得を待たずに Cargo の「パッケージが
ない」というエラーですぐ失敗する（成功にはしない）。

## バックエンドごとの状態

バックエンドは `tools/tauto-test-suite/tests/backends.rs` の一つのランナーで順に回す
（`-- rust` や `-- javascript` で一つに絞れる）。各バックエンドは、選んだすべてのケースについて状態を一つ出す。状態は
`pass`、`partial: 理由`（出力は検査したが、どのバックエンドも観測しない検査が残る）、
`declined: 理由`（`rust = "skip: …"`）、`todo: 理由`（ケースが宣言した失敗：
`backend_known_failure` の失敗、`unimplemented` のケースの失敗）、`fail: 理由` のいずれか。
`fail` が一つでもあればランナーは失敗する。

バックエンドがまだ扱えないことは、そのケースの `backend_known_failure` にだけ書く。
宣言のない未対応や失敗は `fail` になり、宣言した失敗が起きなくなれば古い宣言として
`fail` になる。そのため、各ケースの `backend_known_failure` と `unimplemented` が
残りの作業の一覧そのもので、ほかに一覧を持たない。すべてのケースがすべての
バックエンドで `pass` になることが目標である。`rust = "skip: …"` は Rust だけに効き、
JavaScript の実行は変えない。

評価器のランナー（`tests/cases.rs`）では、状態は `pass`、`unimplemented` のケースの失敗、
失敗のいずれかで、失敗が一つでもあればランナーは失敗する。

## バックエンドの差分 fuzzing

ケースは人が書いた入力しか試さない。`tools/tauto-test-suite/tests/fuzz.rs` は、
seed から型の付いたランダムなプログラムを作り（`src/fuzz.rs`）、評価器・Rust・
JavaScript で実行して、観測が一致することを確かめる。比べるのは show の列と、
実行が正常に終わったか、どの実行時エラー（`the number is too large`、
`division by zero`）で止まったかである。評価器は失敗した実行の show を返さないので、
show の行を前から削ったプログラムで、失敗より前の show を求める。

作るプログラムは止まり、結果が実装の数え方によらない。`i64` の端の値を使う算術、
`if`、`let`、`struct` と `enum` と `match`、一階の関数、クロージャ、`while`、
多重に再開する handler、そして `budget` のうち答えが step の数え方によらない二つ
（止まらない本体を `k(v)` で答える、止まる本体を `info.unbounded()` で続ける）。
乱数は自前の SplitMix64 なので、seed はどの環境でも同じプログラムを指し、依存を
増やさない。

`cargo test -p tauto-test-suite --test fuzz -- [<数> [<最初の seed>]] [eval,rust,javascript]`
で回す。既定の stress は seed 0 から 300 個、`TAUTO_FUZZ_PROFILE=quick` は 9 個を使う。
明示した数と最初の seed が優先する。三つのバックエンドを選ぶのが既定で、seed は並列に
流れ、結果は seed の順に出る。各 seed と全体の経過秒を表示する。時間はビルドキャッシュと
選択したバックエンドにも依存するので、quick と stress の所要時間は実行時の表示で確認する。

`TAUTO_FUZZ_INTERACTIONS=1` は型と束縛の構造を固定し、反復数と整数値を生成する。
seed を三つの系統に順に割り当てるので、連続する三つの seed が全系統を覆う。

- 一回再開する effect と可変借用。handler をまたいだ更新と最終値。
- effect row 多相の高階関数と、環境を捕獲した callback。
- 多重再開と、環境を捕獲した callback。各枝の実行順と回数。

これらは要求、枝の値、更新後の値を show のイベントとして記録する。イベントの順序・回数・
最終結果を Rust 側の小さな算術モデルとも比較し、三つのバックエンドが同じ誤りをした場合も
失敗とする。一般の host effect や Drop のトレースを採取する仕組みではない。
共有可変状態を伴う多重再開、非同期中断、extern の破棄、budget とキャンセルの組合せは
この生成器の対象ではない。従来のランダム式生成器は同じ環境変数を外して別に実行する。

失敗した入力と観測は実行ごとに分かれた一時ディレクトリに保存され、場所が出力される。
interaction が正常に実行されたがモデルと異なる場合は、同じバックエンド群の不一致を
保つ候補だけを採用し、反復数と値を最大 20 回の試行で縮める。候補の型・束縛構造は変えず、
型エラーやビルド失敗に置き換わった候補は採用しない。最小性を保証する縮小ではない。
失敗の原文は original.taut、原文の期待イベント列は original-expected.txt、採用した
縮小入力は reduced.taut、その期待イベント列は expected.txt に保存する。期待イベント列は
モデルか明示した期待値がある場合だけ保存する。構文・型の拒否やビルド失敗も成功とは扱わない。

`TAUTO_FUZZ_FILE=<path>` を付けると、そのファイルのプログラムを同じように比べる。
この経路は任意の入力に算術モデルを適用しない。`TAUTO_FUZZ_EXPECTED=<path>` も付けると、
そのファイルの各行を期待イベント列として読み、正常終了と列の完全一致も要求する。
原文には original-expected.txt、縮小入力には expected.txt を指定する。期待値を指定しない
場合はバックエンド間の比較だけなので、全バックエンドが同じ誤りをする反例の再現には
期待値の指定が必要である。`TAUTO_FUZZ_EXPECTED` は `TAUTO_FUZZ_FILE` と組み合わせる。
縮めた不一致は、直すときに期待結果とともに `cases/` の固定回帰ケースにする。

## セルフホストの差分検査

`differential` は既存のセルフホスト比較ドライバーを示す。受理・拒否や出力は、
指定した構成要素の Rust オラクルと Tauto 実装を、同じ共有入力で比較する。
評価器の一般ランナーはこの契約だけを成功扱いしない。

`TAUTO_SELFHOST_BACKEND=javascript` は `run_tote_native` を使う構成要素ドライバーを
JavaScript で実行する。省略時または `rust` は Rust。`tote_binary` を直接使うテストは
Rust 専用のままであり、この環境変数では切り替わらない。入力収集は path タグの実体、
複数ファイル、tote のソースを読む。load_error ケースでも読み取れるソースは残す。

bootstrap の Rust/JavaScript 出力検査、セルフホストの各構成要素の差分検査、
セルフホスト全体による同一プログラムのコンパイル・実行は異なる保証である。
未実装の段階や実行していない経路を、別の経路の成功で代用しない。

入力監査とランナー自身の検査は次で実行する。

```bash
cargo test -p tauto-test-suite --test runner
```

ケースを選んで各経路を実行する例:

```bash
cargo test -p tauto-test-suite --test cases -- core-kernel
cargo test -p tauto-test-suite --test backends -- rust core-kernel
cargo test -p tauto-test-suite --test backends -- javascript core-kernel
TAUTO_SELFHOST_BACKEND=javascript cargo test --manifest-path tools/selfhost-harness/Cargo.toml --test kernel kernel_replays_one_shared_declaration_on_selected_backend
```

最後の環境変数を省略すれば同じ共有入力を Rust 実行器で比較する。これは選択した
カーネルの差分検査であり、すべての構成要素や全コンパイラー経路の成功を意味しない。

## セルフホスト全段階の受入契約

`selfhost-plan` は共有ケースのすべての要求を列挙する。これは実行結果ではない。
`shared-cases` は、選んだケースの要求ごとに実装、実行器、対象バックエンド、段階を
記録する。Rust の実装から得た値は差分検査の参照値にしか使わず、Tauto 実装の
観測値として扱わない。明示した除外と Rust のハーネス専用ケースは成功と別に数える。

`TAUTO_SELFHOST_BACKEND` はコンパイラーを動かす実行器、`--target` は生成する
プログラムのバックエンドである。後者を省略すると前者と同じになる。JavaScript 上で
動く Tauto の Rust エミッターは Rust の対象経路であり、JavaScript のコード生成を
検査したことにはならない。対象エミッターがなければ未完了になる。

`--component` で構成要素を選んでも、そのケースのほかの要求は消えない。
未観測、未対応、時間制限は未完了として非ゼロ終了する。異なる段階のエラー、
異なる診断、重複した報告、異常終了、古い checkout を指すハーネスは失敗する。
期待した拒否は、その段階の非空の診断だけで照合する。処理系のクラッシュや
裸の失敗通知を型検査などの拒否に読み替えない。

`differential = "rustgen"` の名前付きエントリーは `selfhost_entry` で指定する。
`selfhost_stdout`、`selfhost_compile_error`、`selfhost_run_error` のうち一つを宣言し、
それぞれ正確な標準出力、Tauto コンパイラーの診断の部分文字列、生成プログラムの
実行エラーの部分文字列を検査する。生成、対象コードのビルド、実行は別の段階であり、
ビルド失敗をコンパイラーの期待した拒否や実行エラーとして受け入れない。
この明示契約と専用ドライバーの元のオラクルは同じ共有入力を使う。
制限された構成要素の拒否契約が通ることと、言語全体の受理能力は別の保証である。

```bash
cargo run -p tauto-test-suite --bin selfhost-plan -- cases
TAUTO_SELFHOST_BACKEND=rust cargo run --manifest-path tools/selfhost-harness/Cargo.toml --bin shared-cases -- --root cases --target rust --report selfhost-rust.json
TAUTO_SELFHOST_BACKEND=javascript cargo run --manifest-path tools/selfhost-harness/Cargo.toml --bin shared-cases -- --root cases --target javascript --report selfhost-javascript.json
cargo test -p tauto-test-suite --test selfhost
cargo test --manifest-path tools/selfhost-harness/Cargo.toml --test shared_cases
```

構造化された証明・診断・推論結果、ローダー、一般プログラムのコード生成、所有権の
計測などの要求には、それぞれの完全な観測アダプターが必要である。構成要素だけの
成功でこれらを埋めず、要求単位の未完了を報告する。

共有ランナーの差分一致は、両方の報告が対象段階の形式を満たす場合にだけ成立する。
参照実装の panic はハーネス失敗であり、段階不明の `error` 同士が等しくても成功に
しない。フォーマッターの `error` は正常な整形文字列とも衝突するため、この形式のままでは未完了になる。
空の診断部分文字列は診断未指定として扱い、厳密な受入検査では未完了になる。位置だけの診断や証明の詳細契約も、
完全な観測アダプターなしに別の成功で埋めない。

Rustgen の共有アダプターは `--contract SOURCE ENTRY` を使う。この opt-in モードは
標準エラーに版付きの段階を出力し、入力読み取り・構文表の故障・ソースの拒否・
コード生成成功を区別する。拒否の診断は非空の一行に限り、余分な標準エラーや
異常終了は受け入れない。`--contract` を付けない引数では、標準出力と診断の形式は変わらない。
Rust 実行器では取得したコンパイラー実行ファイルを一度だけ選び、その SHA-256 と
生成コード・生成実行ファイルの SHA-256 を記録する。JavaScript コンポーネントの
具体的なモジュール識別子が公開されない場合は、その制限を明示する。

コンパイラーの初回ビルドとケースの実行には別々の時間枠を使う。準備だけを行う
モードは検証付きキャッシュ API で成果物を構築し、識別子と所要時間を記録するが、
意味論のケースを一つも成功として数えない。

```bash
TAUTO_SELFHOST_BACKEND=rust cargo run --manifest-path tools/selfhost-harness/Cargo.toml --bin shared-cases -- --root cases --prepare rustgen --setup-timeout-seconds 1800 --report setup.json
TAUTO_SELFHOST_BACKEND=rust cargo run --manifest-path tools/selfhost-harness/Cargo.toml --bin shared-cases -- --root cases --target rust --component rustgen --filter NAME --timeout-seconds 120 --report execution.json
cargo test --manifest-path tools/selfhost-harness/Cargo.toml --test shared_cli
cargo test --manifest-path tools/selfhost-harness/Cargo.toml --test rustgen_protocol
```

準備の既定時間は 1800 秒、実行全体の既定時間は 120 秒。これらはコンパイラーの
命令燃料や生成プログラムの時間枠とは別である。準備モードは現在 native 成果物だけを
公開する。準備とケース選択の引数を混在させたり、値を省略したりすることはできない。

各呼出しは古いレポートを開始状態で置き換え、固有の識別子を持つ子プロセスを監督する。
Unix では子孫を含むプロセス群を終了時・時間超過時に停止する。時間超過やクラッシュ
では、選んだケースは未完了、成功数はゼロの終端レポートを残す。成果物を準備できた
ことと、入力の全要求を実行して保証したことは別に報告する。監督機構を利用できない
プラットフォームでは、無期限に実行せず明示的に失敗する。
ワーカーの呼出し識別子は引数で渡し、検証付きキャッシュの環境識別を変えない。
引数解析に失敗しても、`--report` の指定先が一意なら失敗レポートで置き換える。
その指定自体が欠ける・重複する場合は出力先を推測せず、実行前にエラーにする。
監督プロセス自体の外部強制終了は、既に記録した開始・未完了状態のまま残り得る。
これを終端成功や、正常な時間制限処理が済んだ証拠として扱わない。

## 証明表示の検査

`proofs` は証明表示の期待値の一覧。ファイル入力を要求し、各要素の `name` は定理名、
`format` は `block`、`node`、`tree`、`tree-html`、`natural`、`json` のいずれか（省略時は `natural`）。
`output` は出力の全文を文字列として完全一致で検査する。空白や末尾の改行も比較し、正規化しない。
`path` タグの付いた `output` は、そのケースファイルからの相対パスにある期待値ファイルを読む。
`error` は表示を作れない場合のエラー全文を完全一致で検査する。各要素は `output` と `error` のどちらか一方を必須とする。
`failed` と `incomplete` は検査結果の状態を検査する。部分一致と除外文字列による検査は持たない。

`proofs` の各要素の `full` は `--full` の指定に対応する。`format = "json"` では JSON としての構文も検査する。

### hover の検査

`hovers` は、`files` と `entry` で指定したファイルの hover を検査する。
各項目の `at` は対象の文字列、`occurrence` は同じ文字列の出現番号（0 始まり、既定は 0）であり、
その先頭の位置を使う。`contains` は表示に含む文字列の一覧、`absent` は表示がないことを表す。
`proof` は説明を比較する定理名で、同じスナップショットの通常の自然言語表示と一致することを検査する。
`proof_file` はその定理のファイル名（既定は entry のファイル名）である。
`buffers` は entry の親ディレクトリを基準としたファイル名から未保存の本文への対応である。
