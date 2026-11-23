# javascript・rust バックエンドのメッセージ(`tauto run`, `tauto build`)。

js-node-failed = javascript バックエンド(node)を実行できない: { $e }
js-type-not-extern = javascript 型 `{ $name }` はプログラムの extern 型ではない(`extern {"{"} type { $name } {"}"}` と宣言する)
js-type-unbound = extern 型 `{ $name }` に javascript の束縛がない(Tauto.eure の javascript.types に加える)
js-type-ambiguous = javascript.types の extern 型 `{ $name }` が複数の extern 型 ({ $candidates }) を指す。束縛する型の完全名で書く
js-extern-unavailable = extern `{ $name }` は javascript ターゲット { $target } では使えない
js-builtin-browser = `{ $name }` は javascript ターゲット browser では使えない。ユーザー定義のエフェクトと javascript extern の束縛を用意する
js-async-direct = wait を行う extern `{ $name }` が direct ハンドラから到達できる。再開可能なエフェクトを使う
js-wasm-extern-waits = extern `{ $name }` は wait を行いますが、Wasm にした Rust の extern はすぐに答えます。Promise を返す JavaScript の関数に束縛してください
js-wasm-callback-abandons = Rust wasm extern `{ $name }` が受け取るコールバックは、ネイティブのフレームを捨てるか複製するおそれがある。そのエフェクトはコールバックの中で処理するか、javascript の束縛を使う(Rust をまたげるのは direct と resume 1 だけである)
js-extern-binding-form = javascript extern `{ $name }` は、相対モジュールパスに #export を続けた形で書く
js-extern-no-export = javascript extern `{ $name }` にエクスポート名がない
js-type-binding-form = javascript 型 `{ $name }` は、相対モジュールパスに #export を続けた形で書く
js-type-no-export = javascript 型 `{ $name }` にエクスポート名がない
js-extern-no-binding = `{ $name }` に束縛がない。Tauto.eure に javascript.extern か rust.extern を加える
js-source-outside = javascript ソースはトートの中になければならない: { $path }
js-source-leaves = javascript ソースがトートの外に出ている: { $path }
js-source-symlink = javascript ソースにシンボリックリンクは使えない: { $path }
js-source-contains-output = javascript ソースが出力ディレクトリを含んでいる: { $path }
js-inconsistent-instantiation = `{ $name }` の具体化が食い違う: { $a } と { $b }
js-no-concrete-instantiation = `{ $name }` の JavaScript での具体的な型を決められない
js-unresolved-type-argument = JavaScript の型引数 `{ $name }` が決まらない: { $ty }
js-specialization-limit = JavaScript の特殊化が関数インスタンス { $n } 個を超えた(多相再帰が展開し続けている可能性がある)
js-incomplete-type-arguments = 関数値 `{ $name }` の検査済み型引数が足りない
js-wasm-build-failed = Rust wasm extern をビルドできない: { $e }
js-wasm-build-errors = Rust extern を { $target } 向けにビルドできなかった(対応する Rust ターゲットを入れ、wasm で使える依存を使う):
    { $stderr }
js-wasm-callback-direct = Rust wasm のコールバックは direct でなければならない。中断するコールバックには javascript の束縛が要る
js-wasm-unknown-data = 不明な wasm データ型 `{ $name }`
js-wasm-borrowed-view = `{ $name }` は借用を抱えるので wasm ABI をまたげない。所有値か javascript の束縛を公開する
js-wasm-type-abi = 型 { $ty } は Rust wasm ABI をまたげない。所有データを具体的な Rust ラッパーか javascript.extern で公開する
js-wasm-no-borrowed = { $ty } には借用の wasm 表現がない

rust-browser-run = browser ターゲットはモジュールを出力する。`{ $command }` を使う
rust-no-manifest = { $path }: Tauto.eure がない
rust-unsupported = { $place }: { $backend } バックエンドでは対応していない: { $what }
rust-export-generic-skipped = { $path }: `{ $name }` は export しない。ジェネリクスを持つ関数には自分のコードがない
rust-budget-eligible = { $at }: { $function } の budget { $budget }({ $variant }): 静的に適格。外側の budget が有効か、ランタイムの sync 機能があると通常の Future の経路になる
rust-budget-checks = [compiler-checks] 制御の形、文脈呼び出し、型とライフタイム、ハンドラの観測者を検査した。ホストの振る舞いの前提は別に示す
rust-budget-ordinary = { $at }: { $function } の budget { $budget }({ $variant }): 通常の Future の経路
rust-budget-assumption = [trusted-assumption] { $kind } { $name }({ $at }): { $contract }(コンパイラやカーネルによる証明ではない)
rust-wasm-lacks-net = net エフェクト(その HTTP クライアントはスレッドを止める)
rust-target-lacks = { $path }: { $target } ターゲットは { $what } に対応していない
rust-lock-created = { $path } を作った
rust-trusted-code = このプログラムが信頼する Rust コード:
rust-usage = 使い方: { $run }
    {"       "}{ $build }
rust-trusted-extern = {"  "}extern { $name } -> { $rust }（{ $at }）
js-export-row-skipped = { $path }: `{ $name }` はメソッドにしない。インスタンスが答えない effect が行にある
