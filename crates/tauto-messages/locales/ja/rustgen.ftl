# Rust 生成器 (`tauto-rustgen`) のメッセージ: バインディングの解決とビルドの
# エラー、エクスポートについての警告、そしてバジェットや補助関数が通常の経路を
# 保つ理由。名前・型・パス・Rust は変数であり、そのまま書く。

## Bindings

rustgen-binding-not-rust = エラー: { $at } の Rust { $rust } は Rust ではない ({ $error })
rustgen-type-no-binding = エラー: { $name } に rust バインディングがない (Tauto.eure の rust.types に加える)
rustgen-extern-no-binding = エラー: { $name } に rust バインディングがない (Tauto.eure の rust.extern に加える)
rustgen-unknown-host-contract = { $at }: 未知の nonresuming ホスト契約 { $contract }
rustgen-contract-unknown-extern = { $at }: nonresuming 契約が未知の extern { $name } を指している
rustgen-invalid-facade-name = { $at }: Rust の nonresuming ファサード名 { $name } は不正である
rustgen-facade-collides-export = { $at }: nonresuming ファサード { $name } がエクスポートされた名前と衝突する
rustgen-facade-collides-data = { $at }: nonresuming ファサード { $name } がエクスポートされたデータの名前と衝突する
rustgen-entry-unknown-export = { $at }: nonresuming エントリが未知の、または選ばれていないエクスポート { $name } を指している
rustgen-invalid-entry = { $at }: 不正な nonresuming エントリ: { $reason }

## Exports

rustgen-export-not-uniffi = { $name } は UniFFI に公開されない型を持つ
rustgen-export-performs = { $name } は { $row } を実行するので Rust に公開されない。tauto でハンドラを持つ関数に包む
rustgen-export-callback = { $name } は Rust に公開されないコールバック型を持つ。コールバックは、効果行が空の明示的な共有借用で、対応する関数でない値でなければならない
rustgen-export-not-exposed = { $name } は Rust に公開されない型を持つ

## Building

rustgen-extern-misfit =
    エラー: extern { $name } の Rust がその宣言に合わない
    {"  "}宣言: { $declared }
    {"  "}バインド: { $bound } ({ $path })
    {"  "}rustc: { $first }
    { $stderr }
rustgen-extern-type-not-send =
    エラー: extern 型 { $name } はスレッドを越えられないが、このプログラムはタスクを開始する
    {"  "}バインド: { $at }
    {"  "}rustc: { $first }
    {"  "}Send + Sync でない値はホストに留まる。値の代わりに id (アフィン) を取る直接効果の背後に置き、ホストに留めておく。
rustgen-write-failed = { $dir }: { $error }
rustgen-cannot-run-cargo = cargo を実行できない: { $error }
rustgen-rustc-rejected =
    内部エラー: rustc が生成されたコードを拒否した (生成器のバグである。ソースは { $dir } にある):
    { $stderr }

## Borrowed helpers

rustgen-borrow-generic-context = 補助関数には完全な具体型引数が必要である
rustgen-borrow-helper-control = 補助関数が対応しない制御効果を持つ
rustgen-borrow-escaping-result = 借用するのはスカラーの結果を持つ補助関数だけである
rustgen-borrow-generic-context-2 = 具体的なジェネリック引数に、不変な生成クローンの証明がない
rustgen-borrow-parameter-ownership = パラメータが借用・可変・線形・ホスト束縛、またはその他の不透明なものである
rustgen-borrow-analysis-limit = 具体的な補助関数のグラフが有界な読み取り証明を超える
rustgen-borrow-keep-owned = 借用する補助関数の生成は無効である
rustgen-borrow-argument-shape = 補助関数の引数の数がそのインスタンスと一致しない
rustgen-borrow-owner-not-retained = 借用する引数は保持されたクローンのローカルか、証明された借用パターンの子でなければならない
rustgen-borrow-argument-snapshot = 別の引数が評価を変更・中断・観測しうる。所有されたスナップショットを保持する
rustgen-borrow-owned-use = コピーでないパラメータか子が消費・保持・返却される
rustgen-borrow-mutable-read = 補助関数が借用セルか可変セルを読む
rustgen-borrow-field-escape = 借用した値から出られるのはボックス化されていないコピーのフィールドだけである
rustgen-borrow-opaque-call = 借用するのは閉じた直接の補助関数呼び出しだけである
rustgen-borrow-argument-shape-2 = 補助関数の引数の数が一致しない
rustgen-borrow-owned-child = 再帰的な借用引数が借用パラメータに根ざしていない
rustgen-borrow-match-borrow = 明示的な借用 match とガードはソースの所有権を保つ
rustgen-borrow-opaque-use = 補助関数が読み取り証明の外にある構築・借用・捕捉・制御・効果を含む
rustgen-borrow-cursor-origin = スカラーでないローカルは保持されたパラメータに根ざすカーソルでなければならない
rustgen-borrow-helper-mutation = フィールド・借用・捕捉セルへの書き込みはカーソル証明の外にある
rustgen-borrow-cursor-origin-2 = カーソルへの代入は保持されたパラメータの根を保たなければならない
rustgen-borrow-helper-mutation-2 = 代入できるのは補助関数ローカルのスカラー状態と証明されたカーソルのスロットだけである
rustgen-borrow-helper-mutation-3 = 借用された可変束縛と捕捉された可変束縛は所有する補助関数を保つ
rustgen-borrow-analysis-limit-2 = 補助関数が有界なローカル状態の証明を超える
rustgen-borrow-field-base = 射影が不変なローカルのフィールドパスではない
rustgen-borrow-pattern-ownership = パターンが対応しない所有権を持つ

## Synchronous budgets

rustgen-budget-no-immediate-handler = バジェットに直接の nonresuming ハンドラがない
rustgen-budget-handler-of = { $function } のハンドラ
rustgen-budget-analysis-limit = 呼び出しグラフが有界な具体コンテキストの証明を超える
rustgen-budget-concurrent-observer = 中断された状態を保持する間に、共有値が別のスレッドから観測されうる
rustgen-budget-multishot = マルチショットの制御は Future の経路を保つ
rustgen-budget-handler-shape = ハンドラはちょうど一つの Exceeded の腕を持ち、直接の操作を持ってはならない
rustgen-budget-exceeded-not-total = Exceeded にはバジェットの Info を受け取る無条件で全域な腕が必要である
rustgen-budget-continuation-used = Exceeded の継続が使われているか、捨てられることを証明できない
rustgen-budget-abort-not-locally-total = { $op } が証明されていない外側の観測者に逃げうる。局所的で無条件な全域の中断の腕が必要である
rustgen-budget-unproven-payload = ハンドラのペイロードが暗黙のホストの Clone か Drop を呼びうる
rustgen-budget-observable-handler = ハンドラの区間がホストのライフタイム観測者に対して閉じていると証明されていない
rustgen-budget-unproven-lifetime-value = 型 { $ty } の値の破棄または借用のライフタイムが証明されていない
rustgen-budget-handler-may-panic = 検査付き算術が保持された値をホストのパニックフックにさらしうる
rustgen-budget-handler-may-panic-2 = 観測区間で match の完了が証明されていない
rustgen-budget-handler-may-panic-3 = 燃料かホスト制限の検査が閉じた観測区間を抜けうる
rustgen-budget-handler-may-panic-4 = ハンドラのループがパニックせず停止すると証明されていない
rustgen-budget-refcell-guard = RefCell の借用ガードが中断をまたいで生き続けうる
rustgen-budget-callback-mutation = コールバックの証明は可変借用を認めない
rustgen-budget-nested-handler = 入れ子のハンドラは同期の証明で扱われない
rustgen-budget-nested-budget = 入れ子のバジェットは再開可能な状態を保たなければならない
rustgen-budget-effect-operation = 同期の伝播で扱うのは、局所的に捕まる resume-0 の操作だけである
rustgen-budget-unproven-callable = { $origin } は閉じていてホストから不透明であると証明されていない
rustgen-budget-unproven-callable-cast = { $origin } は通常の経路を保つ
rustgen-budget-callback-effect = コールバックのループが停止し tick を持たないと証明されていない
rustgen-budget-body-return = バジェット本体からの return はそれを囲む制御スコープを変える
rustgen-budget-callback-mutation-2 = コールバックの証明は変更を認めない
rustgen-budget-refcell-guard-2 = RefCell への代入が保持された借用ガードを観測しうる
rustgen-budget-callback-effect-2 = コールバックは中断せず tick を持たない内部の本体を持たなければならない
rustgen-budget-call-tier = この呼び出しの制御効果は同期の伝播で扱われない
rustgen-budget-call-tier-2 = この関数の制御効果は同期の伝播で扱われない
rustgen-budget-unproven-type-arguments = { $function } の呼び出しには { $generics } の具体型引数が必要である。見つかったのは { $found }
rustgen-budget-unknown-callback = { $function } のコールバック引数 { $index } ({ $name }) に閉じた内部の由来がない。型 { $ty }、由来 { $origin }
rustgen-budget-missing-argument = 引数がない
rustgen-budget-unproven-parameter = { $function } の引数 { $index } ({ $name }) のライフタイムが証明されていない。解決された型 { $ty } ({ $from } から)
rustgen-budget-unproven-result = { $function } の結果のライフタイムが証明されていないか、呼び出し可能な値が逃げる。解決された型 { $ty }
rustgen-budget-callback-builtin = 組み込み { $name } に閉じた純粋なコールバックの証明がない
rustgen-budget-builtin-may-panic = 組み込み { $name } にパニックしない観測の証明がない
rustgen-budget-extern-tier = 信頼された extern { $name } の呼び出し階層 { $tier } には対応しない
rustgen-budget-extern-result = 信頼された extern { $name } の結果型 { $ty } には対応しない
rustgen-budget-extern-argument = 信頼された extern { $name } の引数 { $index } の型 { $ty } には対応しない
rustgen-budget-extern-contract = extern { $name } には明示的なバインディング契約と、資格のあるホスト契約エントリの両方が必要である
rustgen-budget-unknown-call = 呼び出し先 { $target } は閉じていてホストから不透明であると証明されていない
rustgen-budget-unproven-lifetime-local = ローカル { $name } のライフタイムか呼び出し可能な由来が証明されていない。解決された型 { $ty }
rustgen-budget-unproven-lifetime-var = 可変ローカル { $name } のライフタイムが証明されていない。解決された型 { $ty }
rustgen-budget-assignment-invalidates = 代入が { $name } の呼び出し可能な由来を無効にする

## Where a callable comes from, in the reasons above

rustgen-budget-origin-function = 関数 { $name }
rustgen-budget-origin-local = ローカル { $name }
rustgen-budget-origin-continuation = 継続 { $name }
rustgen-budget-origin-borrow = { $name } の借用
rustgen-budget-origin-borrowed-closure = 借用クロージャ
rustgen-budget-origin-capture-free-closure = 捕捉のないクロージャ
rustgen-budget-origin-captured-closure = 捕捉するクロージャ
rustgen-budget-origin-cast = { $origin } のキャスト
rustgen-budget-origin-computed-callable = 型 { $ty } の計算された呼び出し可能な値
rustgen-budget-origin-computed-value = 型 { $ty } の計算された値
