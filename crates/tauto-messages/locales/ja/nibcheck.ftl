nibcheck-not-a-constructor = { $name } はコンストラクタではありません
nibcheck-ambiguous-constructor = コンストラクタ `{ $name }` が曖昧です: 型注釈をつけるか、{ $candidates } のように書いてください
nibcheck-no-field = { $name } にフィールド `{ $field }` はありません
nibcheck-effect-takes-no-type-arguments = `{ $effect }` は型引数を取りません
nibcheck-arm-write-instance = `{ $effect }` の腕が答えるインスタンスを書いてください: `{ $effect }<…>(…)`、すべてに答えるなら { $every }
nibcheck-effect-type-argument-count = `{ $effect }` の型引数は { $expected } 個ですが、{ $given } 個与えられました
nibcheck-arm-binds-each-type-argument = すべてのインスタンスに答える腕は、型引数を順にすべて束縛します: { $every }
nibcheck-typefn-not-transparent = { $name }: native 型関数は、透明で effect を持たず、Type 型の引数だけを取らなければなりません
nibcheck-typefn-duplicate = native 型関数 `{ $name }` の宣言が重複しています
nibcheck-typefn-body-statements = { $name }: native 型関数の本体は型の式でなければなりません。文や一般の計算には、検査された型レベル評価が必要です
nibcheck-typefn-body-computation = native 型関数の本体は型の式でなければなりません。一般の計算には、検査された型レベル評価が必要です
nibcheck-typefn-expansion-limit = native 型関数の展開が上限を超えました
nibcheck-typefn-not-fully-applied = { $name } は、型関数の中で完全に適用された native 型ではありません
nibcheck-typefn-needs-named-constructor = native 型関数には、名前のある型コンストラクタが必要です
nibcheck-typefn-not-constructor-with-arguments = { $name } は、引数 { $count } 個の native 型コンストラクタではありません
nibcheck-typefn-undeclared-effect = native 型関数の中の effect `{ $effect }` は、宣言された単相の effect ではありません
nibcheck-typefn-argument-count = { $name } の明示的な型引数は { $expected } 個ですが、{ $found } 個ありました
nibcheck-typefn-recursive = 再帰的な native 型関数 { $name } には、検査された型レベル評価が必要です
nibcheck-typefn-used-as-value = { $name } は型を返すので、実行される値としては使えません
nibcheck-pattern-field-missing = フィールド `{ $field }` がパターンにありません

# What the checker of executable code expected a type of.

nibcheck-what-record-constructor = レコードのコンストラクタ
nibcheck-what-constructor = コンストラクタ
nibcheck-what-result-of = `{ $name }` の結果
nibcheck-what-named = `{ $name }`
nibcheck-what-field = フィールド `{ $field }`
nibcheck-what-while-condition = `while` の条件
nibcheck-what-if-condition = `if` の条件
nibcheck-what-returned-value = 返す値
nibcheck-what-argument = 引数
nibcheck-what-product-member = 積のメンバー
nibcheck-what-ascription = 型注釈
nibcheck-what-arm-goal = 腕のゴール
nibcheck-what-arm-body = 腕の本体
nibcheck-what-match-result = `match` の結果
nibcheck-what-budget-steps = budget のステップ数
nibcheck-what-budget-memory = budget のメモリ
nibcheck-what-function-result = 関数の結果
nibcheck-what-guard = ガード
nibcheck-what-handler-arm = ハンドラの腕

# A type that does not fit the one expected.

nibcheck-mismatch = { $what }: { $found } は { $expected } に合いません
nibcheck-mismatch-lend = { $what }: { $found } は { $expected } に合いません: `&` で貸してください
nibcheck-mismatch-number = { $what }: { $expected } のはずですが、別の型の { $found } です。証明からも見える数には `std::{ $module }` の `{ $checked }` を書いてください
nibcheck-mismatch-closure-kind = { $what }: { $expected } のはずのところに { $found } のクロージャがあります
nibcheck-mismatch-open-product = { $what }: { $found } と { $expected } をメンバーの型で対応づけられるのは、どちらも型パラメータや未知の型を含まないときだけです。メンバーを同じ順に書くか、タグで区別してください
nibcheck-mismatch-product-clash = { $what }: 積の二つのメンバーが同じ型 { $member } を持つので、メンバーを型で対応づけられません。メンバーを位置で書くか、タグで区別してください
nibcheck-forgets-linear-member = { $what }: 線形のメンバー { $member } を捨てています
nibcheck-not-an-application = { $ty } は型コンストラクタの適用ではありません
nibcheck-literal-does-not-fit = { $literal } は { $ty } に収まりません
nibcheck-kind-does-not-fit-bound = { $kind } は { $bound } に合いません: 型パラメータに対する { $ty }
