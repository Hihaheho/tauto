nibcheck-not-a-constructor = { $name } はコンストラクタではありません
nibcheck-ambiguous-constructor = コンストラクタ `{ $name }` が曖昧です: 型注釈をつけるか、{ $candidates } のように書いてください
nibcheck-no-field = { $name } にフィールド `{ $field }` はありません
nibcheck-effect-takes-no-type-arguments = `{ $effect }` は型引数を取りません
nibcheck-effect-no-type-argument-named = `{ $effect }` には `{ $name }` という型引数がありません
nibcheck-call-no-type-argument-named = この関数には `{ $name }` という型引数がありません
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
nibcheck-what-product-member = 直積のメンバー
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
nibcheck-mismatch-product-clash = { $what }: 直積の二つのメンバーが同じ型 { $member } を持つので、メンバーを型で対応づけられません。メンバーを位置で書くか、タグで区別してください
nibcheck-forgets-linear-member = { $what }: 線形のメンバー { $member } を捨てています
nibcheck-not-an-application = { $ty } は型コンストラクタの適用ではありません
nibcheck-literal-does-not-fit = { $literal } は { $ty } に収まりません
nibcheck-kind-does-not-fit-bound = { $kind } は { $bound } に合いません: 型パラメータに対する { $ty }

# 値が書かれる場所に書かれた struct、またはレコード型。

nibcheck-record-type-not-a-value = レコード型 `{"{"} … {"}"}` は値ではありません。名前のないレコードは `#{"{"} … {"}"}` と書いてください
nibcheck-struct-as-value = `{ $name }` は struct です: `{ $name } {"{"} field: value {"}"}` と書いてください

# 実行コードの検査の、名前とフィールド。

nibcheck-not-defined = { $name } は定義されていません
nibcheck-not-a-var = `{ $name }` は var ではありません
nibcheck-type-declared-twice = 型 { $name } が二重に宣言されています
nibcheck-function-declared-twice = 関数 { $name } が二重に宣言されています
nibcheck-not-a-function = { $found } は関数ではありません
nibcheck-no-method = { $owner } にメソッド { $name } はありません
nibcheck-not-a-struct = { $name } は struct ではありません
nibcheck-field-given-twice = フィールド `{ $field }` が二重に与えられています
nibcheck-field-missing = { $name } のフィールド `{ $field }` がありません
nibcheck-nat-too-large = { $value } は大きすぎます
nibcheck-not-a-nat = { $value } は Nat ではありません
nibcheck-not-an-int = { $value } は Int ではありません
nibcheck-float-too-large = { $value } は Float には大きすぎます
nibcheck-not-a-var-for-lend = { $what } は var ではありません。`&mut` を貸せるのは var だけです

# 実行コードの検査の、宣言と型。

nibcheck-quote-splice-type = `quote` の式の中の `$` が取るのは SynExpr、SynIdent、Judgement のいずれかで、{ $found } ではありません
nibcheck-int-literal-no-type = 整数リテラルに整数型がありません
nibcheck-closure-returns-borrow = クロージャは借用を返せません
nibcheck-view-type-argument = 借用を抱える型はここでは型引数にできません
nibcheck-generic-effect-argument = 借用を抱えうる { $name } の値は効果の引数にできません: `<{ $name }: NoBorrow>` と書いてください
nibcheck-rc-linear = `&rc { $ty }` は書けません: linear な値はちょうど一度だけ使い、`&rc` の複製はそれを共有します
nibcheck-rc-borrow = `&rc { $ty }` は書けません: { $ty } は借用を抱えますが、箱は保存も返却もされ、借用より長く生きえます
nibcheck-rc-generic-borrow = `&rc { $name }`: { $name } は借用を抱ええますが、箱は保存も返却もされ、借用より長く生きえます: `<{ $name }: Type + NoBorrow>` と書いてください
nibcheck-rc-mut = { $ty } はその複製が共有します: 中身は `&` で借りるだけで、`&mut` では借りられません
nibcheck-rc-not-owned = { $what }: { $found } は { $expected } に合いません: `&rc` の中身はその複製が共有し、`&` で借りるだけで取り出せません
nibcheck-constructor-kind-mismatch = { $what } が取るのは { $arg } から { $result } へのコンストラクタですが、{ $shown } は { $kind } です
nibcheck-type-not-determined = `{ $name }` の型 { $generics } がここでは決まりません。`let x: T = ...` のように値に型を与えてください
nibcheck-takes-arguments = { $name } は引数を { $count } 個取ります
nibcheck-type-constructor-variable-one-argument = { $name } は型コンストラクタ変数で、引数を 1 個取ります
nibcheck-slice-only-borrowed = Slice(A) は借用としてしか使えません
nibcheck-takes-effect-row = { $name } はここで effect 行を取ります: `{ $name }(!{"{"}a{"}"} ∪ e)` のように書いてください
nibcheck-effect-row-only-to-row-parameter = effect 行を与えられるのは行パラメータだけで、{ $name } のこの引数はそうではありません
nibcheck-not-a-type = 型ではありません
nibcheck-kind-of-function-type = `{ $kind }` は関数型の種です
nibcheck-not-a-type-of-program = プログラムの型ではありません
nibcheck-parameter-has-no-type = `{ $name }` の引数に型がありません
nibcheck-resume-quantity = `resume { $quantity }`: 0、<=1、1、ω のいずれかを書いてください
nibcheck-borrow-only-extern-type = 借用を抱えると宣言できるのは extern の `type` だけです。フィールドを持つ型は、フィールドが借用を抱えれば借用を抱えます
nibcheck-borrow-field = 借用はフィールドにできません
nibcheck-declared-shared-holds-itself = { $declared } と宣言されていますが、`{ $name }` は自分自身を持つので shared です
nibcheck-declared-but-field = { $declared } と宣言されていますが、フィールド { $field } は { $kind } です
nibcheck-term-generic-needs-extraction = 項のジェネリック `{ $name }` は、native コンパイルの前に検査された抽出が必要です
nibcheck-return-needs-mut-parameter = -> { $ty } には &mut 引数が必要です
nibcheck-return-needs-borrowed-parameter = -> { $ty } には借用の引数が必要です
nibcheck-value-indexed-constraints = 値で添字づけられた制約には、検査された辞書の抽出が必要です
nibcheck-not-a-class = { $name } はクラスではありません
nibcheck-where-only-generics-of-function = where が制約できるのは { $name } のジェネリックだけです
nibcheck-predicate-written-twice = { $class }({ $argument }) が二重に書かれています
nibcheck-row-variable-not-declared-type = 行変数 `{ $variable }` は宣言されていません。`{ $name }(!{ $variable })` と書いてください

# 実行コードの検査の、文・式・パターン・腕。

nibcheck-let-mut-borrow-binds-return = `let &mut { $name }` が束縛するのは、関数が `-> &mut A` として返すものです
nibcheck-let-borrow-binds-return = `let &{ $name }` が束縛するのは、関数が `-> &A` として返すものです
nibcheck-borrow-cannot-be-stored = 借用は保存できません: `{ $name }` が { $ty } を持つことになります
nibcheck-var-borrow-binds-view = `{ $name }` は借用として束縛されていますが、値は借用を抱えません
nibcheck-var-cannot-store-borrow = 借用は `var { $name }` に保存できません
nibcheck-var-holds-linear = var は線形な値を持てません: `{ $name }` は { $ty } です
nibcheck-view-var-field-assigned = 借用を抱える var のフィールドには代入できません
nibcheck-assigns-field-of-var = { $target } が代入するのは `var` か `&mut` 引数のフィールドです
nibcheck-assign-through-borrow = 借用の指す先に書き込むには `*{ $place } := …` と書く
nibcheck-deref-needs-mut-borrow = `*{ $place } := …` は `&mut` の借用の指す先への書き込みだが、`{ $place }` は `&mut` の借用ではない
nibcheck-deref-outside-assign = 借用は値として読む。`*` を書くのは `:=` の左だけ
nibcheck-return-outside-function = `return` が関数の外にあります
nibcheck-declare-type-at-top-level = 型は最上位で宣言してください
nibcheck-declare-extern-at-top-level = `extern` ブロックは最上位で宣言してください
nibcheck-declare-syntax-at-top-level = syntax やマクロは最上位で宣言してください
nibcheck-not-supported-yet = まだサポートされていません: { $what }
nibcheck-constructor-without-fields = `{ $name }` はフィールドのないコンストラクタです。`()` を付けずに `{ $name }` と書いてください
nibcheck-function-argument-count = { $expected } 個の値を取る関数に { $given } 個が与えられました
nibcheck-cannot-infer-function-type = この呼び出しの関数型を推論できません
nibcheck-product-type-as-value = `×` が作るのは型で、値ではありません。直積は `#(…)` と書いてください
nibcheck-no-effect-declared = effect `{ $effect }` は宣言されていません
nibcheck-host-answers = `{ $effect }` にはプログラムを動かすホストが答える。`handle` はこれに腕を持たない
nibcheck-effect-value-count = `{ $effect }` は値を { $expected } 個取りますが、{ $given } 個与えられました
nibcheck-budget-arms-differ = 1 つの `exceeded` 腕が答える予算が、異なる型を与えています
nibcheck-clone-takes-one-borrow = `clone` が取る借用は 1 つで、`clone(&x)` と書きます
nibcheck-clone-takes-borrow = `clone` は借用を取ります: `clone(&x)` と書いてください
nibcheck-division-operands-unknown = `/` の被演算子の型が分かりません。型を書いてください
nibcheck-integer-division = 整数の `/` は型エラーです。div(a, b)、mod(a, b)、decimal(a) / decimal(b) のいずれかを書いてください
nibcheck-operator-other-operands = `{ $op }` が取る被演算子はこれではありません
nibcheck-operator-not-a-number = `{ $op }` の { $ty }: 数ではありません
nibcheck-label-not-on = ラベル `@{ $tag }` は { $ty } にありません
nibcheck-unit-pattern-mismatch = `#()` は { $ty } に一致しません
nibcheck-pattern-not-supported = このパターンはまだサポートされていません: { $what }
nibcheck-pattern-cannot-match = { $pattern } のパターンは { $target } に一致できません
nibcheck-product-pattern-cannot-match = 直積のパターンは { $ty } に一致できません
nibcheck-product-pattern-members = { $count } 個のメンバーのパターンは { $ty } に一致できません
nibcheck-pattern-field-count = { $name } のフィールドは { $fields } 個ですが、パターンは { $pattern } 個です
nibcheck-match-depends-on-value = この `match` の型は値 `{ $name }` に依存しており、証明でしか検査できません
nibcheck-match-not-exhaustive = この `match` はすべての値を網羅していません
nibcheck-match-literals-need-rest-arm = リテラルの `match` は、名前付きの残り腕 (`other => …`) で終えてください
nibcheck-default-arm-last = 既定の腕 `_ =>` は最後に置いてください
nibcheck-default-arm-unreachable = 既定の腕 `_ =>` はどの値にも一致しません
nibcheck-typed-arm-nested = 型つきの束縛 `{ $name }: …` は `match` の腕のパターン全体にだけ書けます
nibcheck-typed-arm-not-union = 型つきの腕は合併型を絞り込みます。この `match` の対象は { $ty } です
nibcheck-typed-arm-unsolved = 型つきの腕は型の分かった合併型を絞り込みます。この `match` の対象は { $ty } です。型を書いてください（`match x: T {"{"} … {"}"}`）
nibcheck-typed-arm-not-member = { $arm } は { $ty } のメンバーでも、そのメンバーの合併でもありません
nibcheck-typed-arm-type-variable = メンバー { $member } は型変数です。型つきの腕はその値をほかのメンバーの値と区別できません
nibcheck-typed-arm-no-head = メンバー { $member } には型つきの腕が調べられる頭がありません
nibcheck-typed-arm-same-head = { $other } と { $member } は頭が同じです。{ $arm } の型つきの腕はそれらの値を区別できません
nibcheck-pattern-on-union = コンストラクタやリテラルは合併型 { $ty } に一致しません。先にメンバーへ絞り込んでください（`x: T => match x {"{"} … {"}"}`）
nibcheck-match-members-not-covered = この `match` はメンバー { $members } を網羅していません
nibcheck-arm-told-apart-by-type-arguments = `{ $effect }` は型引数で区別されます。腕が答えるのは 1 つのインスタンスで、`{ $effect }<…>(…)` と書きます
nibcheck-arm-value-count = `{ $effect }` が与える値は { $expected } 個ですが、腕が取るのは { $given } 個です
nibcheck-direct-arm-must-resume = { $effect } は direct です。腕のすべての経路は k(e) で終わらなければなりません
nibcheck-arm-does-not-resume = { $effect } は再開しません (`resume 0`): その腕に `{ $k }` はありません
nibcheck-arm-must-be-generic = `{ $effect }` の腕は、どの型引数で perform されても動かなければなりません。型引数は perform する場所で選ばれます

nibcheck-operands-differ = `{ $op }` の { $left } と { $right }: 被演算子が異なります
nibcheck-operands-differ-labeled = `{ $op }` の { $left } と { $right }: 被演算子が異なります。`@{ $tag }` が付くのは片方の被演算子だけです (`{ $op }` よりラベルの結合が強いため)。結果にラベルを付けるには `@{ $tag } (a { $op } b)` と書いてください
nibcheck-not-a-constructor-hint = `{ $name }` はコンストラクタではありません。`{ $hint }` のことですか?
nibcheck-not-a-constructor-plain = `{ $name }` はコンストラクタではありません

# クラスとインスタンス。

nibcheck-class-already-class = { $name } はすでにクラスです
nibcheck-class-built-in = { $name } は組み込みです
nibcheck-class-declared-twice = クラス { $name } が二重に宣言されています
nibcheck-class-already-type = { $name } はすでに型です
nibcheck-value-indexed-classes = 値で添字づけられたクラスには、検査された辞書の抽出が必要です
nibcheck-class-parameter-count = クラス { $name } のパラメータは 1 つですが、{ $count } 個あります
nibcheck-class-argument-arity = クラス { $name } のパラメータは { $expected } 個ですが、{ $count } 個あります
nibcheck-not-a-kind = { $name } は種ではありません
nibcheck-class-parameter-no-borrow = クラス { $class } の引数には NoBorrow を付けられません。メソッドやそれを使う関数の型引数に `NoBorrow` を書いてください
nibcheck-class-member-declared-twice = { $class }::{ $name } が二重に宣言されています
nibcheck-class-method-where-cycle = メソッドの where をたどると自分のクラスに戻ります: { $path }
nibcheck-class-method-performs-effects = { $class }::{ $name } は effect を起こすので、{ $class } に法則は持てません
nibcheck-value-indexed-instances = 値で添字づけられたクラスのインスタンスには、検査された辞書の抽出が必要です
nibcheck-class-structural-no-instances = { $name } は構造的で、書くべきインスタンスはありません
nibcheck-instance-head-distinct-generics = インスタンスの頭部は、型を互いに異なるジェネリックに適用しなければなりません
nibcheck-generic-not-in-head = { $name } は頭部に現れません
nibcheck-instance-needs-constructor = { $class } が取るのは引数が 1 つ足りない型コンストラクタですが、{ $shown } はそうではありません
nibcheck-instance-type-kind = { $class } が取るのは { $bound } までの型ですが、{ $shown } は { $kind } です
nibcheck-instance-orphan = { $class }({ $ctor }) は { $class } か { $ctor } のトートに置かなければなりません
nibcheck-instance-duplicate = { $class } には { $ctor } のインスタンスがすでにあります
nibcheck-where-only-generics-of-instance = where が制約できるのはインスタンスのジェネリックだけです
nibcheck-instance-no-law = { $class } に法則 { $name } はありません
nibcheck-instance-law-twice = インスタンスの法則 { $name } が二重に書かれています
nibcheck-instance-missing-method = インスタンス { $class }({ $ty }) は { $name } を定義していません
nibcheck-instance-method-parameters = { $head } の { $class }.{ $name } が取るのは { $parameters } です

# 型で添字づけられた effect。

nibcheck-index-entry-binds-each-type-argument = `{ $entry }`: `{ $head }` のすべてのインスタンスは、型引数を順にすべて束縛します: `∀ { $want }. { $head }({ $want })`
nibcheck-index-entry-write-forall = `{ $entry }`: `∀ A. res(A)` と書いてください
nibcheck-row-write-instance = 行が意味する `{ $entry }` のインスタンスを書いてください: `{ $entry }(…)`、すべてなら `∀ { $want }. { $entry }({ $want })`
nibcheck-copied-for-too-many-indices = `{ $name }` が多すぎる添字でコピーされています
nibcheck-index-no-type-found = 型が見つかりませんでした
nibcheck-index-generic-not-given = ジェネリック `{ $name }` で、与えられていません
nibcheck-index-arguments-unknown = 型引数がここでは分かりません。注釈を付けてください
nibcheck-type-cannot-index-effect = `{ $ty }` では effect に添字を付けられません
nibcheck-which-effect-this-is = どの `{ $effect }` かが決まりません: { $why }
nibcheck-row-around-two-instances = 周りの行に `{ $effect }` のインスタンスが 2 つあります。どちらかを型注釈で書いてください
nibcheck-generic-indexes-effect-by-why = `{ $generic }` は effect を `{ $wanted }` で添字づけます: { $why }
nibcheck-generic-indexes-effect-by-unknown = `{ $generic }` は effect を `{ $wanted }` で添字づけますが、ここでは分かりません
nibcheck-arguments-rows-name = 引数の行が `{ $wanted }` を { $found } と名指ししています。どちらかを型注釈で書いてください
nibcheck-call-row-two-instances = この呼び出しの周りの行に、添字に使う effect `{ $wanted }` のインスタンスが 2 つあります: { $found }。どちらかを型注釈で書いてください
nibcheck-argument-performs-it-as = 引数はそれを { $found } として perform します。結果の型でどちらかを書いてください

# 型が clone できない理由。

nibcheck-type-is-linear = { $ty } は線形です
nibcheck-type-has-no-clone = { $ty } には clone がありません

# Captures and the classes a type needs.

nibcheck-capture-kind-fixed = キャプチャ `{ $name }` は、関数の種が確定したあとに { $kind } と推論されました。キャプチャされた束縛に型注釈を付けてください
nibcheck-capture-kind-undetermined = キャプチャ `{ $name }` の種が決まりません。キャプチャされた束縛に型注釈を付けてください
nibcheck-needs-class = { $what } には { $class }({ $ty }) が必要です
nibcheck-needs-class-add-where = { $what } には { $class }({ $ty }) が必要です: where { $class }({ $ty }) を加えてください
nibcheck-class-type-undetermined = { $class }(?) の型が決まりません。引数から instance が決まらないメソッドは `{ $class }(T)::m(…)` のように instance を書いて呼びます
nibcheck-no-instance = インスタンス { $class }({ $ty }) がありません

# 値の使い方: move・借用・破棄。

nibcheck-lin-not-used = { $name } は使われていません
nibcheck-lin-arm-captures = 腕が { $what } { $name } を捕捉しています
nibcheck-lin-arm-moves-many-times = { $op } の腕は { $name } を move しますが、何度も実行されます
nibcheck-lin-borrowed-cannot-move = { $name } は借用されているので move できません
nibcheck-lin-closure-borrows-cannot-store = { $name } は { $borrows } を借用しているので保存できません
nibcheck-lin-var-moved-out-of-closure = { $name } は var なので、クロージャの外へ move できません
nibcheck-lin-used-after-move = { $name } が move のあとで使われています
nibcheck-lin-moved-in-loop = { $name } がループの中で move され、次の周回までに代入し直されていません
nibcheck-lin-live-across-many = { $name } は { $shown } をまたいで生きていますが、{ $shown } は ω 回再開します
nibcheck-lin-outer-var-across-many = handle の外の `var { $name }` が { $shown } をまたいで使われていますが、{ $shown } は ω 回再開するので、再開ごとに別の写しになります
nibcheck-lin-used-some-paths = { $name } は一部の経路でしか使われていません
nibcheck-lin-lend-to-borrowed-parameter = 借用を貸せるのは、借用の引数だけです
nibcheck-lin-lent-function-kept = 借りた関数は保存できません。呼ぶか、貸すことだけができます
nibcheck-lin-lent-function-to-generic = 借りた関数を貸せるのは、借りた関数として宣言された引数だけです
nibcheck-lin-this-closure-borrows = このクロージャは { $names } を借用しているので保存できません
nibcheck-lin-borrow-effect-argument = 借用は effect の引数にできません
nibcheck-lin-borrow-returned = { $name } の借用は返せません
nibcheck-lin-borrow-returned-through = { $name } の借用は返せません。値は { $effect } を通して { $name } を借りていて、その handle が { $name } を貸しています
nibcheck-lin-borrowed-in-budget = { $name } は budget の中で借用されていますが、止められた本体はそれより長く生きるかもしれません
nibcheck-lin-destructure = { $name } は { $class } です。{ $root } を分解してください
nibcheck-lin-consumes-captured = { $name } は捕捉した値を消費するので、1 回しか呼べず、借用の関数引数には貸せません
nibcheck-lin-borrowed-after-move = { $name } が move のあとで借用されています
nibcheck-lin-moved-while-borrowed = { $name } が、同じ呼び出しの中で借用されたまま move されています
nibcheck-lin-borrowed-twice = { $name } が 1 回の呼び出しで 2 度借用されています
nibcheck-lin-borrowed-in-argument = { $name } は外側の呼び出しの前の引数が借用している間に、引数の中で再び借用されています
nibcheck-lin-drops-linear = `_` が線形な { $ty } を捨てています

# クラスと、使い方の診断の部品。

nibcheck-lin-class-shared = 共有
nibcheck-lin-class-affine = アフィン
nibcheck-lin-class-linear = 線形
nibcheck-lin-class-var = { $class } の var
nibcheck-lin-what-mut-borrow = &mut
nibcheck-lin-what-borrowing-closure = 借用しているクロージャ
nibcheck-lin-live-across-may-not-resume = { $name } は { $shown } をまたいで生きていますが、{ $shown } は再開しないかもしれません
nibcheck-lin-live-across-may-not-resume-div = { $name } は { $shown } をまたいで生きていますが、{ $shown } は再開しないかもしれません。ループは腕の前 (本体の中) で終えるか、燃料を与えて div をなくすか、操作を resume <=1 と宣言してください
nibcheck-lin-borrowed-by-arm = { $name } は { $op } の腕に借用されています
nibcheck-lin-frozen-by = { $name } は { $by } に凍結されています
nibcheck-lin-does-not-live-long-enough = { $owner } は、それを借りる { $name } ほど長く生きません
nibcheck-lin-holds-borrow-of = { $name } の借用を持っている
nibcheck-lin-shares-var = var { $name } を共有している
nibcheck-lin-continuation-only-in-arm = { $name } は { $why } ので、腕の中でしか呼べません

# 参照の循環。

nibcheck-cycle-unchecked = { $what } は、参照の循環を検査できない値を持っているかもしれません: { $why }
nibcheck-cycle-self = { $what } は、クロージャやデータ構造を通じて自分自身を持っているかもしれません。これは強い参照の循環です{ $path }
nibcheck-cycle-among = { $names } の間に強い参照の循環があります{ $path }
nibcheck-type-method-uses-value = `{ $name }` の本体はパラメータ `{ $param }` を使う型である: 型を与えるメソッドは、インスタンスが分かる場所で、引数の値ではなく型によって読まれる
nibcheck-borrows-result-holds-no-borrow = 結果 { $ty } が借用を抱えない関数に `borrows(…)` が書かれています
nibcheck-borrows-not-a-borrowed-parameter = `borrows(…)` の `{ $name }` は借用を貸す引数ではありません
nibcheck-lin-not-in-borrows = 結果が { $name } を借りていますが、{ $name } は borrows(…) にありません
nibcheck-let-unknown-prop = `{ $word }` は `let` の性質ではありません。書けるのは `let(stack)` だけです
nibcheck-stack-var = `{ $name }` は `var` です。`stack` を書けるのは `let` だけです
nibcheck-stack-type-param = `let(stack) { $name }` の型 { $ty } は型パラメータ `{ $param }` を含み、フレームでの大きさが決まりません
nibcheck-stack-recursive = `let(stack) { $name }` の型 { $ty } は自分を含み、割り当てなしにはフレームに置けません
nibcheck-coerce-own-field = `{ $field }` は `{ $ty }` 自身のフィールドです。`{ $place }.{ $ty }::{ $field }` と書いてください
nibcheck-coerce-move = `{ $ty }` は { $allowed } でだけ `{ $target }` として使えます。中身を移動するには `coerce(owned)` と書いてください
nibcheck-coerce-lend-mut = `{ $ty }` は `&` でだけ `{ $target }` として使えます。`&mut` で渡すには `coerce(mut)` と書いてください
nibcheck-coerce-assign = `{ $ty }` は `&` でだけ `{ $target }` として使えます。フィールドに代入するには `coerce(mut)` と書いてください
nibcheck-coerce-duplicable = `&{ $ty }` は `&{ $target }` として渡せません。`{ $target }` は複製できる型なので `coerce(owned)` が要ります
nibcheck-lin-lending-operation-resumes-once = `{ $name }` は可変の借用を抱えうる値を答えるので、再開は高々一回です。`resume 1` か `resume <=1` と宣言します
nibcheck-lin-overwrite = { $name } の linear な値はこの代入で捨てられてしまいます。`replace` で取り出してください
nibcheck-pattern-cannot-match-labelled = { $pattern } のパターンは、ラベル { $label } の下にある { $target } に一致できない。パターンにラベルを付けて書く（`{ $label } { $name }`）か、値の注釈でラベルを外す（`match (e: { $pattern }(…))`。`@a T <: T` による）
nibcheck-index-entry-writes-body-row = `{ $entry }` は本体が行う効果を隠します。本体の行を書きます: `∀ T. { $head }(() -> T ! {"{"}…{"}"})`
nibcheck-lent-struct-without-owner = struct &{ $name } には同じモジュールで宣言した型 { $name } が要ります
nibcheck-lent-struct-generics = struct &{ $name } は { $name } と同じ型引数を取ります
nibcheck-lent-struct-field = struct &{ $name } のフィールド { $field } は duplicable でも借用でもありません
nibcheck-lent-struct-without-lend = struct &{ $name } には同じモジュールに Lend({ $name }) の instance が要ります
nibcheck-export-twice = exports に `{ $name }` が二度ある
nibcheck-export-unknown = exports の `{ $name }` はプログラムの関数ではない
nibcheck-export-generic = exports の `{ $name }` はジェネリクスを持つ。ジェネリックな関数には export できる自分のコードがない
nibcheck-export-unknown-tote = exports に `{ $tote }::*` があるが、`{ $tote }` はプログラムが読む tote ではない（tote は Tauto.eure の `name` のとおり、`-` もそのまま書く。import 名ではない。読む tote: { $known }）
nibcheck-export-ambiguous = exports の `{ $name }` は複数のファイルが宣言している。{ $candidates } のどれかを書く
