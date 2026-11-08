# Nib — tauto から依存型と証明を除いた言語

Nib は、tauto から依存型と証明系を除いた言語の仕様です。
tauto は Nib の保守的拡張で、Nib のプログラムは tauto のプログラムとしても
同じ意味を持ちます。

```text
tauto = Nib + 依存型・宇宙・Prop・証明・全域性の検査
```

Nib は tauto の実装から独立に書きます。ほかの言語が Nib を目標として参照
することもできますが、この文書はそうした言語を前提にしません。

## 原則

Tauto の設計原則（少数の直交する概念、書き味より健全性、短さより明示性、一つのことに
書き方は一つ、既定で安全）をそのまま引き継ぎます。Nib では特に次の4つを優先します。

- **Minimalism。** 少数の直交する概念だけを入れる。ライブラリで書けるもの
  （単位付きの数、長さ付きの列、表）は言語に入れない。
- **AI-Native。** 暗黙の規則を入れない。数の自動拡張、オーバーロード、
  大文字小文字を区別しない名前、何にでも合う型は持たない。一つのことに
  書き方は一つ。
- **Soundness。** 型検査を通ったプログラムだけを実行し、型が実行時の値を
  正しく述べる。
- **Safe by Default。** 依存と実行は既定で疑う。副作用は effect で明示した範囲に
  とどめ、言語の外から暗黙に権限を得ない。

## 何が正か

Nib の正は、次の3つです。tauto の実装は正ではなく、食い違えば実装の側を
直します。

1. この文書と、それを補う設計文書：[`semantics.md`](semantics.md)（操作的意味論と
   計算体系）、[`ownership.md`](ownership.md)（所有権・借用・再開量）、
   [`classes.md`](classes.md)（型クラス）。
2. Lean のモデル（`lean/Proto/Nib/` などの、依存型を含まないモジュール）。
3. テストケース `cases/`。

この文書には実装のファイルを書きません。

## 値と型

| 種類 | 型 | 備考 |
| --- | --- | --- |
| 整数 | `i32`, `i64` など | 幅を明示した型だけを持ち、`Int` という型はない。溢れは実行時エラー |
| 十進数 | `Decimal` | 正確な十進小数 |
| 浮動小数 | `Float` | IEEE 754 binary64。リテラルは小数点か指数を持つ数（`1.5`、`2e10`）。証明の言語では `std/Float.taut` が 64 ビットの列として定義し、抽出が Nib の `Float` に写す（[`float.md`](float.md)） |
| 単精度浮動小数 | `Float32` | IEEE 754 binary32。リテラルはなく、`Float32::of_float(0.1)` で作る（[`float.md`](float.md)「`Float32`」） |
| 真偽 | `Bool` | `true`, `false` |
| 文字列 | `Text` | 連結の演算子はない。連結は関数で書く。リテラルは三つ：`"…"`（エスケープ `\\ \" \' \n \r \t \0 \u{X…}`、`\u{}` は16進1〜6桁）、`'…'`（エスケープなし、`'` は含められない）、``plaintext`…` ``（エスケープなし、バッククォートと改行は含められない） |
| 単位 | `Unit` | 値は `#()` の1つ。`()` は単位を書かない（`() => e` は引数のない関数）。型の位置に `#()` は書かない |
| 空 | `Never` | 値はない。空の集まりの要素型もこれ |
| 関数 | `(A, B) -> R ! ε` | `ε` は効果の行 |
| 構造体 | `struct` | 名前付きフィールド |
| 列挙 | `enum` | 名前付きのコンストラクタ |
| 和 | `A \| B` | union。結合・可換・冪等 |
| 積 | `A × B` | 直積。成員は書いた順に並び、`A × B` と `B × A` は別の型。`(A × B) × C` と `A × B × C` も別の型 |
| タグ | `@a T` | 書いた時点で存在する。値は変えず、型だけを区別する |

値がないことは、言語の型ではなく標準ライブラリ（`std/prelude/`）の
`enum Option` で表します。

`struct` と `enum` は型パラメータを `(A: Type)` と宣言できます（`<…>` は関数と定理の暗黙引数だけです）。型の適用は関数の呼び出しと同じく `Option(i64)` と書き、`Option<i64>` とは書きません。推論変数・エラー回復・実行時にしか
分からない値のための型は Nib の型では
ありません。実装が推論に使うのは自由ですが、検査を通ったプログラムには
残りません。

### ネイティブ型を返す関数の抽出

Tauto の通常の `struct` や `enum` を返す透明な型関数は、Nib に渡す前に型の
位置で展開します。たとえば `fn PayloadType(Env: Type): Type { Payload }` の
`PayloadType(Owner)` は `Payload` と同じ Nib 型になり、借用型の内側でも使えます。
型関数の宣言や型の値は実行時には残らず、実行時の式から型関数を呼ぶとエラーです。

この経路で扱う型関数の引数は `Type` のみです。本体には型名、型への適用、関数型、
借用型、積・和・タグの型式を書けます。関数型の効果行には宣言済みの単相の効果を
使えます。未定義の効果や型引数を取る効果、行変数はこの経路では拒否します。
型関数どうしの合成は展開しますが、再帰、
一般の計算、項の引数、効果、`opaque`、種の制約や `where` はこの経路では拒否します。
未使用の型関数も本体を検査し、結果で使わない引数も型であることを確認します。
カーネルで検査する依存型の関数と、その実行可能な値への抽出とは別の経路です。

## 所有権

詳しくは [`ownership.md`](ownership.md)。ここには要点だけを書きます。

- **種。** 型は `copy ⊑ shared ⊑ affine ⊑ linear` のどれかの種を持つ。
  `copy` と `shared` は何度でも使え、`affine` は高々一度、`linear` はちょうど
  一度使う。構造体と列挙は種を宣言できる（`affine struct Buf {}`、既定は
  フィールドから決まる）。フィールドのない構造体も波括弧は省けない。
  型パラメータの既定は `affine` で、関数なら `<A: Shared>`、型の宣言なら `(A: Shared)` のように、
  種を宇宙の名前 `Copy`・`Shared`・`Type`（affine）・`Linear` で書いて上限にする（`<A>` は `<A: Type>`）。
  種は Nib の検査だけが見て、カーネルには `Type` が渡る。型構成子の変数の上限は
  `(Type) -> Copy` と書く。
- **使用。** affine の束縛は move の後に使えず、linear の束縛はすべての経路で
  ちょうど一度使う。`var` に affine の値を入れられるが、閉包からは move できない。
- **借用。** `&x` と `&mut x` は引数と `let &x := …` にだけ書ける二級の値で、
  データに入れられない。関数から返せるのは結果の型が `&A` の関数が借用引数から派生した借用を返すときだけ
  （[`ownership.md`](ownership.md)「結果」）。`let &x` は持ち主を凍結し、一つの
  呼び出しの中の `&mut` と `&` の衝突は拒否する。複製可な `A` では `&A ≡ A`。
- **再開量。** `effect e(…): R resume ω` のように、各操作は継続を何回再開するかを
  宣言する（`0`、`<=1`、`1`、`ω`、既定は `<=1`）。行の変数は `<!e>` と `!` を付けて宣言し、
  `T ! e` と書いて使う（`!` は行の印で、使う側の名前に宣言の `!e` は付けない）。`<!e: <=1>` で上限を付けられる。
- **direct。** `effect log(t: Text): Unit direct` は、腕のどの経路も末尾の
  `k(e)` で終わる操作。腕は `direct` の効果だけを行え、
  `handle` の外の借用や `var` を借用閉包のように使える（move はできない）。
  `<!e: direct>` は行の変数を `direct` の操作だけに限る。`show` は `direct`。
  詳しくは [`rust-backend.md`](rust-backend.md) 「`direct` 操作」。
- **制御フロー線形性。** `ω` の効果を跨いで affine の値を持てず、`0` や `<=1`
  の効果を跨いで linear の値を持てない。継続を複製・破棄しても所有が壊れない
  ための規則で、呼び出しの引数、`while`（`Div`）、`budget`（`Exceeded`）にも
  掛かる。
- **標準ライブラリ。** ω の std（`std/prelude/Shared.taut`、`List`・`Map` など
  複製可のデータ）と affine の std（`std/prelude/Affine.taut`、`Buf`・`Vec`・
  `HashMap`、Rust と同じコスト）。境界は `Text::of` と `Buf::of` だけ。
- **extern。** `extern { fn … }` は署名だけの宣言で、tauto の公理と
  同じく信頼の対象。`tauto check` は一覧に出し、`tauto run` は呼べない。

## 型の関係

Nib が定める関係は2つだけです。

- **同値 `A ≡ B`。** 正規形の一致。タグは集合として比べ、入れ子のタグは
  合わせ、`Tagged<∅, T> ≡ T`。union は結合・可換・冪等で比べる。
  直積は成員を書いた順に比べる。`Unit` もほかと同じ一つの成員で、`A × Unit` は `A` と別の型。名前で書いた `Pair(A, B)` は `A × B` と同じ型。`×` は右に結合し
  `A × (B × C) ≡ A × B × C` だが、`(A × B) × C` は別の型（最後でない成員の直積は平らにしない）。
  反射・対称・推移を満たす。
- **部分型 `A <: B`。** 次の規則で閉じたもの。
  - 同値なら部分型。
  - タグは忘れられる（`@a @b T <: @a T`、`@a T <: T`）。付け足すことはない。
  - union への注入（`A <: A | B`）と、union からの出口（すべての成員が `C` の
    部分型なら `A | B <: C`）。
  - 直積は成員の型で対応づけて、成員を忘れたり並べ替えたりできる（`A × B <: A`、
    `A × B × C <: A × C`、`A × B <: B × A`）。付け足すことはない。項の型を期待された型に
    合わせる位置（型注釈 `(e: T)`、関数の引数、型つきの `let`、結果の型）だけで使い、
    関数の型の中、union の成員、`Option(A × B)` のような別の型の中では使わない
    （組み直す値がないため）。対応づけは、両辺に型変数がなく、それぞれの辺の成員の型
    （タグを含む）がすべて違うときだけで、そうでなければエラー（成員を同じ順に書くか、
    タグで見分ける）。整数リテラルのように幅が後で決まる成員は、整数の成員一つに当たる。
  - 関数は引数が反変、結果が共変、効果の行は小さい方が部分型。
  - `Never <: A`。

数の拡張（`i64` から `Decimal` など）は部分型ではなく、明示的な変換関数で
書きます。

## 直積

tauto での直積の構文は [`syntax.md`](syntax.md)「直積」に書きます。

`A × B` は union `A | B` と対になる型で、成員は書いた順に並びます。

- 型は `A × B × C`。`×` は `|` より強く結合し、`A × B | C` は `(A × B) | C`。
  中に union を書くとき、戻り値の型に書くときは波括弧で囲む：`{A | B} × C`。
  union のない戻り値の型に波括弧はいらない：`fn f(): i64 × Text`。
- 値は `#(1, "a")`。成員は書いた順に評価し、その順に並べる。値の成員が
  `#()` なら並べない（`#(a, #())` は `a`）。`#(#(a, b), c)` の `#(a, b)` は一つの成員のまま。
  パターン `#(x, y)` は成員に位置で当たり、`#(p, #())` は `p` である。ラベルをすべての成員に付けたパターン
  （`#(@a x, @b y)`）は、ラベルで成員に当たる。
- 成員は部分型と型注釈で取り出す：`(x: T)` は型 `T` の成員、`(x: @a T)` はタグの
  付いた成員、`(x: A × C)` は成員を減らした直積。`.` の後ろは常に名前で、型で
  取り出す別の書き方はない。
- 同じ型の成員を二つ持つ直積も作れ、位置で区別する（`i64 × i64`）。型で取り出せるのは、
  型が重ならない閉じた直積だけ。同じ型の成員はタグで分ける：`@x 1 × @y 2`。
- 型変数は一つの型として扱い、型が完全に一致する成員を選ぶ（`fn f<K, V>(p: K × V): V × K` は通る）。
  同じ型の成員が二つある（`V × V`）ときは位置で書く。
- 所有権は struct と同じ。種は成員の種の join で、場所から取り出せるのは複製できる
  成員だけ。
- `show` の表示は成員の表示を書いた順に ` × ` でつないだもの：`1 × true × "a"`。

## 算術

- 整数型の `+ - *` と単項 `-` は、溢れたら実行時エラー。折り返さない。
- 整数どうしの `/` は型エラー。整数の除算は Tauto と同じ名前つきの関数（`Nat::div`・`Nat::rem`、
  `Int::tdiv`・`Int::tmod`・`Int::fdiv`・`Int::fmod`、固定幅の整数の `div`・`rem`）で書き、十進数にするには
  `decimal(x)` と書く。0 で割ると effect `DivZero` が起き、結果の型の行に `DivZero` が載る（`Nat::div(a, b): Nat ! {DivZero}`）。
- `Decimal`、`Float`、`Float32` の `/` はその型の除算。ゼロ除算は実行時エラー。
- 続けられない値（壊れた不変条件）で止めるのは `perform stop(message)`（[`host-effects.md`](host-effects.md)）。
  効果なので行に `stop` が出て、ハンドラが答えられる。答えがなければ `message` を出して止まる。
  呼び出し元が扱うべき失敗は `Option`・`Result`・`fail` で書く。
- 幅の違う整数どうし、種類の違う数どうしの演算は型エラー。変換は明示的に書く。
- 秘密の値 `Secret(A)` は `secret` で作り、定数時間の `ct_` の関数と `expose` でだけ読む（[`secret.md`](secret.md)）。

## 名前

- 名前は大文字小文字を区別する。
- 同じ名前の関数を二つ定義できない（オーバーロードはない）。
- 宣言は完全修飾名（`app.List`、`std.prelude.List`）で区別する。別のファイルや prelude と同じ名前の宣言は別の宣言で、ファイルの宣言 → `import` したファイル → prelude の順に解決する（[Rust バックエンド](rust-backend.md)「完全修飾名」）。
- `struct` と `enum` の宣言名は、両方を合わせて重複できない。

## 文と式

`let`、`var` と `:=`（`x.f.g := v` は `var` か `&mut` の変数のフィールドを書き換える）、`fn`、`if`、`match`、`while` と `loop`、`return`、
`struct`・`enum`・`effect` の宣言。

真偽値の否定は関数 `not(b)` で書く（`!` はマクロの呼び出し `m!(…)` と効果の行 `! {E}` にだけ使う）。
`if`・`while`・`match` の条件と対象の式には、名前の直後に `{` が来る struct のリテラルを書かない。`{` はその後ろのブロックの
始まりと読まれるので、書くときは括弧で包む（`if (ready {}) { … }`）。

`match` は網羅的でなければならない。`_ =>` の既定の腕は書ける。既定の腕は最後に一つだけで、前の腕が
覆っていない値が一つ以上残るときだけ書ける（証明の言語と同じ）。enum の
コンストラクタをすべて明示させたい場合は、言語の規則ではなく lint で強制する。

ガード付きの腕 `p if g => e` は、`p` の腕を `match g { true => e false => … }` にし、`…` をその後ろの腕の
`match` にしたものと同じ（証明の言語でも同じ糖衣で、カーネルはガードのない `match` を受け取る）。ガード付きの腕は
網羅性の判定では値を覆わない。

`match e: G` の `G` は `match` 全体の型、腕の `C => ⊢ G' from p` の `G'` はその腕の本体の型で、Nib もこれを検査する。
`G` や `G'` が局所の値に依存する（局所の名前を含む）なら、それは証明の型なので Nib はエラーにする。

整数・`Text` の値のリテラルはパターンに書ける（`x == リテラル` の分岐への糖衣）。最後には名前つきの
残りの腕（`other => …`）が要る。`std/` と `meta/` の lint `rest-arm` は、名前つきの残りの腕を、値が無限にある
これらの型のリテラルの後ろに限って許し、コンストラクタや `Bool` の後ろでは拒否する。

添字つきの型の `match` では、`std/` と `meta/` の lint `indexed-arm-goal` が各腕に目標（`C => ⊢ G' from p`）を
求める。lint は型を見ないので、対象は同じファイルで宣言した添字つきの型のコンストラクタを挙げた `match` である。

異なる enum は同じコンストラクタ名を持てる（同じファイルの `inductive` どうしも同じ）。パターンの短い名前は match 対象の
型で解決する。式では型注釈、関数の戻り値、引数などから所有する型が一つに
決まる必要がある。決まらなければ曖昧性を報告し、宣言順では選ばない。
`型名::コンストラクタ名` は所有する型を明示する。値の後ろの `.` はフィールドの射影だけである。
期待型が union などで所有する型を一つに決められない場合も修飾名を使う。
コンストラクタの同一性は所有する型とその型の中の選択肢であり、短い名前だけではない。

## 評価

- 値呼び。関数を評価し、引数を左から右に評価し、本体を実行する。
- クロージャは環境を持つ。`var` はセルに格納し、クロージャと継続はセルを
  共有する。
- 実行の結果として観測できるのは、効果の順序と状態変更の順序。プログラムの
  結果は専用の構文ではなく、ホストが処理する観測の操作 `show` で外に出す。
  テストはホストが記録した操作の列を比べる。
  budget がどこで切れるかは観測の対象にしない（下の budget）。

`show` はホストが宣言する操作で、どこでも使える。

```nib
effect show<A>(name: Text, value: A): Unit
```

`perform show("x", v)` をどのハンドラも処理しなければ、ホストが名前と値の
表示を記録し、`#()` で続ける。プログラムが `show` の腕（`∀ A. show<A>(n, v), k => …`）を持つハンドラを書けば、
その中ではそのハンドラが処理する。

## 効果

- `effect Ask(q: Text): i64` で操作を宣言し、`perform ask("a")` で行う。
- 関数の型は効果の行を持つ。行に入っていない効果は行えない。
- 効果の同一性は宣言と型引数の **同値** で決め、部分型では決めない。
- ジェネリックな操作は、行と腕にどの実体かを必ず書く。`! {res(Pos)}` と
  `res<Pos>(), k => …` は一つの実体、`! {∀ A. res(A)}` と
  `∀ A. res<A>(), k => …` はすべての実体（型引数を順に束縛する）。すべての
  実体に答える腕は、どの型引数でも動かなければならない。省いた `{res}` や
  `res(), k => …` はエラー（[semantics](semantics.md)「Effects indexed by type」）。
- 型引数に置いた関数の型も効果の行を持つ。`List(() -> i64 ! {stdout})` の要素は
  `stdout` だけを行え、取り出して呼べばその行が呼んだ側に加わる。型引数は不変なので、
  `List(() -> i64 ! {})` を `List(() -> i64 ! {stdout})` として渡すこともしない
  （`Ref` や `HashMap` は中身を書き換えられるため）。値を作る場所では書かれた型が
  型引数を決め、各要素がその行に収まるかを確かめる（リストのリテラル `[f, g]`、
  空の `Nil`、`HashMap::new()` も同じ）。
- **効果の集まり。** `effect Talk { log, stdout }` は効果の集まりに名前を付ける。行に
  `Talk` と書けば、その効果を並べて書いたのと同じ（`{Talk} ∪ e` は `{log, stdout} ∪ e`）。
  集まりは他の集まりを含められるが、自身を含めない。集まり自身は操作を持たず、
  `perform` も腕も書けない。行の検査の前に効果へ展開されるので、カーネルにも
  集まりの名前にも宣言の公開範囲と import 一覧の規則が適用される。
  メンバーは集まりを宣言したファイルで解決し、その宣言の参照を展開先でも保つ。
  集まりを import しても、非公開のメンバー操作そのものの名前は持ち込まない。
  行の検査にも規則を足さない。型引数を持つ集まり（`effect State(T: Type) {…}`）は読まない。
- **集まりで上界を付けた行の変数。** `<!h: Host>` の `h` は、`Host` の効果のうちいくつかだけを
  表す。`h` は `Host` の効果を許す行に収まり、呼び出しで `h` に代入できるのは
  `Host` の効果（と、`Host` 以下で上界を付けた行の変数）だけ
  （`log is not in Host, which bounds h`）。
- `handle { body } with { ask(q), k => arm … ; return v => r }`。ハンドラは
  deep。`k(v)` は同じハンドラの中に戻る。腕はハンドラの外で動く。継続を
  何度再開できるかは操作の宣言の `resume` が決める（multi-shot は `resume ω`）。
- 停止しないかもしれない計算は `Div` を持つ（`while`、再帰、継続を保持する
  ハンドラ）。
- **ハンドラの結果型は、各腕と `return` 腕の型の union。** 数の拡張はしない。

## budget

- `budget(steps: n) { body }` は、本体が `n` ステップを超えたところで止め、
  budget の式の位置で `Exceeded` を行う。`Div` は行から消え `Exceeded` が入る。
- `exceeded(info), k` の腕は `info` を受け取る。`info.more(m)` は `m`
  ステップを足して止まった本体に戻り、`info.unbounded()` は上限なしで戻る。
  継続 `k(v)` は budget の式全体の値を `v` にして先へ進む。`k` の引数は
  本体の型で、`k(v)`・`info.more(m)`・`info.unbounded()` の値はどれもハンドラの
  結果型を持つ。`info.unbounded()` は止まらないかもしれないので `Div` を行う。
- ステップの数え方は実装が決めてよく、実装どうしで一致しなくてよい。仕様が
  求めるのは、停止しない本体がいつか必ず `Exceeded` になることと、入れ子の
  budget のステップが外側の budget のステップにも数えられること。
- 外側のホストの制限は `Exceeded` ではなく `Interrupted` で、効果ではない。

## 並列のプリミティブ

`std/prelude/Par.taut` が std に入れる、タスクと共有の状態。意味は評価器が決め、Rust バックエンドは
リアクター（コアごとのスレッドに多くのタスク）かタスクごとのスレッドで走らせる。

### タスク

```nib
effect Host { Div, stdout, stderr, stdin_bytes, stdout_flush, shutdown_token, argv, wall_clock, monotonic_clock, sleep, random, secure_random, fs_read, fs_write, fs_read_bytes, fs_write_bytes, fs_read_under, fs_read_bytes_under, fs_create_dir, fs_list_dir, fs_remove, fs_stat, fs_read_link, fs_write_new, fs_rename, fs_copy, fs_canonicalize, fs_temp_dir, proc_spawn, proc_read, proc_write, proc_close_stdin, proc_wait, proc_close, proc_run, env, net, net_addr, net_resolve, tcp_listen, tcp_accept, tcp_connect, tcp_read, tcp_write, tcp_shutdown, tcp_close, tcp_unlisten, tls_accept, tls_connect, tls_read, tls_write, tls_shutdown, tls_close, wait }
effect spawn<A>(f: () -> A ! {Host}): Task(A) resume 1
linear struct Task(A: Type) { result: Pending(A) }

fn Task::join<A>(t: Task(A)): A ! {wait}
fn Task::detach<A>(t: Task(A)): Unit
fn par<A, B>(f: () -> A ! {Div, wait}, g: () -> B ! {Div, wait}): Pair(A, B) ! {∀ T. spawn(T), wait}

fn spawn_all<A>(bs: List(() -> A ! {Div, wait})): List(A) ! {∀ T. spawn(T), wait}
fn Task::join_all<A>(ts: List(Task(A))): List(A) ! {wait}
```

- `spawn` は効果で、`Task` は linear（`Task::join` か `Task::detach` のどちらかで使い切る）。
  `join` は Text の `join` と名前が衝突するので `Task::join`。
- タスクの本体 `f` は `Div` と、標準エフェクト（[`host-effects.md`](host-effects.md)）のうち `stdin` と `exit` を除くものを許可する。
  それ以外の、呼び出し元のハンドラを使う操作は許可しない。タスクどうしは `Ref` / `Mutex` / `Atomic` で話す。
- タスクの標準エフェクトは **ホストが答える**。`spawn` を囲むハンドラは答えない（タスクは別のスレッドで走りうるが、継続はスレッドを越えない）。
  実行の権限（`--allow-*`）はタスクにもそのまま効き、範囲外の要求は `Err(Denied(..))` になる。
  - `perform spawn(f)` の行には、`f` が行う標準エフェクトが入る。`spawn` を行う関数の型を見れば、タスクがファイルを読むのか、ネットワークに出るのかがわかる。
  - 実行前の権限の確認は、タスクが行う標準エフェクトも数える（`RowReport::task_effects`）。`spawn` の外でハンドラがその効果を答えていても、タスクの分はホストに届くので数える。
  - 実装は、プログラムを `host_run` で包むときに（[`host-effects.md`](host-effects.md)「誰が答えるか」）、各 `perform spawn(f)` を `perform spawn(() => host_run(f))` にする。評価器・Rust・JavaScript のどれでも、タスクの中の `host_run` が答える。
  - `stdin` は主の流れのもの（タスクどうしで一行を取り合わない）、`exit` は実行全体を終えるので、タスクには許さない。
- タスクの中で利用者の効果を使うには、そのハンドラを **タスクの本体の中に** 張る。
  タスクを起動するライブラリは、本体にする関数の行を `Host` で上界を付けた行の変数にする。
  利用者は自分の効果のハンドラで包んだ関数を渡す。

  ```nib
  // ライブラリ：接続ごとにタスクを起動する。利用者の効果を知らない。
  fn serve<!h: Host>(conn: (c: Conn) -> Unit ! h): Unit ! {∀ T. spawn(T), tcp_accept} ∪ h { … }

  // 利用者：`log` のハンドラで包む。包んだ関数がタスクの中で走る。
  serve((c) => with_log(() => handle_conn(c)))
  ```

  - 答え手はコードに書かれたとおりで、`spawn` を囲むハンドラに暗黙に転送されることも、
    複製されることもない。ハンドラが持つ状態はタスクごとに作られ、タスクをまたいで
    共有するものは `Mutex` / `Atomic` / `Ref` に置く。
  - `h` は `serve` の行にも書く（`spawn` の行にタスクの効果が入るのと同じ理由）。
    呼び出しでは `h` に実際の効果（上の例で `with_log` が `stdout` に書くなら `{stdout}`）が入るので、
    実行前の権限の確認は使う分だけを求める。行を `{Host}` と書くと `Host` のすべてが入り、
    すべての権限を求めることになる。
  - 本体が `Host` にない効果を行うと、行の検査はハンドラを本体の中に置くよう案内する。
- 三つ以上のタスクを同時に走らせるには `spawn_all` を使う。すべての本体を `spawn` してから、結果を本体の順に `List` で返す。
  本体は `par` と同じく `Div` と `wait` だけを行う（`Mutex` や `Channel` で互いを待てる）。ホストに頼む効果を行う本体は `perform spawn` で一つずつ始め、`Task::join` する。
  `Task` を持ったまま `Div` を跨ぐことはできない（`Div` は `resume 0` で、`budget` の下では `Exceeded` になって続きが捨てられうるので、
  linear が捨てられる）。`spawn_all` と `Task::join_all` は構造的な再帰なので `Div` を行わず、この規則を緩めずに書ける。
- `spawn` はトップレベルまで届けばホストが答える（`show` や `test` と同じ）。どこで本体を走らせるかはホストが決め、評価器は `spawn` の場所で本体を最後まで走らせる。
  プレリュードに `spawn` のハンドラは置かない。本体を腕の中で走らせるハンドラは、`resume 1` の `k` を持ったまま `Div` を跨ぐので書けない（[`ownership.md`](ownership.md)）。

### 共有の状態

| 型 | 中身 | 操作 |
|---|---|---|
| `Ref(A)` | 取り替えられる一つの値 | `Ref::new`, `Ref::get`（A は shared）, `Ref::set` |
| `Mutex(A)` | 一度に一つのタスクが持つ値 | `Mutex::lock(m): MutexGuard(A)`（待って中身を Guard に取る。Guard を捨てると返る）、`Mutex::take`, `Mutex::put` |
| `MutexGuard(A)` | ロックした `Mutex` の中身 | `MutexGuard::get(&g): &A`, `MutexGuard::get_mut(&mut g): &mut A`。ブロックの終わりで捨てられると、ホストの Drop が中身を `Mutex` に返す |
| `Atomic` | `u64` | `Atomic::new`, `Atomic::load`, `Atomic::store`, `Atomic::fetch_add`（SeqCst） |

どれも shared（ハンドルの複製が同じ入れ物を指す）。`Mutex` に毒化はない。

### タスクの間で待つ

| 型・関数 | 中身 | 操作 |
|---|---|---|
| `Semaphore` | 残りの許可の数 | `Semaphore::new(n)`, `Semaphore::acquire`（残りが 0 なら待つ）, `Semaphore::release` |
| `Channel(A)` | 上限つきの FIFO | `Channel::new(capacity)`, `Channel::send`（満杯なら待つ）, `Channel::recv`（空なら待つ。閉じて空なら `None`）, `Channel::close` |
| `Task::poll(t)` | 待たずに見る | 終わっていれば `Finished(v)`、まだなら `Running(t)` でタスクを返す |

`Semaphore` と `Channel` は prelude の Tauto で `Mutex` の上に書く（セマフォは、数を持つ `Mutex` と、数が 0 より大きいときだけ満ちている門の `Mutex` の二つで作る）。

タスクの間で待つのは、すべて `std/prelude/Par.taut` のエフェクト `wait(s: Signal) -> Unit` である（[`host-effects.md`](host-effects.md)）。`Signal` は
ホストが一度だけ上げ、二度と下げない旗で、`Task::join` はタスクの終わりの旗を、`Mutex::take` と `Mutex::lock` は中身がこの呼び出しに渡された旗を待つ。
`Signal` は `Par.taut` に `pub` なしで宣言するので、Par を import したファイルの `Signal` と重ならず、プログラムは旗を作ることも名前で書くこともできない。
`wait` は `pub`（`pub(open)` ではない）なので、行に書くことと素通しはできるが、`handle` の腕で答えるのはホストだけである。

```nib
fn Task::join<A>(t: Task(A)): A ! {wait}                 // perform wait(Pending::signal(&result)) のあと Pending::take
fn Mutex::take<A>(m: Mutex(A)): A ! {wait}               // Mutex::claim で列に並び、その旗を待ってから Mutex::take_claimed
fn Mutex::lock<A>(m: Mutex(A)): MutexGuard(A) ! {wait}   // 同じく待ち、中身を Guard に取る
```

`MutexGuard(A)` は affine なホストの型で、捨てられるとホストの Drop が中身を `Mutex::put` と同じに返す（列の先頭が待っていれば、その旗を上げる）。
Drop は効果を行わず、ホストの Drop は信頼である。Guard の中身は、Guard の借用 `MutexGuard::get` / `MutexGuard::get_mut` が返す借用で読み書きし、
その借用が生きているあいだ Guard は動かせず、捨てられない。評価器と Rust は値が最後に捨てられたとき、JavaScript はスコープが閉じたとき、
バイトコード機械（Rust）はブロックの終わりに（`Cps::Define` の `drop`）局所を空にして返す。

```nib
let m := Mutex::new(Vec::new())
{
  var g := Mutex::lock(m)
  let &mut v := MutexGuard::get_mut(&mut g)
  Vec::push(&mut v, 1)
}   // g が捨てられ、ロックが外れる
```

- `Mutex::claim` は列に並ぶだけで待たない。中身があれば旗はすぐ上がり、なければ次の `Mutex::put` が列の先頭に中身を渡して旗を上げる。
  渡された中身は列のその場所のもので、ほかの `Mutex::claim` には取られない。
- 待つことが行に出るので、`Mutex::lock`、`semaphore_*`、`channel_*` の行には `wait` が入る。タスクの中の待ちはそのタスクのことなので、
  `spawn` の行には入らない。
- 待つ場所が一つの効果なので、ホストは一つのスレッドで多くのタスクを走らせ、一つが待つあいだにほかを進められる。
  `sleep` や `net` 系の答えを待つのも同じ `wait` である（[`host-effects.md`](host-effects.md)「時間のかかる答え」）。
- 評価器は本体を `spawn` の場で最後まで走らせるので、上がっていない旗を待つことは、どのタスクも上げられない旗を待つことであり、
  `deadlock` の実行時エラーになる。`Task::poll` が使う `Pending::is_ready` は待たない。

待つループは `Div` を行うので、linear の `Task` をまたいで持てない。送り手と受け手はそれぞれのタスクの本体に置き、外側では
両方を `spawn` してから `Task::join` する。評価器は本体を `spawn` の場で最後まで走らせるので、容量を超えて送る送り手は受け手を
待てない（Rust と JavaScript の backend では待てる）。

### var を共有する閉包と継続

`var` を捕まえた閉包は借用閉包（[`ownership.md`](ownership.md)「借用閉包」）として扱う: `&f` の引数に貸す・その場で呼ぶことは
できるが、保存・返却・タスクへの受け渡しはできない。`handle` の本体・return 腕・腕に `var` が
あるときの継続 `k` は、その腕の中でしか呼べない（[`ownership.md`](ownership.md)「借用と効果」の、外を借用する `handle` の `k` の規則の拡張）。これでタスクに渡る値は
`var` のセルを持たない。

Rust バックエンドでの実行は [`rust-backend.md`](rust-backend.md)「タスク（`spawn`）」。

## Nib に入れないもの

- **tauto にだけあるもの。** 依存型、宇宙、`Prop`、`theorem`・`axiom`・
  `inductive`、全域性の検査。
- **どこにも入れないもの。** 数の自動拡張、オーバーロード、大文字小文字を
  区別しない名前、何にでも合う型、長さや単位を持つ組込みの型。必要なら
  ライブラリで書く。
- **書き方を一つにするため入れないもの。** 比較の `=` と `<>`（`==` と `!=`
  だけ）、`<…>` による型の適用（`Option(i64)` だけ）、べき乗の `^`、添字の
  `[ ]`、`for`、可変長の引数と引数の既定値、穴 `?` と `try`。

## 適合の確かめ方

`cases/` にテストケースを置きます。形式は tauto のテスト
スイートと同じ `.eure` にし、tauto はこれを自分のテストとして実行します。
比べるのは、受理と拒否（`parses`）、型（`types`）、効果の行（`rows`）、
使用の検査（`lin`）、`show` の列（`shows`、動的な所有権検査をしても同じ列で
あること）、捨てた値の列（`drops`）、実行時エラー（`run_error`）です。予算切れの位置は
比べません。

## 未決定

ありません。
