# 公開範囲：`pub` と `pub(open)`

宣言は既定で、それを書いたファイルの中でだけ見える。ほかのファイルから使わせる宣言には `pub` を、中身まで見せる型と effect、外のファイルにも instance を書かせる class には `pub(open)` を付ける。

```tauto
fn helper(): i64 { 1 }                       // このファイルの中だけ
pub fn escape(t: Text): Html { Html { html: t } }

pub struct Html { html: Text }                 // 外からは型の名前だけ（抽象型）
pub(open) enum Shape { Circle(i64), Square(i64) }  // 構成子とフィールドも見える

pub effect session(): UserId               // 外からは perform と行への記載だけ
pub(open) effect ask(q: Text): i64         // 外のファイルも腕を書ける

pub class Size(A: Type) { fn size(a: A): i64 }      // 外からは where とメソッドの呼び出しだけ
pub(open) class Ord(A: Linear) { … }                // 外のファイルも instance を書ける
```

## 規則

| 書き方 | 名前 | 型の構成子・リテラル・パターン・フィールド | effect の腕 | class の instance |
|---|---|---|---|---|
| なし | 宣言したファイルだけ | 宣言したファイルだけ | 宣言したファイルだけ | 宣言したファイルだけ |
| `pub` | どのファイルからも | 宣言したファイルだけ | 宣言したファイルだけ | 宣言したファイルだけ |
| `pub(open)` | どのファイルからも | どのファイルからも | どのファイルからも | どのファイルからも |

- `pub` を付けられるのは `fn`、`theorem`、`axiom`、`def`、`inductive`、`struct`、`enum`、`effect`、`class` で、`mutual { … }` の中の宣言にも付けられる。それ以外の文の前の `pub` は誤り。
- 型の `pub` は型の名前だけを見せる。外のファイルは値を受け取り、渡し、行と型に書けるが、作ることも分解することもできない：構成子の呼び出し、構造体のリテラル、構成子と構造体のパターン、`x.f` の読み書き、カーネルが作る `T::rec`・`T::ind`・`T.noconf` は、宣言したファイルの中でだけ書ける。`T::beq` などの等価は型の名前と同じく見える。
- effect の `pub` は操作の名前を見せる。外のファイルは `perform` でき、関数の行に書け、行変数で素通しできる。`handle` の腕でその操作に答えられるのは宣言したファイルだけである。宣言したファイルが答えを決める関数（`pub fn with_session(user, body)` など）を公開すれば、外のファイルはそれを通して答えを与えられる。それはそのファイルの判断になる。
- class の `pub` はクラスの名前を見せる。外のファイルは `where C(T)` に書け、メソッドと法則を呼べる。`instance C(…)` を書けるのは宣言したファイルだけである（sealed）。外のファイルにも instance を書かせるときは `pub(open)` を付ける。sealed は名前の解決の検査で、instance の集合が閉じていることを型や証明の推論には使わない：「C を満たす型はこれだけ」という定理も、instance についての場合分けもない（閉じた場合分けが要るなら enum を使う）。宣言したファイルがあとから instance を足しても、外の証明は壊れない。
- `pub` の関数の `where` に、同じファイルが `pub` なしで宣言した class は書けない。ほかのファイルはその class を名指せず、境界を満たせないからである。
- 書き方は書く量の多い方が開く。書き忘れは閉じる側に倒れ、閉じすぎはコンパイルエラーで分かる（Safe by Default）。
- 範囲は tote ではなくファイルである。tote の中の別のファイルにも見せるときは `pub` を付ける。tote の中だけに見せる `pub(tote, open)` のような範囲は、必要な例が出てから括弧の中に足す。
- 検査はマクロの展開の後に、名前の解決（`crates/tauto-surface/src/surface/qualify.rs`、`sealed_visibility`）で行う。マクロが別のファイルに展開した構成子や腕は、展開先のファイルのものとして検査する。
- マクロが作る宣言の公開範囲：属性マクロ（`@m!(…) => …`）が作る宣言は、属性を付けた宣言と同じ公開範囲になる。呼び出しのマクロ（`m!(…) => fn a`）と `syntax` が作る宣言は `pub(open)` になる。

## 見える範囲

ファイルが見る宣言は、そのファイル自身の宣言、そのファイルが直接 `import` したファイルの `pub` の宣言、prelude の core の宣言だけである（core 以外の prelude のファイルは `import std::prelude::Os` のように import して見る。「prelude」）。import は推移しない：`a` が `b` を import し、`b` が `c` を import していても、`a` から `c` の宣言は見えない（`a` が `c` を使うなら `a` が `c` を import する）。同じ tote のファイルも、プログラムに読み込まれているだけのファイルも、import していなければ見えない。見えない名前を書くとエラーになり、その名前を宣言するファイルが分かるときは、そのファイルを import するよう案内する。

import が一覧を書くとき（`import std::Text { Text, concat }`、[`syntax.md`](syntax.md)「import」）、ファイルがその import を通して使えるのは一覧の名前と、一覧の型の構成子と型のために作られる名前、一覧の module の関数だけである。それ以外の名前をその import を通して使うと、一覧に書き足すよう案内するエラーになる。一覧にあって使っていない名前と、import したファイルが `pub` で宣言していない名前もエラーである。一覧が持ち込まない名前はその import からは見えないので、二つのファイルが同じ名前を宣言していても、一方の import の一覧だけがその名前を書くなら曖昧ではない。どの名前がどの import から来るかは名前の解決の結果で決まる。prelude のファイル（`std::prelude::Os`）の一覧に書いた prelude の名前は、使っていなくてもエラーにならない。

見える宣言の中で、同じ種類の名前（関数、型、コンストラクタ、module、class）が重なると、どれかを選ぶことはせず、曖昧であるというエラーになる。完全な名前（`a::t`）で書けば、どの宣言かを指せる。ファイル自身の宣言と、import したファイルの `pub` の宣言が同じ名前のときも同じである。module は同じ名前の block を開き直すと中身が合わさるので、module どうしは重ならない。module と class の名前は、入れ子のどの深さでも重ならない。

## prelude

prelude は、見えるものを core とそれ以外に分ける。

- **core** は import なしで見える。リテラルと組み込みの構文が作る、または求めるものだけである：カーネルの prelude（`Nat`、`Bool`、`Eq` など）、リテラルの型（`Text`、固定幅の整数、`Float`）と `Unit`・直積、リスト・直積のリテラルと `perform show`・`test` が使うデータと effect（`Option`、`List`、`Pair`、`Ordering`、`Result`、`fail`、`test`）、整数と `Float` の幅の変換（`std/prelude/Std.taut`、`Text.taut`、`Num.taut`）。
- それ以外の `std/prelude/` のファイルは、std のほかのファイルと同じく import して見る。`import std::prelude::Os` のように、ファイルの道筋がそのまま module の名前になる：`Affine`（`Vec`、`HashMap`、`Slice`、`Buf`）、`Classes`（`ToText`、`join`）、`Macro`（マクロの作者が使う `Syn*`）、`Ord`、`Os`（標準エフェクト、`IoError`）、`Par`（`Task`、`spawn`、`Mutex`、`MutexGuard`）、`Secret`、`Shared`（`Array`、`Bytes`、`Map`）。import は推移しないので、ファイルが使う prelude のファイルはそのファイルが import する。import していないファイルでその名前を書くと、エラーになり、import するべき module を案内する。
- import していないファイルが、non-core の prelude と同じ名前の宣言を持つのは構わない：prelude のその名前は見えないので、重ならない。import すると、同じ種類の名前が見える宣言の中で重なり、曖昧であるというエラーになる。
- prelude のファイルが `pub` なしで宣言した名前（`Par.taut` の `Signal` など）は、そのファイルを import しても見えず、import したファイルの同じ名前の宣言と重ならない。
- `instance`、`syntax`、`macro` はどこからでも見える（import した module のクラスの instance が、import していないファイルで探索に使われる）。
- core の名前は常に見える。core の名前と同じ名前の宣言をファイル自身が持つと、そのファイルでは自分の宣言を指す。標準ライブラリのモデル（`std/Text.taut` など）がこの形で組み込みと並ぶ。
- 例外は prelude を持たない tote である。`Tauto.eure` の `package { prelude = false }` は、その tote のファイルから core のうち `std/prelude/` が宣言する名前（`Option`、`List`、`Pair`、`not` など）を外し、non-core と同じく `import std::prelude::Std`・`Text`・`Num` で見るものにする。カーネルの prelude（`Nat`、`Eq`、`BelowPair` など）と、言語の型（`Bool`、固定幅の整数、`Text` など）は外さない。標準ライブラリ（`std/` と `meta/` を持つ tote と、`import std::…` で読むそのファイル）は prelude を宣言する側なので、prelude を持たない。こうした tote のファイルは使う名前をすべて import から得るので、import のリストで何をどこから使うかを書ける。
- prelude のファイルの import にリストを書くと、そのファイルの名前のうちリストに書いたものだけが見える（型はその構成子とともに）。

中身の規則は同じで、prelude が `pub` とだけ書いた型（`Atomic`、`Array`、`Ref`、`Weak`、`Buf`、`Vec`、`HashMap`、`Slice`、`Mutex`、`MutexGuard`、`Pending`）はプログラムから作ることも分解することもできない。prelude のほかの型と、標準エフェクト（`std/prelude/Os.taut`）を含む effect は `pub(open)` で、テストで `handle` によって標準エフェクトを差し替える書き方（[`host-effects.md`](host-effects.md)「誰が答えるか」）はそのまま書ける。

## 構成子とパターンの束縛

パターンにただ一つ書いた名前は、そのファイルが見る構成子にその名前があれば構成子で、なければ束縛である。そのファイルが直接 import していないファイルの構成子は、名前を取らない。別の tote の `head` という構成子が、`Some(head)` の `head` を構成子に変えることはない。

## 証明とカーネル

カーネルは公開範囲を知らない。隠すのは名前の解決の検査だけで、カーネル、Lean のモデル、信頼の核は変えない。外の証明は宣言したファイルが `pub theorem` で出した補題を使う。定義的等価による計算は止めない：抽象は作れないこと・分解できないことの保証であり、表現を秘密にするものではない。

生成するコード（Rust、JavaScript）では公開範囲を消す。生成物を外の Rust や JavaScript のコードから直接いじることは、`extern` と `trust` の境界の外の話で、型が保証する範囲に入らない。

## 他の宣言の見え方

- `extern` の関数の見え方は公開範囲に左右されない（[`host-effects.md`](host-effects.md)「extern はその tote の中でだけ呼べる」）。`pub` を付ける対象ではない。
- 一覧のない `import` はファイルのすべての `pub` の宣言を修飾なしで見せる。一覧のある `import` は一覧の名前だけを見せる（「見える範囲」）。`as` はない。
- `syntax`、`macro`、`instance` はどこからでも見える（instance を書ける場所は class の公開範囲で決まる。「規則」）。

## 未決定

- `pub import`：import したファイルの `pub` の宣言を、import したファイルの宣言として再び公開する書き方。import が推移しないので、複数のファイルの宣言をまとめて見せるファイルは、これで再公開する。
