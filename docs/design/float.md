# 浮動小数 `Float`

`Float` は IEEE 754 binary64 の値である（[`nib.md`](nib.md)「値と型」）。
証明の言語では `std/Float.taut` が `Float` を 64 ビットの列として定義し、
四則・比較・平方根などを整数の計算で定義する。抽出はそれを Nib の `Float` と
演算に写す（「証明から見た `Float`」）。

## リテラル

小数点か指数を持つ十進数が `Float` のリテラルになる。値は書いた十進数に
もっとも近い `Float` である。表現可能な範囲を超えるリテラルは型エラーになる。
負の値は単項の `-` で書く。先頭の小数点、末尾の小数点、`inf`、`NaN` は
リテラルではない。`Decimal` のリテラルは定義されていない。

整数のリテラルは `Float` にならない。整数と `Float` を混ぜた演算は型エラーで、`Float::of_i64` で変換する（[`nib.md`](nib.md)「算術」、種類の違う数どうしの
演算は型エラー）。

`Float` のリテラルはパターンに書けない。比べるときは `==` か `<` を使う。

## 演算

- `+ - *` と単項の `-` は IEEE 754 のとおり（最近接偶数への丸め）。溢れは
  無限大、`0 * inf` などは NaN になり、実行時エラーにはならない。
- `/` は IEEE 754 の除算。ただし割る数が `0.0` か `-0.0` なら実行時エラー
  `division by zero`（Lean のモデル `FOp.flt` と同じ）。
- `< > <= >=` と `== !=` は IEEE 754 の比較。`0.0 == -0.0` は `true`、NaN は
  自分自身とも等しくない。`Float` は `PartialEq` だけを持ち、`DecEq` を持たない
  ので、`HashMap` のキーにはなれない（[`classes.md`](classes.md)）。

## 表示

`show` と `Text::of_float` は、読み戻すと同じ `Float` になる最短の十進表記を
使い、指数は使わない。同じ長さで同じだけ近い候補があるときは、数として大きい方を
使う。正の無限大と負の無限大は符号を保って表示し、NaN は `NaN` と表示する。
負のゼロは負号を保って表示する。これらの規則と境界ケースは
[`cases/eval/float.eure`](../../cases/eval/float.eure) で検査する。

## 関数

`std/prelude/Num.taut` の `extern` に並ぶ。他の prelude の `extern` と同じく、
署名は信頼の対象である。

| 関数 | 意味 |
| --- | --- |
| `Float::of_i64(n)` | いちばん近い `Float`（最近接偶数） |
| `I64::of_float(x)` | 0 の方向に切り捨てた整数。NaN、無限大、`i64` に収まらない値は実行時エラー `the number is too large` |
| `Float::of_text(t)` | リテラルと同じ書き方の数（先頭に `-` を許す）なら `Some`、それ以外は `None`。大きすぎる数は無限大 |
| `Text::of_float(x)` | 「表示」の文字列 |
| `Float::bits(x)`、`Float::of_bits(b)` | ビット列の `u64` との変換。NaN は正規化されたビット列になる |
| `Float::is_nan(x)` | NaN か |
| `Float::abs`、`Float::floor`、`Float::ceil`、`Float::trunc` | IEEE 754 のとおり |
| `Float::round(x)` | いちばん近い整数。ちょうど半分なら 0 から遠い方 |
| `Float::sqrt(x)` | 平方根。IEEE 754 で正しく丸める |
| `Float::cbrt`、`Float::exp`、`Float::ln`、`Float::log2`、`Float::log10`、`Float::pow(x, y)` | 立方根、指数、対数、べき |
| `Float::sin`、`Float::cos`、`Float::tan`、`Float::asin`、`Float::acos`、`Float::atan`、`Float::atan2(y, x)` | 三角関数と逆三角関数 |
| `Float::sinh`、`Float::cosh`、`Float::tanh` | 双曲線関数 |

## バックエンドの一致

評価器、Rust バックエンド、JavaScript バックエンドは、同じプログラムに同じ
ビットの `Float` を返し、同じ文字列を表示する。

- `+ - * /`、比較、`Float::sqrt`、`Float::abs`、`Float::floor`、`Float::ceil`、
  `Float::trunc`、`Float::round` は IEEE 754 が結果を一つに決めるので、
  どの実行環境の演算を使っても同じになる。
- 三角関数・指数・対数・べきなど、IEEE 754 が結果を一つに決めない関数は、
  実行環境の数学関数を使わない。実行環境ごとに最後のビットが違うためである。
  評価器と Rust バックエンドはランタイムの `crates/tauto-rt/src/float_math.rs`
  を呼び、JavaScript バックエンドは同じ算法を一つずつ同じ順の演算で書いた
  `crates/tauto-jsgen/src/float.js` を使う。二つが同じビットを返すことは、
  端の値を含む入力について、バックエンド間の一致をケースと API テストで検査する。
- 表示は Rust の `Display` を基準にし、JavaScript も同じ文字列を作る。表示の
  境界ケースは `cases/eval/float.eure` で検査する。

## 証明から見た `Float`

`std/Float.taut`（`import std::Float`）が証明の言語での `Float` である。

- `Float` は `float(bits: U64)`、64 ビットの列。定義は列を符号・整数・指数に
  分け、正確な結果を整数で計算し、最近接偶数に丸めて列に戻す。計算に現れる
  数はどれも `2^128` 未満なので、カーネルはその場で計算する。
- import すると、証明の中の `1.5` や `-3.0` は、その値にいちばん近い `Float` の
  対応するビット列と読む（`check/sugar.rs`）。
  `+` などの演算子は `Nat` のままなので、証明では `Float::add(a, b)` と書く。
- 定義のある関数：`Float::add`、`Float::sub`、`Float::mul`、`Float::neg`、
  `Float::div(a, b, h)`（`h` は `b` が 0 でない証明）、`Float::checked_div`
  （0 なら `None`）、`Float::eq`、`Float::lt`、`Float::le`、`Float::is_nan`、
  `Float::is_infinite`、`Float::is_zero`、`Float::abs`、`Float::sqrt`、
  `Float::trunc`、`Float::floor`、`Float::ceil`、`Float::round`、`Float::bits`、
  `Float::of_bits`、`Float::of_i64`、`I64::of_float_checked`（収まらなければ `None`）。
  `Refl` で閉じた演算を計算できる。浮動小数の受理・拒否・実行結果は
  `cases/eval/float.eure` で検査する。
- IEEE 754 が結果を一つに決めない関数（`Float::exp`、`Float::ln`、`Float::pow`、
  三角関数など）と `Text::of_float`、`Float::of_text` は **公理** である。
  検査される関数から呼べるが、証明はその値について何も知らない。使った宣言は
  `axioms: std.Float.Float.exp` のように報告される。抽出は、Nib の同名の
  builtin に写すこれらの公理だけを許す。
- NaN のビット列は IEEE 754 が決めないので、`Float::bits` は実行時もどの NaN にも
  正規化されたビット列を返し、定義の中でもすべての関数が列を `Float::raw` を
  通して読む。だからどのプログラムも NaN どうしを区別できず、定義と実行が
  食い違う所がない。
- 信頼するもの：抽出の写像の表（[`self-host.md`](self-host.md)）が定義どおりに
  振る舞うこと、公理にした関数の実装（`float.rs`、`float_math.rs`、`float.js`）。
  写像の一致は `crates/tauto-cli/tests/float.rs` で見る：定義をカーネルで
  計算した値と実機の値の照合を行う。実行結果の境界ケースは
  `cases/eval/float.eure` で検査する。

- Nib の型安全性（Lean のモデル `lean/Proto/Nib/`、[`semantics.md`](semantics.md)）は
  `Float`・`Float32` の値と `+ - * /` を含めて証明されている。`/` のゼロ除算はモデルでも
  実行時エラーで、証明の言語の `Float::div` はそれを証明で除く。

## `Float32`

`Float32` は IEEE 754 binary32 の値である。テンソルのように数を大量に持つ計算のための
型で、`Float` と同じ規則に従う。

- リテラルはない。`Float32::of_float(0.1)` が `Float` の `0.1` にいちばん近い
  `Float32`（最近接偶数、大きすぎれば無限大）、`Float::of_float32(x)` が同じ数の
  `Float`（正確）。種類の違う数どうしの演算は型エラーなので、`Float` と混ぜるときは
  どちらかに変換する。
- `+ - * /`、比較、`==` は IEEE 754 のとおりで、`/` の 0 除算は実行時エラー。
  `Float32` は `PartialEq` だけを持つ。
- 関数は `std/prelude/Num.taut`：`Float32::bits`、`Float32::of_bits`（`u32`）、
  `Float32::is_nan`、`Float32::abs`、`Float32::floor`、`Float32::ceil`、`Float32::trunc`、
  `Float32::round`、`Float32::sqrt`、および `Float32::exp`、`Float32::sin` など `Float` と
  同じ名前の数学関数。NaN のビット列は `0x7FC00000` に揃う。
- IEEE 754 が一つに決めない関数（`Float32::exp` など）は、同じ数の `Float` の関数の値を
  最も近い `Float32` に丸めたものと決める。`Float` の関数はどの実行環境でも同じビットを
  返すので、`Float32` の関数も揃う。
- `show` は同じ数を `Float` として書く。JavaScript バックエンドは `Float32` も
  `number` で持つので、
  どのバックエンドでも同じ文字列になる。
- 評価器と Rust バックエンドは `f32` で計算する。JavaScript バックエンドは `number` で
  計算し、`+ - * /` と `Float32::sqrt` の結果を `Math.fround` で丸める。`Float` の結果は
  `Float32` の桁の 2 倍より多くを持つので、二度丸めても一度で丸めた値と同じになる。

### 証明から見た `Float32`

`std/Float32.taut`（`import std::Float32`）は `Float32` を 32 ビットの列
`float32(bits: U32)` として定義する。`Float32::of_float` と `Float::of_float32` をビット
列の計算で定義し、四則・平方根・比較・整数部はそれを通して `Float` の定義に帰着する
（`Float32::add(a, b)` は `Float32::of_float(Float::add(Float::of_float32(a), Float::of_float32(b)))`）。
上の二度丸めの性質により、これは IEEE 754 の binary32 の演算と一致する。
`Float32::exp` などは `Float` と同じく公理で、抽出は Nib の同名の builtin に写す。

一致は `crates/tauto-cli/tests/float.rs` で見る。浮動小数の受理・拒否・実行結果は
`cases/eval/float.eure` と対応する backend cases で検査する。

## 数としての `Float`

`std/FloatReal.taut`（`import std::FloatReal`）は、`Float` のビット列と、証明が
扱う数とをつなぐ。実行されるのは `Float` だけで、ここにある定義は抽出されない。

- `Rat`（`std/Rat.taut`）は有理数 `num / (den + 1)`。分母は 0 にならない。
  `Rat::add`、`Rat::mul` は既約分数を返し、`Rat::eq`、`Rat::le`、`Rat::lt` は数として
  比べる（`Eq(Rat, …)` は表し方の等しさ）。
- `Float::val(x)` は有限の `x` が表す数（`Some`）、NaN と無限大は `None`。
  `+0` と `-0` はどちらも 0。
- `Float::of_rat(r)` は `r` にいちばん近い `Float`（最近接偶数）。大きすぎれば
  無限大、0 は `+0`、0 に丸まる数は `r` の符号の 0。
- IEEE 754 の規則「演算は正確な結果を丸めたもの」は、`Float::add(a, b)` が
  `Float::of_rat(Rat::add(va, vb))` に等しい（結果が有限で、`a + b` が正確に 0 でない
  とき）という形になる。四則のこの一致は `crates/tauto-cli/tests/float.rs` で
  カーネルに計算させて確かめている。一般の定理としての証明はない。
- `Float::finite(x)` は NaN でも無限大でもないこと。NaN を除きたい関数は、
  `Float::div` の `h` と同じく、`Eq(Bool, Float::finite(x), true)` を引数に取る。
- `Float::near(y, r, eps)` は `y` が数で `r` から `eps` 以内にあること。
  `Refines(g, f, eps)` は「どの有限の `x` についても `g(x)` は `f` の値から `eps` 以内」。
  数学としての正しさ（微分の規則など）は `f` の側で誤差なしに証明し、実行される
  `g` のずれを `Refines` で述べる。
- `Float::total_cmp` は IEEE 754 の `totalOrder`（`-0 < +0`）。`Float` の `==` と
  `<` は IEEE 754 の比較のままで、`Eq(Float, …)` はビット列の等しさである。
  三つは別のものである。

`Float32` には `Float32::val(x)`（同じ数の `Float` の `Float::val`）と
`Float32::of_rat(r)`（`r` にいちばん近い `Float32`）がある。`Float32::of_rat` は
`Float::of_rat` を経由せず直接丸める（二度丸めは一般の数では正しくない）。

カーネルは `2^128` 以上の閉じた数をその場で計算しないので、`Refl` で確かめられる
のは分母が `2^72` 未満に収まる数までである。

### 実数

`std/Real.taut` の `OrderedField(R)` は順序体の演算と法則の組である。実数を構成も
仮定もしないので、`F: OrderedField(R)` を取る定理は公理を増やさず、証明が与えた
どの `R` についても成り立つ。

## 二進の自然数 `BinNat`

カーネルが閉じた数をその場で計算するのは `2^128` 未満までである。それより大きな数の
計算は、`std/BinNat.taut` の帰納型で行う。カーネルの組み込みの計算を広げないので、
信頼する核は増えない。

- `Pos` は正の数で、下位のビットから読む：`One` は 1、`Bit0(p)` は `2p`、
  `Bit1(p)` は `2p + 1`。`BinNat` は `BinZero` か `BinPos(p)` である。`n` ビットの
  数は大きさ `n` の項になる。
- 演算は `add`、`mul`、`sub`（`b` が大きければ 0）、`compare`、`eq`。`sub` と
  `compare` は、符号つきの差 `PosDiff`（`Pos.diff`）から読む。
- `to_nat` と `of_nat` が `Nat` と行き来する。定理は公理を使わず、演算が `to_nat` を
  通して `Nat` の演算と一致することを述べる：`to_nat(of_nat(n)) = n`、
  `to_nat(add(a, b)) = Nat::add(to_nat(a), to_nat(b))`、`mul` も同じ形。`eq` は
  `eq_refl` と `eq_sound` で命題の等号と結ばれ、`compare(a, a) = Equal`、
  `sub(a, a) = BinZero` が成り立つ。
