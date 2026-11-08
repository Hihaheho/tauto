# effect を持つ計算の証明

effect を持つ関数と、それを動かすハンドラは、書いたまま定理に使える。精密化
（`crates/tauto-kernel/src/check/effects.rs`）がそれぞれを計算の木として読み、
カーネルは読んだ項だけを見る。カーネルに規則は足さない。実行する
プログラムは書いたとおりに読む。

例は `examples/handler-proofs.taut`、検査は `cases/check/effect-computations.eure`。

## 計算の木

カーネルの prelude（`crates/tauto-kernel/src/prelude.taut`）が持つ。

```text
inductive Comp(Op: Type, Res: (Op) -> Type, A: Type): Type {
  CompPure(a: A)
  CompOp(o: Op, k: (Res(o)) -> Comp(Op, Res, A))
}
```

`CompPure(a)` は `a` で終わった計算、`CompOp(o, k)` は操作 `o` を行い、
その答え（型 `Res(o)`）に `k` を当てて続ける計算。ハンドラは木の fold
（`Comp::fold`）で、継続は処理済みの木を返すので deep になる。継続を何度
呼んでもよいので multi-shot もそのまま表せる。

`Comp::bind`、`Comp::fold` の法則（モナド則、ハンドラの β 則、ハンドラと
`Comp::bind` の交換）は `std/Effect.taut` にあり、公理を使わない。継続の
等しさは関数外延性を使わず、点ごとの等しさ `CompEq` で述べる。

## effect の読み方

`effect e(P0, …): R` は三つの宣言を作る。名前に `@` を含むので書けない。

- `e@op`：操作。コンストラクタ `e@args(a0: P0, …)` 一つの帰納型。
- `e@res`：答えの型。`e@args(…)` に `R` を返す。
- `e@arm<B>`：引数と継続を取る関数から、`e` の腕を作る。

型の総称を持つ effect と、型がカーネルの型でない effect（`i64`、`Text` など）は
読まない。それを行う関数は理由つきで skip される。

## 行

行は effect を名前の順に一つずつ並べたもの。行の操作は
`OpSum(e0@op, OpSum(e1@op, … OpNone))`、答えは `res_sum(…)` で、どちらも
prelude の帰納型と関数。書いた順や重複は読みに影響しない。

### 行変数

`fn f<!e>(…): A ! {claim} ∪ e` の行変数 `e` は、`e` が表す effect の操作と答えの
二つの引数 `e@rowop: Type`、`e@rowres: (e@rowop) -> Type` として読む。行は
`OpSum(claim@op, e@rowop)` のように `OpNone` の代わりに `e@rowop` で終わる。
`e` の操作は `f` の中では行えず、転送するか、`e` を行に持つ関数を呼ぶことでしか
現れない。`f` はどの行についても成り立つ関数として検査されるので、呼び出しの
側でどの effect を `e` に当てても読みは正しい。

呼び出し `f(…, act)` では `e` に当てる effect を次のように決め、その行の
`e@rowop`・`e@rowres` を先頭の引数として渡す。

- 行に `e` を持つ引数に、行の分かる関数（関数名、引数、ハンドラの継続）を渡して
  いれば、その行から `f` 自身の effect を除いたもの。
- そうでなければ、呼ぶ側の行から `f` 自身の effect を除いたもの。

呼び出しの行（`f` の effect と `e` に当てたもの）は、ほかの小さい行の関数と同じく
`Comp::lift` で呼ぶ側の行へ転送する。行変数は一つの関数に一つまでで、引数の行の
変数は関数自身の行の変数でなければならない。書いた呼び出しは二つの引数を書かない
（抽出も同じ）。

## 関数と式の読み方

`fn f(x: X): A ! {e…}` は `fn f(x: X): Comp(Op, Res, A)` として検査する。
本体の式は次のように読む。

| 書いたもの | 読んだ項 |
|---|---|
| effect のない式 `v` | `Comp::ret(Op, Res, v)` |
| `perform e(a…)` | `Comp::op(Op, Res, i(e@args(a…)))`（`i` は行への注入） |
| `let x := c; rest` | `Comp::bind(Op, Res, c, x => rest)` |
| 引数に effect のある呼び出し `g(c)` | 引数を先に `Comp::bind` してから呼ぶ |
| 小さい行の関数の呼び出し | `Comp::lift`：すべての操作を外へ転送するハンドラ |
| `match`、`if` | 各腕を読む。`match x: T` の結果の型は `Comp(Op, Res, T)` |
| `handle { c } with { … }` | `Comp::handle_in`：`c` を処理する effect を足した行で読み、腕は `e@arm`、処理しない effect は `Comp::forward` で外へ |
| `var x: S := v; rest` | `x` の読み書きを `rest` だけの二つの effect にし、値を引き回すハンドラで処理する |

effect のない関数・定理・定義の中の `handle` で、effect が残らないものは、
その計算の値（`Comp::value`）として読む。関数の本体に `handle` があれば、
本体全体を effect のない行の計算として読む。

ハンドラの腕で外の `var` を書き換えると、その書き換えは外の `var` のハンドラへ
転送され、行った順に値が引き回される。

型を推論できない所では、読んだ項に `the(Comp(Op, Res, T), …)` で値の型を書く。
値の型は、書いた型注釈、関数の結果の型、変数・操作・関数の結果の型から決まる
ものだけを使う。決まらないときは `let x: T := …` と書く。

## 読まないもの

次のものを含む関数は skip される（理由を出す）。実行には影響しない。

- `Div` を持つ関数（一般の再帰。木が有限にならない）。
- カーネルの型でない型を使う effect や本体。
- 閉包が捕まえる `var`、ガードやパターンのあるハンドラの腕、`budget`。
- 型の総称を持つ effect。
- 自身の行にない行変数を引数の行に持つ関数、行変数が二つ以上ある関数。

読んだ関数がカーネルで検査に通らないときも skip になる。

## パッケージ（tote）での扱い

パッケージでは、読める effect（型の総称がなく、型がカーネルの型だけのもの）だけを
行い・処理する関数をカーネルにも渡し、ほかの関数と同じく抽出する。抽出は
effect の宣言、`! {…}` の行、`perform`、`handle` を、型を写して書き出す。
読めない effect を使う関数、`Div` や `budget` を持つ関数、ガードのあるハンドラの腕を
持つ関数は、書いたとおりに実行する。カーネルにも渡した関数の読みが skip されるか
検査に落ちたときも、書いたとおりに実行する。

## 信頼

読んだ項はカーネルと独立カーネルが検査するので、証明の健全性は読み方に
依らない。読み方に依るのは「定理が実行についての主張になっていること」で、
これは読み方が Nib の意味論（`semantics.md`「Effects (deep, multi-shot handlers)」）と
一致することに依存する。

## Lean での裏付け

`lean/Proto/Handlers.lean` の `adequate` は、bind とハンドラのフレームを持つ抽象機械で、`perform` が最も近いハンドラまでの継続を捕まえる（何度でも再開できる）とき、値まで走るプログラムの木が fold で `pure v` になることを示す。操作・値・ハンドラの腕は抽象的に扱い、`var`、行、エラボレータそのものはモデルに含まない。

## 未決定

- `Div` を持つ関数を、fuel 付きの木として読むこと。
- 型の総称を持つ effect。
- 行変数が二つ以上ある関数。
