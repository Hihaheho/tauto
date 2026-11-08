# tauto のマクロ：証明のステップ（tactic）

実装は `crates/tauto-macro/src/macros/expand/step.rs`、`std/Rewrite.taut`、`std/Tactic.taut`、試験は `cases/check/steps.eure`。

マクロの設計（[`macro.md`](macro.md)）の上に、証明を
**元のゴールと次のゴールを明示したステップ** で書く仕組み。tactic は信用されないメタプログラムで、
作った項は書かれたゴールと一緒にカーネルと独立カーネルが検査する。**カーネルに規則を足さない。**

---

## 要約

1. ステップは項が書ける場所に書く：`by t!(arg): G0 { Δ ⊢ G from p … }`。`G0` が元のゴール、各腕が
   tactic の残す次のゴール `G`（増えた文脈 `Δ` つき）とその証明 `p`。次のゴールがなければ `{}`。
2. tactic は **入力の型が `ProofStep` の関数** を `macro` で登録したもの。tactic のための宣言や言語はない
   （`macro.md`「`macro` 宣言（登録）と呼び出し `NAME!(…)`」：マクロの種類は関数の入力の型で決まる）。tactic は穴 `?arm1 … ?armN` を一つずつ含む
   `SynExpr` を返す。
3. 展開は `the(G0, S[?armK := the(Gk, pk)])`。書いたゴールはどれも `the` の注釈としてカーネルが検査する。
   tactic が何を作っても、受理するかはカーネルが決める。
4. 書いたゴールと tactic の結果は **変換で** 比べる（型注釈つきの `let` と同じ）。違えば、tactic が残した
   ゴールをそのまま貼れる形で示す。
5. std の tactic は `rewrite!`（`std/Rewrite.taut`）、`nat_norm!` と `nat_le!`（`std/Tactic.taut`。このファイルは `Rewrite.taut` を読み込む）、`int_norm!`（`std/IntNorm.taut`）。`std/` と `meta/` のステップは std の tactic だけを
   呼ぶ（lint の規則 `step-tactic`）。
6. マクロの出力にもステップを書ける（`ExStep`）。展開器は書かれたステップと同じ手順で展開し、検査する
   （「マクロの出力の中のステップ」）。

## 書き方

`match` の腕の目標と `calc!` の書き方は [`syntax.md`](syntax.md)「パターンと `match`」・「証明の構文」。

```
by TACTIC!(引数): 元のゴール {
  x: A, h: P ⊢ 次のゴール1 from 証明1
  ⊢ 次のゴール2 from 証明2
}
```

- `by` は文脈キーワードで、後ろに `名前!(` が続くときだけキーワードになる。
- 引数は一つの式。引数のない tactic は `t!(())` と書く。引数は検査せずに渡し、必要なら tactic が
  `elab_check` で検査する。
- 腕は `Δ ⊢ G from p`。`Δ` は `name: T` をカンマで並べたもので、空なら `⊢ G from p`。`⊢` は省略しない。
- 腕の順は tactic が決める。ラベルは書かない（文脈とゴールが書かれているので要らない）。
- `: 元のゴール` は必ず書く（書かなければ `step.before`）。ただし **ステップがステップの腕の証明そのもののとき** は、その腕のゴールが
  元のゴールなので書かない。書くと同じ `step.before` で拒否する。書いた元のゴールが場所のゴールと違うときは `step.before_mismatch`（「展開と検査（`step.rs`）」の 2）。どのゴールもファイルにちょうど一度書かれる。
- 証明は任意の項で、穴 `?h`、別のステップ、型注釈つきの `let` を含んでよい。
- 書けるのはカーネルが検査する宣言（`theorem`、`def`、カーネルの言語の `fn`）の項の位置だけ。
  `mutual` の中と、実行されるコードの中には書けない（`step.fragment`）。

例：`std/Nat.taut` の `Nat::add_comm` の帰納の段を、等式の鎖で書く。

```
Succ(k) => by rewrite!(Nat::add_comm(a, k)): Succ(Nat::add(a, k)) = Nat::add(Succ(k), a) {
  ⊢ Succ(Nat::add(k, a)) = Nat::add(Succ(k), a) from by rewrite!(Nat::add_succ_left(k, a)) {
    ⊢ Succ(Nat::add(k, a)) = Succ(Nat::add(k, a)) from Refl
  }
}
```

元のゴールは `Nat::add(a, Succ(k))` ではなく計算した形 `Succ(Nat::add(a, k))` で書いている。変換で一致すれば
よいので、書き手は読みやすい形を選べる。

## tactic の定義

`std/prelude/Macro.taut` にあるもの：

```
struct ProofStep { before: Judgement, arg: SynExpr, after: List(StepGoal), span: SynSpan }
struct StepGoal { binders: List(Judgement::Binder), ty: Judgement }
// SynExpr の構成子：`?name`
ExHole(Text, SynSpan)
fn syn_hole(k: u64, at: SynSpan): SynExpr   // ?armK
```

- `before` は元のゴール（文脈は場所の変数）、`after` は書かれた腕（各腕の変数は文脈の後ろに並ぶ原子）。
- tactic は `after` の変数を `BAtom` で束縛に使え、それが書き手の名前になる（`cases/check/steps.eure` の試験用の `intro!`）。
- `after` が `Nil` なのは、腕のないステップのとき（`tauto expand --by` の提案、「道具」）。tactic は既定の
  振る舞い（`rewrite!` なら全ての出現の書き換え）で項を返す。
- 構文の比較・置換・抽象の部品（`syn_same`、`syn_replace`、`syn_abstract`、`syn_diff`、`syn_app_parts`）も
  `Macro.taut` にある。利用者の tactic も同じ部品で書く。
- 入力の型が `ProofStep` のマクロは `by NAME!(…)` でしか呼べず、他のマクロは `by` で呼べない
  （`macro.argument` / `step.tactic`）。
- `by` の後ろに書けるのは tactic の呼び出しだけ。引数のない tactic は `by nat_norm!()` と書く（引数は単位 `()`）。
- 合成（順に試す、繰り返す）は普通の Nib の関数で書く。tactic 専用の言語は作らない。

## 展開と検査（`step.rs`）

宣言ごとに、外側のステップから一つずつ処理する。宣言 `d` の最初のステップについて：

1. ステップの場所を穴にした宣言を検査し、場所の文脈とゴール（`tauto goals` と同じ `HoleGoal`）を得る。
   前のステップの 4 の検査で、このステップが残りの穴として現れていれば、その穴を使い、この検査は行わない
   （前のステップの腕の証明の中にあるステップは、穴として現れないので検査する）。したがって、ステップが
   k 個の宣言の検査は k + 1 回ほどになる。
2. 書いた `G0` と場所のゴールを変換で比べる（`step.before_mismatch`）。
3. tactic を呼ぶ。穴がちょうど `?arm1 … ?armN`（腕の数）でなければ `step.holes`。
4. `the(G0, S)` を場所に置いて検査し、各穴のゴールと文脈を得る。穴で増えた変数の名前は腕の `Δ` の名前と
   同じで、型は変換で等しくなければならない（`step.context_mismatch`）。ゴールは変換で比べる
   （`step.goal_mismatch`、tactic の残したゴールを示す）。項が型に合わなければ `step.output_ill_typed`。
5. `the(G0, S[?armK := the(Gk, pk)])` を場所に置く。腕の証明がステップなら `the` で包まない（そのステップが
   自分の元のゴールを `the` で書く）。

比べるのは、定理 `step'check(Γ…, step'v: 見つけた型): 書いた型 { step'v }` をカーネルに渡すこと（`Γ…` は場所の文脈。
名前の `'` は識別子に書けない文字なので、`step'check` と `step'v` は書かれた名前とぶつからない）。カーネルの検査のほかに判断はない。
誤りのあとは、その宣言のステップをすべて、先頭から順に穴 `?step`、`?step'2`、`?step'3` … にして、残りの診断が重ならないようにする。

| 保証 | 誰が確かめるか |
|---|---|
| 定理が正しい | 二つのカーネル。展開後の項は手で書いた項と区別がない |
| 書いた元のゴールが本当のゴール | 2 の比較と `the(G0, …)` |
| 書いた次のゴールが本当のゴール | 4 の比較と `the(Gk, pk)` |
| 書いた文脈が本当の文脈 | 4 の比較（誤っても健全性は崩れない） |
| tactic が正しい | 確かめない。要らない |

展開後の項は `tauto macro expand` で見え、記録の種類は `step`。

## マクロの出力の中のステップ

マクロの出力の `SynExpr` は、構成子 `ExStep(tactic, arg, before, arms, span)` でステップを含んでよい。
腕は `struct SynStepArm { binders: List(SynBinder), goal: SynExpr, body: SynExpr }`（`binders` は型つきの `BName`）。
`quote { by t!(e): G0 { … } }` も `ExStep` を作る。

- 展開器は、出力を差し込んだ宣言のステップを、書かれたステップと同じ手順（「展開と検査（`step.rs`）」）で
  展開する。tactic は書かれたステップと同じ入力（場所のゴールと文脈、書かれた元のゴールと腕）で走り、
  作られる項も書かれたステップと同じになる。カーネルに規則を足さない。
- 型付きマクロの引数の中のステップは、型付きマクロを展開する前に、引数をその場所に置いた宣言で展開する。
  ステップのゴールは引数の中の場所の型で、展開した引数がマクロの入力になる。
- tactic は登録した名前で探す。ステップを含む出力を作ったマクロを呼ぶファイルが、tactic を読み込んでいなければ
  ならない（`macro.unknown`）。tactic の import は使われたものとして数える。tactic が作る項の名前は、
  書かれたステップと同じく tactic を定義したファイルで解決するので、呼ぶ側は tactic の使う宣言を読み込まない。
- 元のゴールは書かれたステップと同じく省けない（`step.before`）。省けるのは、ステップの腕の証明そのものであるステップだけ。
- tactic の出力はステップを含まない（`step.nested`）。tactic は腕ごとの穴を持つ項を作り、別の tactic を
  書かれていないゴールで走らせない。マクロの出力のステップの腕の証明は、ステップを含んでよい。
- lint の `step-tactic` は、構文のリテラルが述べるステップ（`proof!` の本文の `by t!`）にも同じ規則を当てる。
- 位置のマクロの出力のステップも同じ手順で展開する。出力を差し込んだ宣言に位置のマクロの呼び出しが残っていれば、
  その場所は穴のまま、ステップを先に展開する（穴は自分の場所のゴールで次の回に展開される）。残っていなければ、
  ステップを展開してからカーネルが宣言を検査する。
- tactic の呼び出し `t!(e)` が展開前のマクロの呼び出しの引数の中にあるとき、展開器はそれを展開せずに残す。
  それを読んでステップを作るのはそのマクロである（`proof!` の本文の `$t!(e)`）。どの呼び出しの引数の中でもない
  tactic の呼び出しは、今までどおり `macro.argument` で拒否する。

## 道具

- `tauto goals` / `try` / `fill`：穴の扱いはステップの外と同じ。腕の `?h` のゴールは書かれたゴール。
- `tauto expand FILE --hole h --by 'rewrite!(e)'`：穴をステップにする。まず腕なしで書いて tactic を走らせ、
  展開器が `step.arms` で腕を述べ、それを `?h_1 …` つきで書き出す（`assist::expand_step`）。穴がステップの
  腕の証明そのものなら `: G0` を省く。
- LSP：腕の `Δ ⊢ G` が tactic の残したものと違う（`step.goal_mismatch`、`step.context_mismatch`）とき、診断は
  腕の見出し（`from` の前）を tactic の残したものに書き直す編集を `fix` に持つ。`tauto check --json` の
  エラーの `fix`（`title`、範囲、`text`）と、LSP の `textDocument/codeAction`（`quickfix`）がそれを返す。腕の変数の名前は、
  tactic が足した数と同じなら書かれたままにする。
- `tauto lint`：`step-tactic`（`std/` と `meta/` は `rewrite!`、`nat_norm!`、`nat_le!`、`int_norm!` だけ）。
- `tauto macro expand --write`：ステップを項として書き戻す。

## std の tactic

基準は「項では短く言えないことをする tactic だけを置く」。項の構文と一対一の tactic（`intro!`、`exact!`、
`apply!`、`cases!`、`induction!`）は同じことの二つ目の書き方になるので置かない。補題の全体から探す tactic は
言語としては書けるが、補題を足すと他の証明の展開が変わるので std には置かない。

**`rewrite!(e)`**、`e: Eq(A, l, r)`：元のゴールが `M(l)`、腕のゴールが `M(r)`。項は
`Eq::subst(z => M(z), Eq::sym(e), ?arm1)`。モチーフは推論しない：書かれた二つのゴールの差から一つに決まり、
読み手はその二つを見比べて確かめられる。

- `l` と `r` は `e` の型から読む（`elab_check`）。読めないとき（帰納法の仮定になる再帰呼び出し）や、
  型の書き方が違うときは、二つのゴールの違う最小の部分から読む。
- どの出現を書き換えるかは腕のゴールが決める。腕がなければ全ての出現。
- 二つのゴールが等式以外でも違えば拒否する（一つの等式に一つのステップ）。

**`nat_norm!(())`**：ゴール `Eq(Nat, l, r)` の両辺を `Nat::add`、`Nat::mul`、`Succ`、`Zero`、数字で組んだ式として
読み、それ以外の部分式を変数（`syn_same` で同じものを同じ変数）とする反映の tactic。項は
`Nat::norm_eq(vars, l', r', Refl)`。`l'`、`r'` は `NatExpr`（`NeConst`、`NeVar`、`NeAdd`、`NeMul`）、`vars` は変数の
値の並びで、`std/NatNorm.taut` が持つ。

- 信頼するのは `Nat::norm_eq` だけ。正規化 `ne_norm`（変数の添字の積を整列した単項式の和を、整列した和にする）の
  健全性 `ne_norm_sound` が tauto の定理として示してあり、tactic の読み取りが誤っても、できた項が
  カーネルに通らないだけ。両辺の正規形が違うときも `Refl` が通らず、`step.output_ill_typed` が二つの
  正規形を示す。
- 腕は残さない（書くと拒否）。ゴールを書き換えるのは `rewrite!` の腕の証明の位置で `by nat_norm!() {}` と書く。
- 数字 `n` は空の積 `n` 個の和になるので、数字の大きな式には向かない（係数は持たない）。時間のほとんどは、展開した
  式を検査するカーネルの変換にかかる。

**`nat_le!(())`**：ゴール `l <= r = true` または `l < r = true`（`Nat::le`、`Nat::lt` も同じ）の両辺を `nat_norm!` と同じに読む。
`l < r` は `Succ(l) <= r` として読む。項は `Nat::norm_le(vars, l', r', Refl)`。`Refl` がカーネルに通るのは、
`Np::le_chk(Ne::norm(l'), Ne::norm(r')) = true` が計算で出るときだけ。

- `Np::le_chk(p, q)` は、`p` の正規形の各項に、`q` に同じ単項式で係数が小さくない項があるかを、
  整列した二つの並びを一度なぞって確かめる。これが `true` なら変数の値によらず `p` の値は `q` の値以下である
  （`Np::le_chk_sound`、`Nat::norm_le`）。信頼するのは `Nat::norm_le` だけで、tactic の読み取りが誤っても
  できた項がカーネルに通らないだけ。
- 完全ではない。係数を比べるだけなので、仮定を使う不等式、引き算を含む不等式、`a * b <= c * d` のような
  単項式どうしの大小は証明しない。通らないときは `step.output_ill_typed` が二つの正規形から計算した
  `false` を示す。
- 腕は残さない（書くと拒否）。目標は `<=`、`<`、`Nat::le`、`Nat::lt` の形で書く（`Eq(Bool, …)` の形は読まない）。

**`int_norm!(())`**：ゴール `Eq(Int, l, r)` の両辺を `Int::add`、`Int::sub`、`Int::mul`、`Int::neg`、数字の `int_of_nat` で組んだ式として
読み、それ以外の部分式を変数とする反映の tactic。`nat_norm!` と同じ形で、信頼するのは `Int::norm_eq` だけ。
腕は残さない（書くと拒否）。

## 設計原則との関係

- **Minimalism**：tactic のための構成は `by`、`ProofStep`、`ExHole`、`ExStep` だけ。マクロの出力のステップは書かれたステップと同じ手順で展開し、別の仕組みを持たない。tactic は入力の型で決まる四つ目の種類（入力の型が `ProofStep` の関数）で、ほかに宣言や構文の種類はない。
- **Soundness**：カーネルは変えない。tactic と精密化の誤りは二つのカーネルが拒否できる。
- **AI-Native**：証明の状態が道具を動かさずにソースから読める。`expand` がゴールを書き、食い違いは貼れる形で返る。
- **Self-Verification**：tactic は Nib で書かれ、展開器は self-host の構文（`totes/surface`、`totes/macros`）にもある。
- Lean の形式化に tactic のための部分はない。カーネルに規則を足さないので、tactic について示す性質がない。
