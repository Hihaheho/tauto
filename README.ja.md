<picture>
  <source media="(prefers-color-scheme: dark)" srcset="https://raw.githubusercontent.com/Hihaheho/tauto/main/assets/logo-dark.svg">
  <source media="(prefers-color-scheme: light)" srcset="https://raw.githubusercontent.com/Hihaheho/tauto/main/assets/logo.svg">
  <img alt="Tauto" src="https://raw.githubusercontent.com/Hihaheho/tauto/main/assets/logo.svg" height="100px">
</picture>

# Tauto

*A minimal language for AI to build and prove correct software.*

[English](README.md)

Tauto は、AI がプログラムと証明を書き、人間がその命題を検証するための、小さな形式言語です。
証明を項として書く依存型の純粋な核、深い multi-shot の algebraic effect handler、
名前で区別される効果、所有権と借用、共有のステップ予算のもとで再開できる実行を持ちます。
Nib は、Tauto から依存型と証明を除いた言語です。

ソースファイルの拡張子は `.taut` と `.tauto` を受け付けます。このリポジトリでは `.taut` を使います。

## この先行公開に含まれるもの

これは実験段階のソース公開です。Rust の実装、Tauto で書いた道具、形式化を含みます。
言語と CLI は変更される可能性があり、安定版ではありません。

| パス | 内容 |
| --- | --- |
| `crates/` | Rust の実装：構文解析、精密化、カーネル、評価器、バックエンド、CLI、エディタ支援 |
| `totes/` | Tauto で書いた道具とライブラリ：独立カーネル、Nib 検査器、構文解析、フォーマッタ、コード生成器など |
| `std/` | 標準ライブラリとその証明。`std/prelude/` は import なしで使える宣言で、カーネルも読みます（共有する `enum`・`struct` は帰納型になり、`std/prelude/Ord.taut` は両方のカーネルがすべて検査します。組み込みの型のインスタンスは信頼します） |
| `meta/` | 小さな核とカーネルのモデル、およびその性質の証明 |
| `lean/` | Lean 4 による形式化：参照意味論と証明 |
| `examples/` | プログラムと証明、Rust・JavaScript との連携例 |
| `cases/` | テストの入力と期待する結果 |
| `tools/` | パーサー生成と、Tauto の道具を Rust 実装と比較するテスト |
| `scripts/` | テスト、表の生成、Lean のセットアップ |
| `docs/design/` | 設計と実装の文書 |
| `Tauto.eure` | ソースのルートと依存を宣言するプロジェクトのマニフェスト |

## 対象

検査したプログラムは、Tauto で書いた機械（`totes/vm`）か評価器（`--backend eval`）で走らせるか、次へコンパイルします。

- **Rust**（`tauto build`、`tauto run --backend rust`）：`tauto-rt` とリンクする Rust のクレート。`unsafe` を含みません。
- **JavaScript**（`crates/tauto-jsgen`、`tauto build --emit javascript`、`tauto run --backend javascript`）：単独の ES モジュール。既定の対象は Node で、ブラウザでは ES モジュールとして読み込みます（[`docs/design/javascript-backend.md`](docs/design/javascript-backend.md)、ホストの束縛の型は [`docs/design/javascript-host-types.md`](docs/design/javascript-host-types.md)）。
- **WebAssembly**：Rust バックエンドを wasm32 向けに作ります（`tauto build --backend rust --target wasm32-wasip1` または `--target wasm32-unknown-unknown`）。wasm32 にはスレッド・リアクター・`net` がありません（[`docs/design/rust-backend.md`](docs/design/rust-backend.md)）。

## 所有権とメモリ

値は `copy`・`shared`・`affine`・`linear` のいずれかで、検査器（`crates/tauto-nibcheck`）がムーブと借用、貸している間に場所がムーブされないことを検査します。Rust への出力は GC を持たず、値は所有されて捨てられ、`shared` な値は参照カウントで管理します（唯一所有なら in-place で更新）。署名と局所変数に `shared` な型が現れない関数は参照カウントを走らせません。JavaScript への出力はエンジンの GC に任せます。詳しくは [`docs/design/ownership.md`](docs/design/ownership.md)。

## 必要なもの

- Git と、rustup で入れた Rust。`rust-toolchain.toml` は日付で固定した nightly を指定し、rustup が初回に入れます。nightly が要るのは、`.cargo/config.toml` が crate の公開からの期間を検査し、`-Znext-solver=coherence` を渡すためです。
- 初回のビルドではネットワーク：Cargo はロック済みの依存を取得し、[Eure](https://github.com/Hihaheho/eure) は Git のコミットを固定しています。
- 任意：JavaScript バックエンドには Node、Wasm には `rustup target add wasm32-wasip1`（または `wasm32-unknown-unknown`）、形式化には Lean 4.34.1（下記）。

## ビルドして試す

```bash
git clone https://github.com/Hihaheho/tauto.git
cd tauto
cargo install --locked --path crates/tauto-cli
tauto run examples/handlers.taut
tauto check examples/proofs.taut
```

例とライブラリのソースを使うため、チェックアウトを残してください。
大きめのプログラムと連携例は [examples](examples/README.md) にあります。

開発時は、リポジトリのルートで検証を実行します。

```bash
bash scripts/test.sh full
```

一部だけを調べる場合は `bash scripts/test.sh focused -p tauto-kernel` を使えます。
これは全体の検証を代替しません。ツールチェインのキャッシュは
[`docs/design/build-cache.md`](docs/design/build-cache.md) に、ケースの形式は
[`docs/design/test-suite.md`](docs/design/test-suite.md) にあります。

## 言語の雰囲気

効果とハンドラ（`examples/handlers.taut`）：`ask` は継続を何度でも（`ω`）再開でき、
使い切った `budget` にはステップを足して再開できます。

```
pub(open) effect ask(n: i64): i64 resume ω

let c := handle { perform ask(5) + 1 } with {
  ask(n), k => k(n) + k(n + 1)
  return v => v
}
let d := handle { budget(steps: 3) { 7 } } with {
  exceeded(info), k => info.more(100)
}
```

証明は項で書きます。帰納型の値に対する `match` は生成された eliminator に展開され、
マッチした値のフィールドに対する呼び出しが帰納法の仮定になります（`std/Base.taut`）。
再帰呼び出しは、マッチした値の型に現れる引数を除いて、どの引数を変えてもかまいません。
腕の中でフィールドをさらに `match` した先の値（`Cons(a, Cons(b, rest)) => f(rest)` の `rest`）に対しても再帰できます。
マッチした引数とは別の引数で再帰するときは、`decreasing_by y` でその引数を書きます（`fn` でも `theorem` でも）。
`(match x: (H) -> G { … })(h)` のように、仮定を一般化した `match` の中でも再帰できます。
`mutual` ブロックの中で、同じ型を `match` する関数を二つ以上定義できます。

`crates/tauto-kernel/src/prelude_deq.taut` の `module Nat` から抜粋します。

```
theorem eq_sound(a: Nat, b: Nat, e: Nat::eq(a, b) = true): (a = b) {
  match a: (a = b) {
    Zero => match b: (Zero = b) {
      Zero => Refl
      Succ(b2) => False::elim(true_ne_false(Eq::sym(e)))
    }
    Succ(a2) => match b: (Succ(a2) = b) {
      Zero => False::elim(true_ne_false(Eq::sym(e)))
      Succ(b2) => Eq::congr(Succ, eq_sound(a2, b2, e))
    }
  }
}
```

証明は、ゴールを書いたステップ `by t!(arg): G0 { Δ ⊢ G from p … }` でも書けます。
タクティク `t` は信用されないマクロです。`G0` はステップの前のゴールで、各腕には
タクティクが残すゴールを書きます。書いたゴールとタクティクが作った項は、すべて
カーネルが検査します（`examples/nat/Mul.taut`、記法は `nat!`）。

```
pub theorem mul_comm(n: Nat, m: Nat): nat!(`$n * $m = $m * $n`) {
  match m: nat!(`$n * $m = $m * $n`) {
    Zero => Eq::sym(mul_zero_l(n))
    Succ(k) => by rewrite!(mul_succ_l(k, n)): nat!(`$n * $k + $n = ${Succ(k)} * $n`) {
      ⊢ nat!(`$n * $k + $n = $n + $k * $n`) from by rewrite!(mul_comm(n, k)) {
        ⊢ nat!(`$k * $n + $n = $n + $k * $n`) from add_comm(k * n, n)
      }
    }
  }
}
```

等式の連鎖は `calc a { = b from p … }` で書けます（[`docs/design/syntax.md`](docs/design/syntax.md)）。

標準ライブラリのタクティクは二つです（`std/Tactic.taut`）。`rewrite!(e)` は等式で
書き換えます。`nat_norm!()` は自然数の半環の等式を、Tauto で健全性を証明した
正規化で証明します。

## 設計の指針

Tauto は、AI が書き、人間が確かめるための言語です。以下の規則はすべてそのためにあります。
受理されるものは機械が検査し、書かれたものはその場で読めなければなりません。

**言語**

- **少数の直交する概念。** 証明のための完全な依存型と、実用的な計算のための
  algebraic effects に、資源のための所有権を加え、少ない概念で多くを言えるようにします。
  言語の実装と証明は言語自身で書き、自己ホスティングとその検証を目指します。
- **健全性は書き味に優先する。** カーネルが受理した宣言は、名前を使わない独立した
  もう一つのカーネルが検査し直します。精密化の誤りはカーネルが拒否できなければならず、
  カーネルの誤りは何より先に直します。
- **糖衣はカーネルに規則を足さない。** 新しい構文は、カーネルが既に受け取る項
  （eliminator の適用、λ、Π）に展開されます。
- **短さより明示性。** 読み手がその場で確かめられないものは推論に任せません。
  入れ子パターン、型注釈つきの `let`、`match` での添字の単一化、フォーマッタは入れ、
  モチーフを推論する書き換えや、推論させる `_` の穴は入れません。暗黙引数は、
  第一階のマッチングで決まるものだけです。クラスの instance は型の頭の構成子から
  見つけ、一つの型に一つだけなので、探索はありません。
- **名前付きの穴 `?h` は書きかけの証明の印。** 穴を含む宣言は未完成として報告され、
  受理されません。`sorry` はありません。
- **一つのことに書き方は一つ。** 同じ意味の構文を二つ用意しません。
- **既定で安全に。** 依存と実行は既定で疑います。公開から 14 日経っていない crate は
  取り込まず、副作用は effect で明示した範囲にとどめます。

**証明**

- 証明は項か、前のゴールと後のゴールを書いたステップ `by t!(arg): G0 { Δ ⊢ G from p }`
  で書きます。タクティクは信用されないマクロで、書かれたゴールと作られた項は
  カーネルが検査します。ゴールを書かないタクティクはありません。
- `std/` と `meta/` は公理を使わず（例外は商の公理 `Quot::sound` で、関数外延性を置く
  `std/Quot.taut` だけが使います）、標準のタクティク（`rewrite!`、`nat_norm!`）だけを
  呼び、既定腕 `_ =>` を使わず（言語としては許しますが、`match` がどの構成子を
  覆うかが見えなくなります）、整形済みに保ちます。標準ライブラリに置くタクティクは、
  項では短く言えないことをするものだけです。
- 途中の命題は、型注釈つきの `let` で名前と型を付けます。補助定理に切り出すのは、
  再利用するか、それ自体に意味のある命題のときだけです。
- 仮定は含意 `P -> Q` にせず、後ろの引数 `h: P` に取ります。`match a` は `a` より
  後ろの引数をすべて一般化し、各腕では精密化された型のまま同じ名前で見えます。
- 変数でない式での場合分けは `match e eqn h: G { C => ⊢ G' from p … }` と書きます。
  各腕の目標は `G` の `e` を置き換えたもので、それを書き、`h` は等式 `e = C` です。
  型に `e` が出る仮定も、各腕では `e` を `C` に置き換えた型で同じ名前のまま見えます。
- 反転は添字を単一化する `match` で書きます。等式と射影による反転は、単一化が
  届かないときだけにします。
- 証明の型から第一階で決まる引数はジェネリクスにし、呼び出しでは証明だけを渡します
  （`eq_Kpi(e1, e2)`）。
- 計算で確かめられる事実は、`Refl` の定理として残します。

## 例

- `examples/proofs.taut`：小さな証明、公理とそれに依存する定理、偽の等式の否定。
- `examples/handlers.taut`、`examples/effects.taut`：効果、ハンドラ、`budget`。
- `examples/ownership.taut`：所有権、借用、引数のビューを返す関数。
- `examples/nat/`：自然数についての証明（交換法則、分配法則、順序、整除性など）。
  `nat!` 構文マクロで書いています。
- `examples/lambda/`：単純型付きラムダ計算の型安全性と強正規化を、公理なしで証明。
  記法は `lc!` マクロで書いています。
- 検証済みのプログラム：
  - `examples/sort/`：任意の順序型の挿入ソート。
  - `examples/bst/`：二分探索木。
  - `examples/compiler/`：算術式からスタックマシンへのコンパイラ。
  - `examples/calc/`：文法から証明側の型も作る電卓。読んだ式をスタックマシンで計算すると、その式の値が残ることを証明。
  - `examples/regex/`：微分による、言語を判定するマッチャ。
  - `examples/wf/`：整礎再帰による関数。
- `examples/rust/`：生成したバインディングを通じて Rust のクレートを呼ぶ Tauto のプログラムと、
  スレッド上のタスク。
- `examples/javascript/`：JavaScript バックエンドのプログラム。JavaScript の非同期関数と、Wasm に
  コンパイルした Rust の関数を呼び、効果を起こすコールバックと境界をまたぐ借用を使う。

## Lean による形式化

`lean/Proto` は Lean 以外に依存せず、`sorry` を使いません。

| モジュール | 証明していること |
| --- | --- |
| `Proto/Kernel/` | 依存型カーネルのモデル：subject reduction、合流性、述語的な核の強正規化と無矛盾性、双方向型検査器の健全性（強正規化のもとでの完全性） |
| `Proto/Nib/` | Nib の核：深い multi-shot ハンドラを含む型付けと small-step 意味論、preservation と progress、`Div` を含まない行のプログラムの停止性、所有権（使用の検査、借用、貸している間は場所がムーブされないこと、ビューを返す関数） |
| `Proto/Macro/` | マクロ：スコープ集合による衛生性、燃料つきの展開、型付きマクロの受理 |
| `lean/Proto/Core.lean`、`Renaming.lean`、`ListSet.lean`、`Tags.lean`、`Effects.lean`、`Choice.lean`、`Budget.lean`、`Syntax.lean` | preservation と progress を持つ小さな非依存の核、名前の付け替え、リストによる有限集合、集合としてのタグと効果の行、共有ステップ予算のモデル |

### ビルド

形式化の構成は [`lean/README.md`](lean/README.md)、何を証明しているかは [`docs/design/lean.md`](docs/design/lean.md) を参照してください。

Lean は **4.34.1** に固定しています（`lean/lean-toolchain`）。公式のリリースアーカイブ
`https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-<platform>.zip`
を取得し、使う前に SHA-256 を確かめてください。

| `<platform>` | SHA-256 |
| --- | --- |
| `linux` | `3013aba02bb8bf31b1cf8c9d956d60fb95bb1c10920dfe91abcaa59cb461ddac` |
| `linux_aarch64` | `b4bcf1d79f1b5859c04625058d3707701d87a65815f7f0686a1f14df821954c5` |
| `darwin` | `60b45c76003a4561fb66d7ec2003569006d255d2860179445e56d3e2a029090e` |
| `darwin_aarch64` | `9019fcd34e93fddf0ecf9d40d28f05a86ba563ac3b701a9c5116ce1c96379360` |

ハッシュが一致しないときは、そこで止めてください。`scripts/setup-lean-4.34.1.sh` がこの手順を
行います：使っている環境のアーカイブを取得し、上のハッシュを確かめ、`.tools/lean-4.34.1`（または引数の
絶対パス）に展開します。展開したディレクトリを `LEAN_DIR` として：

```bash
bash scripts/setup-lean-4.34.1.sh "$PWD/.tools/lean-4.34.1"
LEAN_DIR=$PWD/.tools/lean-4.34.1
cd lean
ELAN='' LAKE_OVERRIDE_LEAN=false "$LEAN_DIR/bin/lake" --keep-toolchain --no-cache build
```

## 詳しい資料

次の節は英語版の [README.md](README.md) にだけあります。

- [Targets](README.md#targets)、[Ownership and memory](README.md#ownership-and-memory)、[Repository layout](README.md#repository-layout)、[Development](README.md#development)
- [Using tauto](README.md#using-tauto)（[Type errors](README.md#type-errors)、[Writing a proof a step at a time](README.md#writing-a-proof-a-step-at-a-time)、[Proofs written in tauto](README.md#proofs-written-in-tauto)、[How the kernel checks](README.md#how-the-kernel-checks)、[What the kernel does with inductive types](README.md#what-the-kernel-does-with-inductive-types)、[Well-founded recursion](README.md#well-founded-recursion)、[Universe polymorphism](README.md#universe-polymorphism)）
- [Parser generation](README.md#parser-generation)、[Nib](README.md#nib)、[Syntax and macros](README.md#syntax-and-macros)、[Editor support](README.md#editor-support)
- [Rust backend](README.md#rust-backend)、[JavaScript backend](README.md#javascript-backend)、[Self-hosting](README.md#self-hosting)、[Totes](README.md#totes)

## 制限

- `check` は実行のための本体（ブロック、`var`、`perform`、`handle`）を読み飛ばし、それらは `run` が検査します。
- 暗黙引数は第一階のマッチングだけで、名前付き引数はありません。クラスの instance は型の頭の構成子か `where` の仮定から見つけ、それ以外は探しません。
- 添字の単一化は第一階のフィールドを持つ構成子までです。入れ子の帰納型は、パラメータを持つ型や添字つき・相互の型を通るものを拒否します。
- 宇宙の多相は数値の水準のテンプレートだけで、記号で量化した宇宙はありません。
- 効果の行は値の型なしで検査し、Lean の規則とは繋がっていません。`budget` の中断と multi-shot での予算の共有は評価器のテストだけが保証します。依存型を含む Nib の核の性質は未証明です。
- 穴は `mutual` ブロックの中と型の位置には書けません。マクロの展開のキャッシュはありません。
- パッケージのレジストリはありません。依存はパスか Git のリポジトリで指定します。
- Rust バックエンドは、multi-shot の `handle` の中の `return` と M 層の `budget` に対応していません。
- `tauto bind` は `unsafe fn`、`async fn`、`dyn Trait`、const generics、マクロ、型引数の実体化が設定にないジェネリックな関数などを出さず、報告します。
- Wasm は Rust バックエンド経由だけで、スレッド・リアクター・`net` がなく、panic は abort します。
- 評価器、lint、名前つきの精密化器、完全な Rust 生成器は Nib で書き直していません。

## サプライチェーン

- `.cargo/config.toml` は、公開から 14 日経っていないクレートのバージョンを拒否します
  （`rust-toolchain.toml` で固定した nightly の Cargo が強制します）。
- `.gitignore` は許可リストです。許可したもの以外はすべて無視します。

## 依存とクレジット

- [Eure](https://github.com/Hihaheho/eure)：マニフェストとケースファイルの形式（Git のコミットを固定）。
- [parol](https://github.com/jsinger67/parol)：`tauto.par` からパーサーを生成します（`tools/tauto-parol-gen` だけで動きます）。生成したパーサーは実行時に `scnr2` を使います。
- [Lean 4](https://lean-lang.org/)：`lean/` の形式化。
- `query-flow`、`proc-macro2`、`quote`、`serde_json`、`rustdoc-types`、`tauto-rt` の feature の後ろの `tokio`・`reqwest`・`rustls` など。すべては `Cargo.lock` にあります。
- メッセージは FTL で書きます（`crates/tauto-messages/locales`）。
- `crates/tauto-syntax`、`totes/pargen`、`totes/llkgen`、`totes/llk`、`totes/scan`、`totes/syntax` の文法の記法、LL(k) の表の生成、スキャナーの生成、表の形式、ランタイムの設計は、Jörg Singer による [parol](https://github.com/jsinger67/parol) と [scnr2](https://github.com/jsinger67/scnr2)（MIT OR Apache-2.0）に由来します。
- `totes/unicode` と `totes/pargen` の Unicode の表は、Rust の標準ライブラリと `regex-syntax` クレートを通して、Unicode Character Database（Unicode License v3）に由来します。
- `crates/tauto-rt/src/float_math.rs` は `libm` クレート 0.2.11（MIT OR Apache-2.0）に由来し、元の告知を残しています。`crates/tauto-jsgen/src/float.js` は同じ関数を JavaScript に移したものです。
- 告知とライセンスの全文は [NOTICE](NOTICE) にあります。

## ライセンス

[Apache License, Version 2.0](LICENSE-APACHE) と [MIT license](LICENSE-MIT) の
どちらかを選んで利用できます。

明示的に別段の定めをしない限り、このプロジェクトに含めるために意図して提出された
貢献は、Apache-2.0 ライセンスの定義に従い、追加の条件なしに上記の二つのライセンスで
提供されるものとします。
