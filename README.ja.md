# Tauto

*A minimal language for AI to build and prove correct software.*

[English](README.md)

Tauto は、AI が書いて人間が検証するプログラムと証明のための、小さな形式言語です。
証明を項として書く依存型の純粋な核、深い multi-shot の algebraic effect handler、
名前で区別される効果、所有権と借用、共有のステップ予算のもとで再開できる実行を持ちます。
Nib は、Tauto から依存型と証明を除いた言語です。

## この先行公開に含まれるもの

これは一部だけの早期公開です。実装（Rust で書かれています）はまだ公開していません。
ここにあるのは、プロジェクトの仕様の側です。

| パス | 内容 |
| --- | --- |
| `lean/` | Lean 4 による形式化：参照意味論と、それについての証明 |
| `std/` | Tauto で書き、Tauto で証明した標準ライブラリ |
| `examples/` | Tauto のプログラムと証明 |
| `crates/tauto-test-suite/cases/` | 実装が何を答えるべきかを定めるケースファイル |
| `Tauto.eure` | プロジェクトのマニフェスト（まだどのツールも読みません） |

## 言語の雰囲気

効果とハンドラ（`examples/handlers.taut`）：`ask` は継続を何度でも（`ω`）再開でき、
使い切った `budget` にはステップを足して再開できます。

```
effect ask: (n: i64) -> i64 resume ω

let c = handle { perform ask(5) + 1 } with {
  ask(n), k => k(n) + k(n + 1)
  return v => v
}
let d = handle { budget(steps: 3) { 7 } } with {
  exceeded(info), k => info.more(100)
}
```

証明は項で書きます。帰納型の値に対する `match` は生成された eliminator に展開され、
マッチした値のフィールドに対する呼び出しが帰納法の仮定になります（`std/Base.taut`）。

```
theorem nat_eq_sound(a: Nat, b: Nat, e: Eq(Yn, nat_eq(a, b), yes)): Eq(Nat, a, b) {
  match a -> Eq(Nat, a, b) {
    zero => match b -> Eq(Nat, zero, b) {
      zero => refl()
      succ(b2) => False_elim(yes_ne_no(Eq_sym(e)))
    }
    succ(a2) => match b -> Eq(Nat, succ(a2), b) {
      zero => False_elim(yes_ne_no(Eq_sym(e)))
      succ(b2) => Eq_congr(succ, nat_eq_sound(a2, b2, e))
    }
  }
}
```

証明は、ゴールを書いたステップ `by t!(arg) -> G0 { Δ ⊢ G => p … }` でも書けます。
タクティク `t` は信用されないマクロです。`G0` はステップの前のゴールで、各腕には
タクティクが残すゴールを書きます。書いたゴールとタクティクが作った項は、すべて
カーネルが検査します（`examples/nat/Mul.taut`、記法は `nat!`）。

```
theorem mul_comm(n: Nat, m: Nat): nat!(`$n * $m = $m * $n`) {
  match n -> nat!(`$n * $m = $m * $n`) {
    zero => Eq_sym(mul_zero_r(m))
    succ(k) => by rewrite!(mul_succ_r(m, k)) -> nat!(`$m + $k * $m = $m * ${succ(k)}`) {
      ⊢ nat!(`$m + $k * $m = $m + $m * $k`) => by rewrite!(mul_comm(k, m)) {
        ⊢ nat!(`$m + $m * $k = $m + $m * $k`) => refl()
      }
    }
  }
}
```

標準ライブラリのタクティクは二つです（`std/Tactic.taut`）。`rewrite!(e)` は等式で
書き換えます。`nat_norm!(())` は自然数の半環の等式を、Tauto で健全性を証明した
正規化で証明します。

設計の原則を短くまとめると：

- **健全性は書き味に優先する。** カーネルが受理した宣言は、独立したもう一つの
  カーネルが検査し直します。新しい構文は、カーネルが既に受け取る項に展開され、
  カーネルに規則を足しません。
- **短さより明示性。** 暗黙引数は、第一階のマッチングで決まるものだけです。
  モチーフの推論も、推論させる `_` の穴も、ゴールを書かないタクティクもありません。
  名前付きの穴 `?h` は書きかけの証明の印で、穴を含む宣言は未完成として報告され、
  受理されません。`sorry` はありません。
- **一つのことに書き方は一つ。**

## 例

- `examples/proofs.taut`：小さな証明、公理とそれに依存する定理、偽の等式の否定。
- `examples/handlers.taut`、`examples/effects.taut`：効果、ハンドラ、`budget`。
- `examples/ownership.taut`：所有権、借用、引数のビューを返す関数。
- `examples/nat/`：自然数についての証明（交換法則、分配法則、順序、整除性など）。
  `nat!` 構文マクロで書いています。
- `examples/lambda/`：単純型付きラムダ計算の型安全性と強正規化を、公理なしで証明。
  記法は `lc!` マクロで書いています。
- 実行もできる、検証済みのプログラム（それぞれ `NOTES.md` つき）：
  - `examples/sort/`：任意の順序型の挿入ソート。
  - `examples/bst/`：二分探索木。
  - `examples/compiler/`：算術式からスタックマシンへのコンパイラ。
  - `examples/regex/`：微分による、言語を判定するマッチャ。
  - `examples/wf/`：整礎再帰による関数。
- `examples/rust/`：生成したバインディングを通じて Rust のクレートを呼ぶ Tauto のプログラムと、
  スレッド上のタスク。

## Lean による形式化

`lean/Proto` は Lean 以外に依存せず、`sorry` を使いません。

| モジュール | 証明していること |
| --- | --- |
| `Proto/Kernel/` | 依存型カーネルのモデル：subject reduction、合流性、述語的な核の強正規化と無矛盾性、双方向型検査器の健全性（強正規化のもとでの完全性） |
| `Proto/Nib/` | Nib の核：深い multi-shot ハンドラを含む型付けと small-step 意味論、preservation と progress、`Div` を含まない行のプログラムの停止性、所有権（使用の検査、借用、貸している間は場所がムーブされないこと、ビューを返す関数） |
| `Proto/Macro/` | マクロ：スコープ集合による衛生性、燃料つきの展開、型付きマクロの受理 |
| `Proto/Core.lean`、`Renaming.lean`、`ListSet.lean`、`Tags.lean`、`Effects.lean`、`Choice.lean`、`Budget.lean`、`Syntax.lean` | preservation と progress を持つ小さな非依存の核、名前の付け替え、リストによる有限集合、集合としてのタグと効果の行、共有ステップ予算のモデル |

### ビルド

Lean は **4.34.1** に固定しています（`lean/lean-toolchain`）。公式のリリースアーカイブ
`https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-<platform>.zip`
を取得し、使う前に SHA-256 を確かめてください。

| `<platform>` | SHA-256 |
| --- | --- |
| `linux` | `3013aba02bb8bf31b1cf8c9d956d60fb95bb1c10920dfe91abcaa59cb461ddac` |
| `linux_aarch64` | `b4bcf1d79f1b5859c04625058d3707701d87a65815f7f0686a1f14df821954c5` |
| `darwin` | `60b45c76003a4561fb66d7ec2003569006d255d2860179445e56d3e2a029090e` |
| `darwin_aarch64` | `9019fcd34e93fddf0ecf9d40d28f05a86ba563ac3b701a9c5116ce1c96379360` |

ハッシュが一致しないときは、そこで止めてください。展開したディレクトリを `LEAN_DIR` として：

```bash
cd lean
ELAN='' LAKE_OVERRIDE_LEAN=false "$LEAN_DIR/bin/lake" --keep-toolchain --no-cache build
```

## サプライチェーン

- `.cargo/config.toml` は、公開から 14 日経っていないクレートのバージョンを拒否します
  （`rust-toolchain.toml` で固定した nightly の Cargo が強制します）。
- `.gitignore` は許可リストです。許可したもの以外はすべて無視します。

## ライセンス

[Apache License, Version 2.0](LICENSE-APACHE) と [MIT license](LICENSE-MIT) の
どちらかを選んで利用できます。

明示的に別段の定めをしない限り、このプロジェクトに含めるために意図して提出された
貢献は、Apache-2.0 ライセンスの定義に従い、追加の条件なしに上記の二つのライセンスで
提供されるものとします。
