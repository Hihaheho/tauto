# Cranelift JIT（`tauto-jit`）：設計

`tauto run`・`tauto test` など「検査したプログラムをすぐ走らせる」場面を速くするため、
`tauto-vm` の中で関数単位に Cranelift で機械語を生成する。配布用のネイティブ
バイナリは Rust バックエンド（`rust-backend.md`）の役目であり、この JIT は扱わない。

## 原則

- **観測できる振る舞いは VM と同じ。** 表示・書き込み・終了コード・実行時エラー、
  ホストの step 上限の数え方まで一致させる。意味の正は `eval.rs`。
- **所有権の判断は `lin.rs` が一手に持つ。** JIT は NIR に書かれた move / copy /
  借用 / drop の位置をそのまま使い、独自に推論しない。
- **`unsafe` は `tauto-jit` の中に閉じる。** 機械語の生成と実行には `unsafe` が
  避けられない。`tauto-rt`・`tauto-vm`・生成された Rust コードの
  `#![forbid(unsafe_code)]` は変えない。JIT は既定で有効とし、無効にするフラグで VM だけの実行に戻せる。Cranelift が対応しない環境では自動的に VM で動かす。
- **カーネルは変えない。** 証明・型の扱いに JIT は関わらない。JIT は信頼する核の
  外にあり、正しさは差分比較で確かめる（「検証」）。

## 下ろす IR

NIR の直接形（`tauto_nir::Package` の各関数）から Cranelift IR を作る。

- 層（`Tier`）・`Repr`・`Storage` が決まっているので、SSA への写像が素直で、
  直接呼び出しとレジスタ割り当ての利点が残る。
- `nir::cps` は全層を一つの方法で扱えるが、呼び出しごとに継続を作るので JIT の
  利点が消える。VM がすでにこの形を実行している。
- VM のバイトコードは型と所有権の情報を失っており、汎用の `Value` を扱うことになる。

## 対象と境界

JIT するのは S 層（効果なし・`direct` だけ）の関数で、固定幅整数・`Bool`・`Unit` だけを
普通の局所変数に持つものに限る。算術・比較・`if`・ブロック・`while`・`return`・
`div`/`mod`、同じ条件を満たす関数の呼び出しを扱う。
A 層・O 層・M 層の関数、およびそれらの `handle` を含む関数は VM のまま動かす。

どの関数を JIT するかは NIR だけで静的に決まり、実行時のプロファイルには依らない
（同じ入力なら同じ結果）。

### Rust 製 VM（`crates/tauto-vm`）

`Program::native`（`tauto_vm::native::Native`）に JIT のコードを持たせる。`Op::Call` で
対象の関数を呼ぶとき、どの `budget` の中でもなければ native コードを走らせ、値を
`tauto_vm::Value` との間で変換する。`budget` の中では step が `budget` に数えられるので、
VM のバイトコードで動かす。

### Tauto 製 VM（`totes/vm`、既定の `tauto run`）

機械（`machine.taut`）には手を入れない。証明（`proof/machine.taut`）が扱う機械のまま
にするためである。代わりにシェル（`main.taut`）が、プログラムを機械に渡す前に
対象の関数の本体を「ホストに `vm_native` を尋ねる」本体に置き換え、元の本体は
関数の列の末尾に移す（`native.taut` の `vm_native_program`）。シェルは `vm_native` に
答えるとき、どの `budget` の中でもなければ extern（`totes/vm/bridge`）越しに native
コードを走らせ、そうでなければ元の本体へ進む。extern は数と `Bool` だけをやりとりする。

`tauto` コマンドは機械を動かす前に NIR のプログラムを bridge に渡し、bridge は機械の
スレッドで最初に尋ねられたときに JIT する。単独で起動した機械には native コードがない。

### 無効にする

環境変数 `TAUTO_JIT=0` で JIT を使わず VM だけで動かす。
Cranelift が対応しない環境では JIT のコードが作られず、VM だけで動く。

### 深い再帰

native コードは `MAX_DEPTH`（10,000）段より深く呼ぶと諦め、`DEEP_STACK`（4 GiB）の
スタックを持つスレッドで最初からやり直す。それでも足りなければ VM のバイトコードで
動かす。native コードには効果がないので、やり直しても結果と step の数は変わらない。

## 値の表現とメモリ

トレース GC は持たない。種がそのまま表現を決める（`ownership.md`）。

| 種 | 表現 |
| --- | --- |
| copy | 即値（固定幅整数・`Bool` など） |
| shared | ヒープ上の参照カウント付きの箱 |
| affine / linear | 単一所有の箱。NIR の drop の位置で解放 |

`Indirect::Shared` / `Indirect::Unique`、`Repr::SharedVar` は Rust バックエンドの
`Rc` / `Box` / `Rc<RefCell>` と同じ意味に写す。循環参照について言えることも
Rust バックエンドと同じである。

`Nat`・`Int` の多倍長演算、文字列、ホスト効果などは `tauto-rt` の関数を
`tauto-jit` 内の `extern "C"` の shim 越しに呼ぶ。`tauto-rt` 自身は変えない。

## step 上限と `budget`

NIR の `ticked` な呼び出しで、JIT のコードも VM と同じ数だけ step を数える。
上限に達したときは VM と同じエラーで終わる。

## 検証

- 既存の case を VM と JIT の両方で走らせ、出力・終了コード・エラーを比べる。
- JIT が対象外とした関数の数を出し、境界の位置が想定どおりかを確かめる。
- 共有値の参照カウントと単一所有値の解放回数をデバッグ時に数え、リークと二重解放を検出する。

## 依存の版

Cranelift の crate（`cranelift-codegen`・`cranelift-frontend`・`cranelift-jit`・
`cranelift-module`・`cranelift-native`）は、ワークスペースの `[workspace.dependencies]`
に `=` で同じ版に完全に固定し、`Cargo.lock` をコミットする。版を上げるときは
すべてを一度に上げる。git 依存と vendor は使わない。

## 未決定

- `Tauto.eure` で JIT を無効にできるようにするかどうか。
- 構造体・enum・閉包の箱のレイアウトと、参照カウント・drop を JIT でどう扱うか。
- A 層（`fail` / `raise` / `catch`）の関数を JIT するかどうか。
- O 層の関数をどう扱うか。
