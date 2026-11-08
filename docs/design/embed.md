# Rust から tote をマシンで動かす（`tauto-embed`）

Rust の crate は、`build.rs` で `tauto-build` が書く facade を通して tote を呼ぶ。
facade には二つの形があり、関数と型は同じになる。

- **Rust backend の facade**: tote のコードを crate の中にコンパイルする。
- **マシンの facade**（`tauto-vm` を `tauto-embed` から使う）: crate に入るのは
  data 型、その値とマシンの値の変換、マシンを呼ぶ関数と、ビルドがコンパイルした
  プログラムのバイト列（`tauto_vm::image`）だけになる。tote を変えても crate で
  再コンパイルされるのは小さな facade だけになる。

## どちらになるか

`TAUTO_BACKEND=vm` か `TAUTO_BACKEND=rust` で選ぶ。指定がなければ、`tauto-embed`
に依存する crate の debug assertions 付きのビルドはマシンの facade に、それ以外は
Rust backend の facade になる。マシンの facade が扱えない tote（uniffi、nonresuming entry、
変換のない型の値を公開する関数: 関数、`Nat`、linear な型、link、そして下の
extern の制限に当たるもの）は、理由を書いた warning を出して Rust backend の
facade になる。

## reload

どちらの facade にも `reload() -> Result<bool, String>` がある。Rust backend の
facade は常に `Ok(false)` を返し、変更は次のビルドで入る。マシンの facade は
tote のファイルを読み、動いているコードをコンパイルしたとき（最初はビルドが
読んだとき）と中身が違えば、コンパイルし直して次の呼び出しから新しいコードを
動かす（`Ok(true)`）。いつ呼ぶかは呼ぶ側が決める。新しいコードが
コンパイルできないとき、または公開する関数や data 型が facade を作ったときと
違うとき（`tauto_nir::interface_fingerprint`。Rust の型が変わったので再ビルドが
要る）は、古いコードのまま動き続け、理由をエラーで返す。

マシンの値はスレッド間で共有しない。スレッドごとにコンパイルした tote を持ち、
`reload()` は呼んだスレッドのものを読み直す。

## 変換

`tauto_embed::Vm` が Rust の値とマシンの値を相互に変換する。標準の型の実装は
`tauto-embed` にあり、tote の data 型の実装は `tauto-rustgen` が書く
（`emit_vm_lib_tokens`）。マシンは Rust の型を知らない。data 型はパッケージの中の
番号で、constructor は data 型の中の番号で指す。fingerprint はこの順序も含むので、
reload で読み違えることはない。

## ビルドが書くプログラム

`tauto_vm::image::Image` はコンパイルしたプログラムと、外から呼ぶための公開関数の
表と data 型ごとの constructor の表を持ち、バイト列に書ける。facade はこれを
埋め込むので、最初の呼び出しはコンパイルせずに動き、debug のバイナリは tote の
ファイルがなくても動く（reload にはファイルが要る）。

バイト列に書けないもの（実行時の構文パーサ、macro host が作った宣言、リテラルと
関数以外の定数）を持つプログラムは、warning を出して、最初の呼び出しでソースから
コンパイルする。バイト列はそれを書いたマシンと同じ版でしか読まない。

## extern

マシンは extern 関数を、package の `externs` の中の番号で host に頼む
（`Op::Extern`、`Host::call_extern`）。マシンは Rust の型も関数の名前も知らず、
番号と値だけを渡す。この層は Rust に依存しないので、ほかの言語から動かすマシン
でも使える。

マシンの facade は、番号ごとに引数を変換し、Rust backend の facade と同じ
extern のラッパー（`externs`）を呼び、答えを変換して返す関数
（`tauto_externs`）を持つ。extern の型（`extern { type T }`）の値は、マシンの中
では host の値（`Value::Host`）として持つだけで、表示は `<T>` になる。

扱うのは、値で渡す引数と `&T` で渡す引数。`&T` は一度 Rust の値に変換して参照を
渡す（extern の型なら、マシンが持つ値をそのまま借りる）。`&mut T` を取る extern、
generic な extern、借用を返す extern、Tauto の関数を受け取る extern は扱わず、
その tote は Rust backend の facade になる。

extern の型は fingerprint に入る。extern を足す・型を変える reload は再ビルドが
要る。

公開する関数の `&T` の引数（extern の型以外）は、複製してマシンに渡す。
