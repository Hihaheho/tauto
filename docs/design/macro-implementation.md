# tauto のマクロ：構成

[`macro.md`](macro.md) の設計を、クレートとモジュールに割り当てたもの。

カーネル（`check.rs`、`check/` の下）の規則はマクロのために変わらない。マクロが使うのは入口（宣言を一つ検査する関数を外から呼ぶ、など）だけ。

---

## 全体の構成

```text
crates/tauto-parol         tauto.par（呼び出しのトークンと、syntax・macro・NAME!(…)・quote の構文を含む）とその表
crates/tauto-grammar       文法の表のデータ型、表の読み込み、字句の駆動部、LL(k) の駆動部、型付き AST の汎用の木
                           依存：なし（std だけ）
totes/llkgen               （Nib）文法の文字列から表を作る。コミットした参照の表と一字一句同じ
crates/tauto               macros/：構文の値、衛生、展開、下ろし、由来、登録、Code、型付きマクロの変換、ステップ
                           eval.rs：関数を値の引数で呼ぶ入口と、マクロのホスト
crates/tauto-cli           tauto macro …、tauto syntax … のコマンド
std/prelude/Macro.taut          構文の値の型、Code の操作、macro_error などの効果、syn_* の builtin の宣言
lean/Proto/Macro/          `macro-semantics.md`「Lean のモジュールと証明義務」
meta/MacroScope.taut      同上（Scope.lean の tauto への移植）
cases/macro/               受け入れのケース（.eure）
```

依存の向き：`tauto` → `tauto-grammar`、`tauto` → `tauto-parol`。`tauto-grammar` は std の外のクレートに依存しない。

## 表の生成器（根拠）

- `tauto.par` の構文解析器を作る道具は `tools/tauto-parol-gen` にだけある。道具の依存は多い（CLI、乱数、並列、生成器の道具など）ので、
  道具はワークスペースの外に自分の `Cargo.lock` を持ち、その依存はルートの `Cargo.lock` と tauto の本体の供給網に入らない。
- 利用者の `syntax` の表は `totes/llkgen`（Nib）が作るので、表を作るのに道具は要らない。
  `crates/tauto-selfhost/tests/llkgen.rs` が、コミットした参照の表（`crates/tauto-grammar/tests/data`、
  `crates/tauto/tests/syntax_fixtures/.tauto-syntax`、`examples/*/.tauto-syntax`）について、`totes/llkgen` の出力が一字一句同じであることを確かめる。
- 実行部は自前（「`crates/tauto-grammar`」）。実行時に読んだ表をそのまま駆動部に渡せるように、表は実行時に作る値で持つ（`&'static` の定数にしない）。

## モジュールと API

### `tauto.par` のマクロの構文

キーワードは `KwBudget` などと同じく **文脈つき** で、同じ綴りの識別子を壊さない。

```text
// 構文のリテラル（`macro.md`「リテラルの三つの形」）。名前の位置に構文の名前を書く。
// 名前は字句では省けて、surface.rs がマクロの引数の外での省略を拒む。
// plaintext`…` は Text のまま読む（意味は組み込みの構文 plaintext のリテラルと同じ。Text が先に並ぶので MacroText との同点で勝つ）。
//
// 字句のモード：INITIAL・InParen・InBrace のどれでも、MacroDelimStart1 を読むと InMacroDelim1 に、
// MacroBlockStart3 を読むと InMacroBlock3 に入る（2・3、4・5・6 も同じ）。InMacroDelim… と InMacroBlock… では
// 改行と空白を読み飛ばさず、対応する閉じ（MacroDelimEnd…、MacroBlockEnd…）を読むと元のモードに戻る。
MacroText: <INITIAL, InParen, InBrace>/([\p{L}_][\p{L}\p{N}_]*)?`[^`\r\n]*`/ ;
MacroDelimStart3: <INITIAL, InParen, InBrace>/([\p{L}_][\p{L}\p{N}_]*)?<<<`/ ;
MacroDelimStart2: <INITIAL, InParen, InBrace>/([\p{L}_][\p{L}\p{N}_]*)?<<`/ ;
MacroDelimStart1: <INITIAL, InParen, InBrace>/([\p{L}_][\p{L}\p{N}_]*)?<`/ ;
MacroBlockStart3: <INITIAL, InParen, InBrace>/`{3}([\p{L}_][\p{L}\p{N}_]*)?[ \t]*\r?\n/ ;
MacroBlockStart4: <INITIAL, InParen, InBrace>/`{4}([\p{L}_][\p{L}\p{N}_]*)?[ \t]*\r?\n/ ;
MacroBlockStart5: <INITIAL, InParen, InBrace>/`{5}([\p{L}_][\p{L}\p{N}_]*)?[ \t]*\r?\n/ ;
MacroBlockStart6: <INITIAL, InParen, InBrace>/`{6}([\p{L}_][\p{L}\p{N}_]*)?[ \t]*\r?\n/ ;
MacroDelimEnd3: <InMacroDelim3>'`>>>' ;
MacroDelimEnd2: <InMacroDelim2>'`>>' ;
MacroDelimEnd1: <InMacroDelim1>'`>' ;
MacroTick: <InMacroDelim1, InMacroDelim2, InMacroDelim3>'`' ;     // 閉じでないバッククォート（閉じが長く一致して先に取られる）
MacroBlockEnd3: <InMacroBlock3>/`{3}/ ;   MacroTicks2: <InMacroBlock3>/`{1,2}/ ;
MacroBlockEnd4: <InMacroBlock4>/`{4}/ ;   MacroTicks3: <InMacroBlock4>/`{1,3}/ ;
MacroBlockEnd5: <InMacroBlock5>/`{5}/ ;   MacroTicks4: <InMacroBlock5>/`{1,4}/ ;
MacroBlockEnd6: <InMacroBlock6>/`{6}/ ;   MacroTicks5: <InMacroBlock6>/`{1,5}/ ;
MacroChunk: <InMacroDelim1, InMacroDelim2, InMacroDelim3, InMacroBlock3, InMacroBlock4, InMacroBlock5, InMacroBlock6>/[^`]+/ ;

MacroDelim: MacroDelim3 | MacroDelim2 | MacroDelim1 ;
MacroDelim1: MacroDelimStart1 { MacroChunk | MacroTick } MacroDelimEnd1 ;   // 2・3 も同じ
MacroBlock: MacroBlock3 | MacroBlock4 | MacroBlock5 | MacroBlock6 ;
MacroBlock3: MacroBlockStart3 { MacroChunk | MacroTicks2 } MacroBlockEnd3 ;  // 4・5・6 も同じ
Text: <INITIAL, InParen, InBrace>/"([^"\\]|\\[\\"'nrt0]|\\u\{[0-9a-fA-F]{1,6}\})*"|'[^']*'|plaintext`[^`\r\n]*`/ ;

// マクロの呼び出し NAME!( … )（`macro.md`「`macro` 宣言（登録）と呼び出し `NAME!(…)`」）。名前・!・( が空白なしで続くときだけ。
// 否定 !x、!=、効果の行 -> T ! {e} とは字句で分かれる（どれも名前の直後に !( が来ない）。
MacroBang: <INITIAL, InParen, InBrace>/[\p{L}_][\p{L}\p{N}_]*!/ ?= /\(/ ;
KwSyntax: <INITIAL, InBrace>/syntax/ ?= /[ \t]+[\p{L}_][\p{L}\p{N}_]*[ \t]*=/ ;
KwMacro:  <INITIAL, InBrace>/macro/  ?= /[ \t]+[\p{L}_][\p{L}\p{N}_]*[ \t]*=/ ;
KwQuote:  <INITIAL, InParen, InBrace>/quote/ ?= /[ \t]*\{|[ \t]+stmts[ \t]*\{/ ;
Dollar:   <INITIAL, InParen, InBrace>'$' ;

SyntaxDecl: KwSyntax Ident Eq MacroBlock ;          // 塊の名前は par でなければならない（読み込みで検査）
MacroDecl:  KwMacro Ident Eq Ident ;
SyntaxLit:  MacroText | MacroDelim | MacroBlock ;
MacroCall:  MacroBang LParen Expr RParen ;       // 中身はリテラルか式。どちらとして使うかは展開のとき（`macro.md`「`macro` 宣言（登録）と呼び出し `NAME!(…)`」）
QuoteExpr:  KwQuote [ Ident ] Block ;               // Ident は stmts だけ
Splice:     Dollar Ident | Dollar LParen Expr RParen ;
```

- `Primary` の選択肢に `SyntaxLit`、`MacroCall`、`QuoteExpr`、`Splice` がある。`OtherStmt` の選択肢に `SyntaxDecl`、`MacroDecl` がある。
  `surface.rs` は `SyntaxLit` を `TermKind::SyntaxLit`、`MacroCall` を `TermKind::MacroCall` にし、式の文として書かれた
  `MacroCall` を `Stmt::MacroCall` にする（文の位置）。名前のない `SyntaxLit` は `MacroCall` の引数そのもののときだけ受け付ける。
  型付きマクロの引数の式の中に名前のないリテラルがあれば、展開のときにエラー。
- `surface.rs` は開き・断片・閉じのトークンを一つの呼び出しにまとめる。塊は、閉じの前の空白（閉じの字下げ）の数だけ各行の頭から取り除き、行ごとのずれを `MacroCall` に持たせる
  （DSL の位置から書かれた位置を引くため。`origin.rs`）。浅い行は `macro.block_indent`。
- `Splice` は構文としてはどこでも読めるが、`surface.rs` が `quote` の外の `$` をエラーにする（`"$ is written only inside quote"`）。
- `fmt.rs`：`SyntaxLit` の中身に触れない（`Text` のリテラルの中身に触れないのと同じ）。`quote { … }` は普通のブロックと同じ字下げ。
- ケース `untagged-backtick-text-needs-the-syntax-name`（`cases/types/syntax-literals.eure`。`` `abc` `` は拒否）：`` `abc` `` は字句では名前のない `MacroText` として読めるが、
  マクロの引数の外なので `surface.rs` が拒む。
- `tauto.par` を変えたら `bash scripts/generate-tauto-parol.sh` で作り直し、`self-host.md` の表（`totes/syntax/src/tables.nib`）も作り直す。

### `totes/llkgen` と表のファイル

```text
totes/llkgen/
  src/main.nib  標準入力から文法の文字列、標準出力に表のファイル
```

- 入力の文法を `macro.md`「`syntax` 宣言」の規則で検査する（禁止の指示、`%start` が一つ、`k ≤ 3`）。
- 型の生成規則のために、**書かれた文法の形**（変形の前）を読み、非終端記号ごとに選択肢・記号・`[ ]`・`{ }`・`( )`・`^` を書き出す。
- `TautoExpr` は終端記号として予約する（文法に定義を書かせず、生成器が番号を割り当て、字句の DFA には入れない）。
- `tauto syntax gen` は tote の中の `syntax` をすべて集め、表がない・指紋が合わないものについて、`totes/llkgen` を
  `tauto build --release` でビルドして走らせる。`TAUTO_GRAMMAR_GEN` で別の実行ファイルを指せる。使われていない表は消す。

表のファイル `.tauto-syntax/<grammar_sha256>.tables`（tote の直下。コミットする）。形は `self-host.md` の `totes/syntax` の
表と同じ考え方（数は空白区切り、列の先頭に要素の数、名前は空白区切り）で、節の名前を行頭に置く：

```text
tauto-syntax-tables 1
grammar_sha256 <64 桁>
generator <表を作った生成器と、表の書き方の版>
title <名前か ->
max_k <数>
terminals <N> <名前…>
tauto_expr <終端記号の番号か -1>
non_terminals <N> <名前…>
start <番号>
productions <N> { <lhs> <attr> <len> <記号…> }          記号：非終端記号は 0 以上、終端記号は -(番号+1)。attr は 0〜4
symbol_attrs <N> { <production> <position> <attr> }
lookahead <N> { <nt> <prod0> <k> <ntrans> { <from> <term> <to> <prod> } }
classes <N> { <start_code_point> <end_code_point> <class> }
modes <N> { <名前> <nskip> <skip…> <ntrans> { <term> <kind> <target> } <nstates> { <naccept> { <term> <priority> <la_kind> <la_dfa> } <ntrans> { <class> <target> } } }
lookahead_dfas <N> { <nstates> { <accepting> <ntrans> { <class> <target> } } }
schema <N> { 型の宣言（`macro.md`「型付き AST の生成規則」）：<種類> <名前> <フィールドの数> { <名前> <型> } … }
```

- `generator` の行は、表を作った生成器と表の書き方を決める版。`totes/llkgen` は、参照の表に書かれた版の書き方（状態の番号の付け方まで）に一致するように書いてある。
- 文字クラスは区間の列（全コードポイントを走査しなくてよい）。字句の先読みは DFA を `lookahead_dfas` に番号で書く。

### `crates/tauto-grammar`

依存なし。駆動部は `self-host.md` の `totes/scan`・`totes/llk` と **同じ振る舞い** にし、差分試験する。

- 表（`Tables`）：表のファイルを読み、文法の指紋と schema を持つ。
- 字句：モードの積み上げ、最長一致、`priority`、先読み DFA、読み飛ばし。`${` は DFA より先に見る（`macro.md`「DSL の中の tauto の式（前置き `${ … }`）」）。
  `${ … }` の対応する `}` は tauto の字句で数えるので、呼び出し側（`tauto`）が渡す関数で求める。
- 構文：開始の非終端記号から、先読みの自動機械で予測し、右辺を積む。スタックは値で持ち、上限で止める（Rust の再帰をしない）。
  出力は出来事の列（非終端記号を開く・閉じる、トークン（読み飛ばしたものも）、`${ … }` の位置）か、最初の構文エラー
  （見つけたトークンと、期待する終端記号の一覧）。
- 型付き AST の組み立ては schema に従った **汎用の木**（`Ast`）まで。Nib の値にするのは `tauto` の側。

### 評価器（`eval.rs`）

- `call_function`：検査済みのプログラムの関数を名前で、値の引数で呼び、値と使ったステップ・確保の数を返す。
- `Host`：呼べる builtin の許可リスト（`macro-security.md`「マクロのホストの許可リスト」）、ステップと確保の上限、
  `macro_warn` の記録、`elab_*` に答える関数、`syn_expand` の答え。許可リストの外の builtin を呼べば実行時エラー。
- 値に `Code`（不透明）がある。`code_*` の builtin はこれだけを受け付ける。
- 確保の数え上げ：データ、資源（`Buf` など）、セル、継続の捕獲で 1 を足す。
- 普通の `tauto run` は、すべてを許すホストで同じ振る舞い。

### `crates/tauto/src/macros/`

| ファイル | 中身 |
|---|---|
| `mod.rs` | 入口。プログラムの展開 |
| `expand.rs` | ファイルごとの展開：`syntax` の表を読み、`quote` を構成子の呼び出しにし、リテラルを型付き AST の値にし、外側から呼び出しを展開する。登録（関数の型から種類を決める、行の検査、builtin の到達性の検査）、深さ・出力の大きさ・禁止の出力の検査 |
| `expand/typed.rs` | 型付きマクロ：`macro.md`「呼び出しと段」の 1〜6。`Code` と、その使用の要約 `U` を作る |
| `expand/elab.rs` | `elab_*` の操作を凍結した環境で答える（読むだけ） |
| `expand/step.rs` | 証明のステップ（[`macro-steps.md`](macro-steps.md)） |
| `syn.rs` | 表面の構文と構文の値（`Syn…`）の行き来（`Lift`、`Lower`）。原子の結びつけ（`macro.unknown_atom`、`macro.scope_extrusion`） |
| `node.rs` | 評価器の値と離れた、マクロの値の素のデータ |
| `quote.rs` | `quote { … }` と `$` を構成子の呼び出しにする |
| `scope.rs` | スコープの印、反転、解決、カーネルへの名前（`x#k`。`macro-semantics.md`「衛生」） |
| `origin.rs` | 由来の表、仮の span（`EXPANSION_BASE = 1 << 30`）、診断の位置と trace |

カーネルとの接点（**規則は変えない**。入口だけ）：

- カーネルの断片の型付きマクロ：宣言を一つ、凍結した環境（その宣言より前に受理した宣言）で検査し、指定した位置（span）の文脈と型を `HoleGoal` と同じ形で
  返す入口。穴の処理と同じ道を使い、精密化した項（暗黙の引数を書いたもの）も返す。
- `defeq`・`whnf`：`check.rs` の変換性と正規化を、凍結した環境で呼ぶ入口。
- どちらも `check.rs` の関数を外から呼ぶ入口で、`check/core.rs` には触れない（再検査は「受理した宣言を core が検査し直す」道のまま）。

### コマンド

`macro.md`「道具（AI-Native）」の通り。`tauto check --json` は展開の一覧 `expansions` を持つ（ほかのフィールドはマクロがなくても同じ）。

## 他の文書との関係

| 文書 | 関係 |
|---|---|
| [`self-host.md`](self-host.md)（`totes/scan`・`totes/llk`・`totes/syntax`） | 表の形と駆動部の振る舞いを共有する。`self-host.md` の表の書き出し（`nib_tables`）と、この文書の表のファイルは同じ項目 |
| `self-host.md`（OS の builtin） | 許可リストの外。OS の操作は効果 `Os` にする（`macro.md`「マクロ関数の行」） |
| [`rust-backend.md`](rust-backend.md) の名前空間 | 生成した型の名前（`math_Eqn` → `math.Eqn`）。`macro.md` の未決定の問い「OQ-11 生成した型の名前と名前空間」 |
| [`ownership.md`](ownership.md)「Lean での証明」 | `macro-semantics.md` の T3・T5 が使う |
