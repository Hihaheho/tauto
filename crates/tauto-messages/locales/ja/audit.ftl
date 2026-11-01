# `tauto audit` のメッセージ（テキスト出力。`--json` は訳さない）。

audit-usage = audit が取るのは `--json` だけである
audit-none = なし
# 行頭の 2 つの空白は FTL では消えるので、文字列リテラルで書く。
audit-externs = {"  "}extern:     { $list }
audit-axioms = {"  "}公理:       { $list }
audit-effects = {"  "}効果:       { $list }
audit-rust = {"  "}Rust:       ブリッジ { $bridge }、クレート: { $crates }
audit-javascript = {"  "}JavaScript: { $list }
audit-granted-nothing = 許可なし
audit-granted = 許可 { $kinds }
audit-command = {"  "}コマンド:   { $name }（{ $main }、{ $granted }）{ $about }
audit-not-read = {"  "}未読:       { $list }
