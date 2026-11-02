no-command = コマンド { $name } はありません。tauto にもこのプロジェクトにもありません（`tauto --help` で両方の一覧が出ます）
lang-unknown = 知らない言語です: { $lang }（知っているもの: { $known }）

# The usage of the commands. The syntax itself is in `USAGE` in main.rs.
main-usage = 使い方:
main-usage-project-command = プロジェクトか、それが直接依存するトートのコマンド
main-usage-offline = 取得しない。ロックされた依存がキャッシュになければエラーになる
main-usage-lang = メッセージの言語（en, ja）。指定がなければ $TAUTO_LANG、~/.config/tauto/config.eure の `lang`、$LANG の順に見る

# `tauto try`, `fill`, `expand` and `suggest`.
main-accepted = 受理
main-rejected = 却下
main-suggest-axioms = 公理: { $axioms }
main-suggest-axioms-none = なし
main-suggest-remaining-holes = 残る穴: { $holes }
main-suggest-file-status = ファイルの状態: { $status }
main-expand-needs-by = expand には `--by` が必要だ

# `tauto fmt`.
main-fmt-not-formatted = { $path }: 整形されていない
main-fmt-fix-outside = { $file }: 修正の範囲がファイルの外にある

# `tauto run`.
main-run-tote-no-main = トート { $name } に src/main.taut も src/main.tauto もない
main-run-interrupted = （{ $steps } ステップで中断。`--steps N` で増やせる。`--allow-div` で上限をなくせる）
main-eval-text = テキスト
main-lint-unknown-option = lint: 不明なオプション { $flag }
main-fix-applied = 修正: { $file }:{ $line }:{ $col }: { $title }
main-fix-reverted = 取り消し: { $file }: { $title }（エラー { $before } -> { $after }{ $new }）
main-fix-new-errors = 。新しいエラー: { $errors }
main-fix-unfixed = 未修正: { $file }:{ $line }:{ $col }: { $message }
main-fix-unfixed-reverted = 未修正（修正を取り消した）: { $file }:{ $line }:{ $col }: { $message }
main-fix-summary = エラー { $before } -> { $after }: 修正 { $applied } 件、取り消し { $reverted } 件、未修正 { $unfixed } 件
main-fix-unreadable = 読めない
