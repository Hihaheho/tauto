# `tauto bench`.

bench-help =
    使い方: { $usage }

    リリースモードで一度だけビルドし、プロセス全体の実時間を測る。
    既定値: ウォームアップ 1 回、サンプル 10 回、1 回あたりのタイムアウト 30000 ms。
    ウォームアップ: 0..100、サンプル: 1..1000、timeout-ms: 1..3600000。
    出力の上限は 1 回の実行につきストリームごとに 1 MiB。標準入力は空だ。
    実行のたびにプログラムの作用が繰り返される。コンパイルの時間は測らない。
    起動、出力の収集、監視スレッド、1 ms ごとのポーリングは測った時間に含まれる。
    1 ms 未満の差に意味を読み取らないこと。これはプロファイラではない。
bench-duplicate-option = オプションが重複している: { $option }
bench-backend-rust-only = bench が対応するのは `--backend rust` だけだ
bench-needs-integer = { $option } には 0 以上の整数が必要だ
bench-out-of-range = { $option } の値が許される範囲の外にある
bench-timeout-range = `--timeout-ms` には 1 から 3600000 までの整数が必要だ
bench-unknown-option = 知らないオプション: { $option }
bench-one-path = bench が受け取るソースファイルかパッケージディレクトリは一つだけだ
bench-needs-path = bench にはソースファイルかパッケージディレクトリが必要だ
bench-program-failed = プログラムが失敗した（{ $status }）
bench-output-changed = 実行ごとにプログラムの stdout/stderr が変わった。計測の要約は出さない
bench-cannot-read-output = プログラムの出力を読めない: { $error }
bench-output-limit = プログラムの出力がストリームあたり 1 MiB を超えた
bench-cannot-start = ベンチマークを起動できない: { $error }
bench-cannot-wait = ベンチマークの終了を待てない: { $error }
bench-timeout = プログラムがタイムアウトした（{ $ms } ms）
bench-reader-failed = { $stream } の読み取りに失敗した
bench-running = bench: ウォームアップ { $warmup } 回とサンプル { $samples } 回を実行する。プログラムの作用は毎回繰り返される
bench-run-error = { $run } 回目: { $error }
bench-overhead-note = 監視スレッドと 1 ms ごとのポーリングを含む。1 ms 未満の差には意味がない
bench-heading = rust release: プロセス全体の実時間（ms）、サンプル { $samples } 回、ウォームアップ { $warmup } 回
bench-consistent = 終了コード 0。stdout（{ $stdout } バイト）と stderr（{ $stderr } バイト）は毎回同じだった
bench-error = bench: { $error }
