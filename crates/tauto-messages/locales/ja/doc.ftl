# `tauto doc` のメッセージ。

doc-help =
    使い方: tauto doc FILE|DIR [-o DIR]
    ローカルの HTML とソースのスナップショットを新しいディレクトリ（既定は target/tauto/doc）に書き出す。
    証明を検査するが、プログラムは実行しない。実行時のシグネチャは型検査も証明検査もしない。
doc-usage = 使い方: tauto doc FILE|DIR [-o DIR]
doc-output-exists = { $path } はすでに存在する。新しい出力ディレクトリを選ぶこと
doc-no-sources = 文書化する .taut または .tauto のソースファイルがない
