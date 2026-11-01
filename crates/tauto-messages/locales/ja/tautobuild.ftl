tautobuild-no-out-dir = tauto-build はビルドスクリプトから実行する (OUT_DIR が設定されていない)
tautobuild-needs-dependency = error: Tauto.eure には rust の依存 { $name } が必要である。Cargo.toml に加える
tautobuild-export-twice = rust.exports に関数 { $name } が重複している
tautobuild-export-unknown = rust.exports の関数 { $name } は不明かジェネリックである。ジェネリックでない関数を選ぶ
tautobuild-exports-invalid = 不正な rust.exports: { $warnings }
