# `tauto bind` (`tauto-bind`). The report it writes stays in English.

bind-unexpected = tauto bind: unexpected { $arg }
bind-usage = usage: { $usage }
bind-crate-mismatch = { $file }: crate is { $found }, not { $wanted }
bind-format-version = error: rustdoc JSON format_version is { $found }, tauto bind reads { $wanted } (use the nightly in rust-toolchain.toml)
bind-out-of-date = { $file } is out of date (run { $command })
bind-not-regular = { $file }: expected a regular file
bind-recovery = Recovery files are preserved at { $path }
bind-rustdoc-failed =
    error: cargo rustdoc failed:
    { $stderr }
bind-expected-block-containing = { $file }: expected a block containing { $key }
bind-dependency-texts = { $file }: { $path }: expected a list of texts
bind-dependency-unsupported = { $file }: { $path }: unsupported value
bind-dependency-version = { $file }: { $path }: expected a version or a block

# The config file.
bind-unknown-key = unknown key `{ $key }`
bind-crate-missing = `crate` is missing
bind-expected-block = expected a block
bind-expected-text = expected a text
bind-expected-texts = expected a list of texts
