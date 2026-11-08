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
bind-unbound = { $item }: { $reason }
bind-iterator-item = { $item }: Iterator::Item: { $reason }
bind-not-public = { $item }: not a public item of { $crate_name }
bind-only-structs-enums-functions = { $item }: only structs, enums and functions are bound
bind-type-needs-instances = { $item }: a type with type or const parameters needs its instances in the config (not supported yet)
bind-trait-not-bindable = { $item }: the trait { $trait_name } is not one that can be bound
bind-why-unsafe-fn = unsafe fn
bind-why-async-fn = async fn
bind-why-const-generic = a const generic
bind-why-generic-needs-instance = a generic function needs an instance in the config
bind-why-instance-count = the config gives { $given } type arguments, the function has { $expected }
bind-why-instance-type-unbound = the instance type { $type_name } is not bound
bind-why-mut-str = &mut str
bind-why-mut-slice = &mut [T] is not supported
bind-why-impl-trait-argument = an `impl Trait` argument
bind-why-size-nested = { $type_name } nested in a type (only a parameter, the result, or an Option result is converted)
bind-why-type = the type { $type_name }
bind-why-large-tuple = a tuple of more than two
bind-why-self-outside-impl = Self outside an impl
bind-why-type-parameter = the type parameter { $name }
bind-why-str-nested = a &str nested in a type
bind-why-alias-default-parameter = the alias { $alias } has a default parameter
bind-why-type-not-bound = the type { $type_name } is not bound
bind-why-unsized-slice = an unsized slice
bind-why-dyn-trait = dyn Trait
bind-why-impl-trait-result = an `impl Trait` result
bind-why-no-tauto-form = a type that has no tauto form
