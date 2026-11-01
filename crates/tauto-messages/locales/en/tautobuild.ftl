tautobuild-no-out-dir = tauto-build must run from a build script (OUT_DIR is not set)
tautobuild-needs-dependency = error: Tauto.eure needs the rust dependency { $name }; add it to Cargo.toml
tautobuild-export-twice = rust.exports contains duplicate function { $name }
tautobuild-export-unknown = rust.exports function { $name } is unknown or generic; select a non-generic function
tautobuild-exports-invalid = invalid rust.exports: { $warnings }
