# The messages of `tauto doc`.

doc-help =
    usage: tauto doc FILE|DIR [-o DIR]
    Writes local HTML and source snapshots to a new directory (default target/tauto/doc).
    Checks proofs without executing the program. Runtime signatures are not type-checked or proof-checked.
doc-usage = usage: tauto doc FILE|DIR [-o DIR]
doc-output-exists = { $path } already exists; choose a new output directory
doc-no-sources = no .taut or .tauto source files to document
