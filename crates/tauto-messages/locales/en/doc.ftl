# The messages of `tauto doc`.

doc-help =
    usage: tauto doc FILE|DIR [-o DIR]
    Writes a highlighted HTML page for each source file and an index to a new directory (default target/tauto/doc).
    Names link to their declarations. Does not run the program or check proofs.
doc-usage = usage: tauto doc FILE|DIR [-o DIR]
doc-output-exists = { $path } already exists; choose a new output directory
doc-no-sources = no .taut or .tauto source files to document
