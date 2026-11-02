//! Explicit host IO boundary: bundle a source root for the Tauto loader.
fn main() -> std::io::Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    let (bundle, output_path) = if args.len() == 2 {
        (
            selfhost_harness::source_bundle::source_bundle(std::path::Path::new(&args[0]))?,
            &args[1],
        )
    } else if args.len() == 5 && args[0] == "--tote-inputs" {
        let root = std::path::Path::new(&args[1]);
        let tote = args[2]
            .to_str()
            .ok_or_else(|| std::io::Error::other("tote ID is not UTF-8"))?;
        // The caller supplies reviewed file IDs; this mode never sweeps a tree.
        let list = std::fs::read_to_string(&args[3])?;
        let allowed: Vec<String> = list
            .lines()
            .filter(|s| !s.is_empty() && !s.starts_with('#'))
            .map(String::from)
            .collect();
        (
            selfhost_harness::source_bundle::BundlePlan::from_tote(root, tote, &allowed)?
                .encode()?,
            &args[4],
        )
    } else {
        return Err(std::io::Error::other(
            "usage: source-bundle ROOT OUTPUT | --tote-inputs ROOT TOTE ALLOWLIST OUTPUT",
        ));
    };
    // Refuse overwrite: a bundle is a new build input, never a source edit.
    let mut output = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(output_path)?;
    std::io::Write::write_all(&mut output, bundle.as_bytes())
}
