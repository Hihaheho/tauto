//! Workspace membership and `NAME: workspace` resolution.
//!
//! See `docs/design/workspace.md`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

use tauto_message::{Message, msg};

use crate::manifest::{self, Manifest, MemberSpec, WorkspaceSection};
use crate::program::canonical_path;

/// A resolved workspace: root directory and members by `package.name`.
#[derive(Debug, Clone)]
pub struct Workspace {
    pub root: PathBuf,
    /// Member package name → member directory (canonical).
    pub members: BTreeMap<String, PathBuf>,
}

/// Affiliation path written on a tote: scalar `workspace = "…"` or map `parent`.
pub fn affiliation_path(m: &Manifest) -> Option<&str> {
    match &m.workspace {
        Some(WorkspaceSection::Affiliate(path)) => Some(path.as_str()),
        Some(WorkspaceSection::Root { parent: Some(p), .. }) => Some(p.as_str()),
        Some(WorkspaceSection::Root { parent: None, .. }) => None,
        None => None,
    }
}

/// Whether this manifest declares `workspace.members` (a workspace root).
pub fn is_workspace_root(m: &Manifest) -> bool {
    matches!(m.workspace, Some(WorkspaceSection::Root { .. }))
}

/// Immediate workspace root for membership and `NAME: workspace`: the
/// directory the tote's affiliation names, or `dir` when it is a root or has
/// no affiliation. Nested roots that declare `parent` affiliate to that
/// parent; their own `members` are a separate workspace for their children.
pub fn affiliation_root(dir: &Path) -> Result<PathBuf, Message> {
    let m = manifest::read(dir)?;
    match affiliation_path(&m) {
        Some(rel) => {
            let root = resolve_rel(dir, rel)?;
            let root_m = manifest::read(&root).map_err(|e| {
                msg!(
                    "tauto-workspace-root-unreadable",
                    tote = dir.display().to_string(),
                    root = root.display().to_string(),
                    error = e
                )
            })?;
            if !is_workspace_root(&root_m) {
                return Err(msg!(
                    "tauto-workspace-affiliation-not-root",
                    tote = dir.display().to_string(),
                    root = root.display().to_string()
                ));
            }
            Ok(canonical_path(&root))
        }
        None => Ok(canonical_path(dir)),
    }
}

/// Directory that holds `Tauto.lock` for the tote in `dir`: the outermost
/// workspace reached by following `parent` from [`affiliation_root`].
/// A `parent` cycle (self-reference or A → B → A) is an error.
pub fn lock_root(dir: &Path) -> Result<PathBuf, Message> {
    let mut root = affiliation_root(dir)?;
    let mut seen = BTreeSet::new();
    seen.insert(root.clone());
    loop {
        let m = manifest::read(&root).map_err(|e| {
            msg!(
                "tauto-workspace-root-unreadable",
                tote = dir.display().to_string(),
                root = root.display().to_string(),
                error = e
            )
        })?;
        let Some(WorkspaceSection::Root {
            parent: Some(parent),
            ..
        }) = &m.workspace
        else {
            break;
        };
        let outer = resolve_rel(&root, parent)?;
        let outer_m = manifest::read(&outer).map_err(|e| {
            msg!(
                "tauto-workspace-root-unreadable",
                tote = dir.display().to_string(),
                root = outer.display().to_string(),
                error = e
            )
        })?;
        if !is_workspace_root(&outer_m) {
            return Err(msg!(
                "tauto-workspace-affiliation-not-root",
                tote = dir.display().to_string(),
                root = outer.display().to_string()
            ));
        }
        root = canonical_path(&outer);
        if !seen.insert(root.clone()) {
            return Err(msg!(
                "tauto-workspace-parent-cycle",
                root = root.display().to_string()
            ));
        }
    }
    Ok(root)
}

/// Resolve the workspace owned at `root_dir` (the directory of that root's
/// `Tauto.eure`).
pub fn resolve(root_dir: &Path) -> Result<Workspace, Message> {
    let root_m = manifest::read(root_dir)?;
    let Some(WorkspaceSection::Root { members, parent: _ }) = &root_m.workspace else {
        return Err(msg!(
            "tauto-workspace-not-root",
            dir = root_dir.display().to_string()
        ));
    };
    let root_canon = canonical_path(root_dir);
    let mut by_name: BTreeMap<String, PathBuf> = BTreeMap::new();

    for spec in members {
        let candidates = expand_member(root_dir, spec)?;
        for candidate in candidates {
            let from_glob = matches!(spec, MemberSpec::Glob(_));
            match classify_candidate(root_dir, &root_canon, &candidate, from_glob)? {
                Candidate::Member { name, dir } => {
                    if let Some(existing) = by_name.get(&name) {
                        // The same directory listed twice (path and glob, or
                        // overlapping globs) is one member, not an error.
                        if *existing == dir {
                            continue;
                        }
                        return Err(msg!(
                            "tauto-workspace-name-twice",
                            name = name.as_str(),
                            first = existing.display().to_string(),
                            second = dir.display().to_string()
                        ));
                    }
                    by_name.insert(name, dir);
                }
                Candidate::Drop => {}
            }
        }
    }

    if by_name.is_empty() {
        return Err(msg!(
            "tauto-workspace-empty",
            root = root_dir.display().to_string()
        ));
    }

    Ok(Workspace {
        root: root_canon,
        members: by_name,
    })
}

/// Directory of workspace dependency `name` for the tote in `dir`.
pub fn dependency_member(dir: &Path, name: &str) -> Result<PathBuf, Message> {
    let m = manifest::read(dir)?;
    let root = match affiliation_path(&m) {
        Some(rel) => resolve_rel(dir, rel)?,
        None if is_workspace_root(&m) => dir.to_path_buf(),
        None => {
            return Err(msg!(
                "tauto-workspace-dep-not-member",
                name = name,
                tote = dir.display().to_string()
            ));
        }
    };
    let ws = resolve(&root)?;
    let member_canon = canonical_path(dir);
    if !ws.members.values().any(|d| *d == member_canon) {
        return Err(msg!(
            "tauto-workspace-dep-not-member",
            name = name,
            tote = dir.display().to_string()
        ));
    }
    let Some(target) = ws.members.get(name) else {
        return Err(msg!(
            "tauto-workspace-dep-missing",
            name = name,
            root = root.display().to_string()
        ));
    };
    Ok(target.clone())
}

/// Member directories of the workspace at `root_dir`, in package-name order.
pub fn member_dirs(root_dir: &Path) -> Result<Vec<PathBuf>, Message> {
    let ws = resolve(root_dir)?;
    Ok(ws.members.into_values().collect())
}

/// Workspace root whose `members` apply to CLI selection from `dir`: `dir`
/// itself when it declares `members`, otherwise its affiliation root.
pub fn workspace_for_commands(dir: &Path) -> Result<Option<PathBuf>, Message> {
    let m = manifest::read(dir)?;
    if is_workspace_root(&m) {
        return Ok(Some(canonical_path(dir)));
    }
    if affiliation_path(&m).is_some() {
        return Ok(Some(affiliation_root(dir)?));
    }
    Ok(None)
}

/// Look up member `name` in the workspace that CLI commands from `from` use.
pub fn member_named(from: &Path, name: &str) -> Result<PathBuf, Message> {
    let Some(root) = workspace_for_commands(from)? else {
        return Err(msg!(
            "tauto-workspace-tote-unknown",
            name = name,
            root = from.display().to_string()
        ));
    };
    let ws = resolve(&root)?;
    ws.members.get(name).cloned().ok_or_else(|| {
        msg!(
            "tauto-workspace-tote-unknown",
            name = name,
            root = root.display().to_string()
        )
    })
}

/// Whether `name` is a legal `--tote` argument: a package name, never a path.
pub fn is_tote_flag_name(name: &str) -> bool {
    !name.is_empty()
        && !name.contains('/')
        && !name.contains('\\')
        && name != "."
        && name != ".."
}

/// Directory named by `--tote NAME` from working directory `from`.
///
/// `NAME` is a member `package.name` of the workspace in force from `from`.
/// Outside a workspace, `--tote` is refused (use a file or directory path).
pub fn tote_flag_dir(from: &Path, name: &str) -> Result<PathBuf, Message> {
    if !is_tote_flag_name(name) {
        return Err(msg!("tauto-workspace-tote-path", name = name));
    }
    member_named(from, name)
}

enum Candidate {
    Member { name: String, dir: PathBuf },
    Drop,
}

fn classify_candidate(
    root_dir: &Path,
    root_canon: &Path,
    candidate: &Path,
    from_glob: bool,
) -> Result<Candidate, Message> {
    let eure = candidate.join("Tauto.eure");
    if !eure.is_file() {
        if from_glob {
            return Ok(Candidate::Drop);
        }
        return Err(msg!(
            "tauto-workspace-member-missing",
            path = candidate.display().to_string(),
            root = root_dir.display().to_string()
        ));
    }
    let m = manifest::read(candidate).map_err(|e| {
        msg!(
            "tauto-workspace-member-bad",
            path = candidate.display().to_string(),
            error = e
        )
    })?;
    if m.package.name.is_empty() {
        if from_glob {
            return Ok(Candidate::Drop);
        }
        return Err(msg!(
            "tauto-workspace-member-mismatch",
            path = candidate.display().to_string(),
            root = root_dir.display().to_string()
        ));
    }
    let affiliated = match affiliation_of_member(&m, candidate, root_canon)? {
        Affil::ThisRoot => true,
        Affil::None | Affil::Other => false,
    };
    if affiliated {
        return Ok(Candidate::Member {
            name: m.package.name,
            dir: canonical_path(candidate),
        });
    }
    if from_glob {
        return Ok(Candidate::Drop);
    }
    Err(msg!(
        "tauto-workspace-member-mismatch",
        path = candidate.display().to_string(),
        root = root_dir.display().to_string()
    ))
}

enum Affil {
    ThisRoot,
    None,
    Other,
}

fn affiliation_of_member(
    m: &Manifest,
    member_dir: &Path,
    root_canon: &Path,
) -> Result<Affil, Message> {
    // Outermost root member "." : workspace map with members and no parent.
    if is_workspace_root(m) && affiliation_path(m).is_none() {
        return Ok(if canonical_path(member_dir) == *root_canon {
            Affil::ThisRoot
        } else {
            // Nested root that forgot parent, or another root listed by mistake.
            Affil::Other
        });
    }
    let Some(rel) = affiliation_path(m) else {
        return Ok(Affil::None);
    };
    let pointed = resolve_rel(member_dir, rel)?;
    Ok(if canonical_path(&pointed) == *root_canon {
        Affil::ThisRoot
    } else {
        Affil::Other
    })
}

fn expand_member(root_dir: &Path, spec: &MemberSpec) -> Result<Vec<PathBuf>, Message> {
    match spec {
        MemberSpec::Path(p) => {
            check_member_path(p)?;
            if p.ends_with("Tauto.eure") || Path::new(p).file_name().is_some_and(|n| n == "Tauto.eure")
            {
                return Err(msg!(
                    "tauto-workspace-member-file",
                    path = p.as_str()
                ));
            }
            Ok(vec![resolve_rel(root_dir, p)?])
        }
        MemberSpec::Glob(pat) => {
            check_member_path(pat)?;
            if pat.contains('\0') {
                return Err(msg!("tauto-workspace-bad-glob", pattern = pat.as_str()));
            }
            let mut out = Vec::new();
            walk_glob(root_dir, Path::new(""), pat, &mut out)?;
            out.sort();
            out.dedup();
            Ok(out)
        }
    }
}

fn walk_glob(
    root: &Path,
    rel: &Path,
    pattern: &str,
    out: &mut Vec<PathBuf>,
) -> Result<(), Message> {
    // Match `rel` (relative to root, no leading ./) against `pattern`.
    // Expand by walking the tree under root. A match does not stop descent:
    // `plugins/**` must still find `plugins/a` after matching `plugins`.
    // Symlinks are not followed. Hidden names and build directories are skipped.
    let full = if rel.as_os_str().is_empty() {
        root.to_path_buf()
    } else {
        root.join(rel)
    };
    let meta = match std::fs::symlink_metadata(&full) {
        Ok(m) => m,
        Err(_) => return Ok(()),
    };
    if meta.file_type().is_symlink() || !meta.is_dir() {
        return Ok(());
    }
    let slash = path_slash(rel);
    if glob_match(pattern, &slash) {
        out.push(full.clone());
    }
    let read = std::fs::read_dir(&full).map_err(|e| {
        msg!(
            "tauto-workspace-walk",
            path = full.display().to_string(),
            error = e.to_string()
        )
    })?;
    for ent in read {
        let ent = ent.map_err(|e| {
            msg!(
                "tauto-workspace-walk",
                path = full.display().to_string(),
                error = e.to_string()
            )
        })?;
        let name = ent.file_name();
        let name = name.to_string_lossy();
        if skip_glob_dir_name(&name) {
            continue;
        }
        let ft = ent.file_type().map_err(|e| {
            msg!(
                "tauto-workspace-walk",
                path = full.display().to_string(),
                error = e.to_string()
            )
        })?;
        if ft.is_symlink() || !ft.is_dir() {
            continue;
        }
        let child_rel = if rel.as_os_str().is_empty() {
            PathBuf::from(name.as_ref())
        } else {
            rel.join(name.as_ref())
        };
        let child_slash = path_slash(&child_rel);
        if glob_prefix_ok(pattern, &child_slash) {
            walk_glob(root, &child_rel, pattern, out)?;
        }
    }
    Ok(())
}

/// Directory names glob expansion does not enter or treat as candidates.
fn skip_glob_dir_name(name: &str) -> bool {
    name == "."
        || name == ".."
        || name.starts_with('.')
        || name == "target"
        || name == "node_modules"
}

fn path_slash(p: &Path) -> String {
    p.components()
        .filter_map(|c| match c {
            Component::Normal(s) => Some(s.to_string_lossy().into_owned()),
            Component::CurDir => Some(".".into()),
            Component::ParentDir => Some("..".into()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("/")
}

/// Whether `path` matches the whole glob `pattern` (`*` / `**` / `?`).
fn glob_match(pattern: &str, path: &str) -> bool {
    glob_match_segs(
        &split_segs(pattern),
        &split_segs(path),
    )
}

fn glob_prefix_ok(pattern: &str, path: &str) -> bool {
    // A directory `path` may still lead to a match if some suffix of the
    // pattern can match under it.
    let pats = split_segs(pattern);
    let segs = split_segs(path);
    if segs.is_empty() {
        return true;
    }
    // If pattern starts with **, always ok to descend.
    if pats.first().is_some_and(|p| p == "**") {
        return true;
    }
    // Greedy: path segments must match a prefix of the pattern without consuming
    // the final unmatched pattern remainder incorrectly.
    prefix_could_match(&pats, &segs)
}

fn prefix_could_match(pats: &[String], segs: &[String]) -> bool {
    fn go(pats: &[String], segs: &[String]) -> bool {
        match (pats.first().map(String::as_str), segs.first().map(String::as_str)) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some("**"), _) => {
                // ** can absorb zero or more; try all splits.
                if go(&pats[1..], segs) {
                    return true;
                }
                if segs.is_empty() {
                    return false;
                }
                go(pats, &segs[1..]) || go(&pats[1..], &segs[1..])
            }
            (Some(p), Some(s)) => {
                if seg_match(p, s) {
                    go(&pats[1..], &segs[1..])
                } else {
                    false
                }
            }
        }
    }
    go(pats, segs)
}

fn glob_match_segs(pats: &[String], segs: &[String]) -> bool {
    match (pats.first().map(String::as_str), segs.first().map(String::as_str)) {
        (None, None) => true,
        (Some("**"), _) => {
            if pats.len() == 1 {
                return true;
            }
            // ** matches zero segments.
            if glob_match_segs(&pats[1..], segs) {
                return true;
            }
            if segs.is_empty() {
                return false;
            }
            // ** matches one or more: consume one segment, keep **.
            glob_match_segs(pats, &segs[1..])
        }
        (None, Some(_)) => false,
        (Some(_), None) => pats.iter().all(|p| p == "**"),
        (Some(p), Some(s)) => {
            if seg_match(p, s) {
                glob_match_segs(&pats[1..], &segs[1..])
            } else {
                false
            }
        }
    }
}

fn seg_match(pat: &str, seg: &str) -> bool {
    if pat == "**" {
        return false; // handled above
    }
    let pb = pat.as_bytes();
    let sb = seg.as_bytes();
    let (mut i, mut j) = (0usize, 0usize);
    let mut star = None::<(usize, usize)>;
    while j < sb.len() {
        if i < pb.len() && (pb[i] == b'?' || pb[i] == sb[j]) {
            i += 1;
            j += 1;
        } else if i < pb.len() && pb[i] == b'*' {
            star = Some((i, j));
            i += 1;
        } else if let Some((si, sj)) = star {
            i = si + 1;
            j = sj + 1;
            star = Some((si, j));
        } else {
            return false;
        }
    }
    while i < pb.len() && pb[i] == b'*' {
        i += 1;
    }
    i == pb.len()
}

fn split_segs(s: &str) -> Vec<String> {
    if s.is_empty() {
        return Vec::new();
    }
    s.split('/').filter(|p| !p.is_empty()).map(str::to_string).collect()
}

fn check_member_path(p: &str) -> Result<(), Message> {
    if p.is_empty() {
        return Err(msg!("tauto-workspace-bad-path", path = p));
    }
    let path = Path::new(p);
    if path.is_absolute() {
        return Err(msg!("tauto-workspace-bad-path", path = p));
    }
    for c in path.components() {
        match c {
            Component::Normal(s) if !s.is_empty() => {}
            Component::CurDir | Component::ParentDir => {}
            _ => return Err(msg!("tauto-workspace-bad-path", path = p)),
        }
    }
    if p.split('/').any(|s| s.is_empty()) {
        return Err(msg!("tauto-workspace-bad-path", path = p));
    }
    Ok(())
}

fn resolve_rel(base: &Path, rel: &str) -> Result<PathBuf, Message> {
    check_member_path(rel)?;
    Ok(base.join(rel))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn glob_star_one_segment() {
        assert!(glob_match("totes/*", "totes/eure"));
        assert!(!glob_match("totes/*", "totes/eure/x"));
        assert!(glob_match("plugins/**", "plugins"));
        assert!(glob_match("plugins/**", "plugins/a/b"));
        assert!(glob_match("a/*/c", "a/b/c"));
        assert!(!glob_match("a/*/c", "a/b/x/c"));
    }

    #[test]
    fn glob_starstar_keeps_descending() {
        let root = tempfile_root("glob");
        std::fs::create_dir_all(root.join("plugins/fire")).unwrap();
        std::fs::create_dir_all(root.join("plugins/ice/deep")).unwrap();
        let mut out = Vec::new();
        walk_glob(&root, Path::new(""), "plugins/**", &mut out).unwrap();
        let got: std::collections::BTreeSet<_> = out
            .into_iter()
            .map(|p| p.strip_prefix(&root).unwrap().to_path_buf())
            .collect();
        assert!(got.contains(Path::new("plugins")));
        assert!(got.contains(Path::new("plugins/fire")));
        assert!(got.contains(Path::new("plugins/ice")));
        assert!(got.contains(Path::new("plugins/ice/deep")));
    }

    #[test]
    fn glob_skips_hidden_build_dirs_and_symlinks() {
        let root = tempfile_root("glob-skip");
        std::fs::create_dir_all(root.join("app")).unwrap();
        std::fs::create_dir_all(root.join("target/crate")).unwrap();
        std::fs::create_dir_all(root.join("node_modules/pkg")).unwrap();
        std::fs::create_dir_all(root.join(".hidden/x")).unwrap();
        std::os::unix::fs::symlink(&root, root.join("loop")).unwrap();
        let mut out = Vec::new();
        walk_glob(&root, Path::new(""), "*", &mut out).unwrap();
        let got: std::collections::BTreeSet<_> = out
            .into_iter()
            .map(|p| p.strip_prefix(&root).unwrap().to_path_buf())
            .collect();
        assert_eq!(got, [PathBuf::from("app")].into_iter().collect());
    }

    #[test]
    fn nested_workspace_lock_follows_parent_membership_stays_local() {
        let root = tempfile_root("lock");
        write_eure(
            &root,
            "workspace {\n  members = [\"nested\"]\n}\n",
        );
        write_eure(
            &root.join("nested"),
            "package { name = \"nested\" version = \"0.1.0\" }\nworkspace {\n  parent = \"..\"\n  members = [\"demo\"]\n}\n",
        );
        write_eure(
            &root.join("nested/demo"),
            "package { name = \"demo\" version = \"0.1.0\" }\nworkspace = \"..\"\n",
        );
        let outer = canonical_path(&root);
        let nested = canonical_path(&root.join("nested"));
        assert_eq!(affiliation_root(&root.join("nested/demo")).unwrap(), nested);
        assert_eq!(affiliation_root(&root.join("nested")).unwrap(), outer);
        assert_eq!(
            workspace_for_commands(&root.join("nested")).unwrap(),
            Some(nested.clone())
        );
        assert_eq!(lock_root(&root.join("nested")).unwrap(), outer);
        assert_eq!(lock_root(&root.join("nested/demo")).unwrap(), outer);
        assert_eq!(lock_root(&root).unwrap(), outer);
        assert_eq!(
            member_named(&root.join("nested/demo"), "demo").unwrap(),
            canonical_path(&root.join("nested/demo"))
        );
        assert_eq!(
            member_named(&root.join("nested"), "demo").unwrap(),
            canonical_path(&root.join("nested/demo"))
        );
    }

    #[test]
    fn path_and_glob_same_directory_are_one_member() {
        let root = tempfile_root("dedupe");
        write_eure(
            &root,
            "workspace {\n  members = [\".\", \"lib\", glob`*`]\n}\npackage { name = \"root\" version = \"0.1.0\" }\n",
        );
        write_eure(
            &root.join("lib"),
            "package { name = \"lib\" version = \"0.1.0\" }\nworkspace = \"..\"\n",
        );
        let ws = resolve(&root).unwrap();
        assert_eq!(ws.members.len(), 2);
        assert!(ws.members.contains_key("root"));
        assert!(ws.members.contains_key("lib"));
    }

    #[test]
    fn parent_self_reference_is_a_cycle() {
        let root = tempfile_root("cycle-self");
        write_eure(
            &root,
            "workspace {\n  parent = \".\"\n  members = [\".\"]\n}\npackage { name = \"loop\" version = \"0.1.0\" }\n",
        );
        let err = lock_root(&root).unwrap_err().to_string();
        assert!(err.contains("cycle") || err.contains("循環"), "{err}");
    }

    #[test]
    fn parent_mutual_reference_is_a_cycle() {
        let root = tempfile_root("cycle-ab");
        write_eure(
            &root.join("a"),
            "workspace {\n  parent = \"../b\"\n  members = [\"demo\"]\n}\n",
        );
        write_eure(
            &root.join("b"),
            "workspace {\n  parent = \"../a\"\n  members = [\"demo\"]\n}\n",
        );
        write_eure(
            &root.join("a/demo"),
            "package { name = \"demo\" version = \"0.1.0\" }\nworkspace = \"..\"\n",
        );
        let err = lock_root(&root.join("a/demo")).unwrap_err().to_string();
        assert!(err.contains("cycle") || err.contains("循環"), "{err}");
    }

    #[test]
    fn tote_flag_requires_a_workspace_member() {
        let root = tempfile_root("tote-flag");
        write_eure(
            &root,
            "package { name = \"alone\" version = \"0.1.0\" }\n",
        );
        let err = tote_flag_dir(&root, "alone").unwrap_err().to_string();
        assert!(
            err.contains("not a member")
                || err.contains("メンバーではない")
                || err.contains("tote-unknown"),
            "{err}"
        );
        assert!(tote_flag_dir(&root, "./alone").is_err());
        assert!(tote_flag_dir(&root, ".").is_err());
    }

    fn write_eure(dir: &Path, text: &str) {
        std::fs::create_dir_all(dir).unwrap();
        std::fs::write(dir.join("Tauto.eure"), text).unwrap();
    }

    fn tempfile_root(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "tauto-ws-{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }
}
