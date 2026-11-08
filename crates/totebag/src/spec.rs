//! Where a tote comes from, and the identifiers that fix it: a Git
//! repository, a ref in it and a directory; a full commit ID; the SHA-256 of
//! the source tree.

use std::fmt;

use tauto_rt::Text;

/// A tote in a Git repository: `semver { git = "https://…" ref = "refs/heads/main" dir = "semver" }`,
/// a binding a line in `Tauto.eure`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GitSource {
    /// An `https://` URL without credentials, query or fragment, or a
    /// `file:///` URL of a repository on this machine.
    pub url: String,
    /// A full ref, `refs/heads/…` or `refs/tags/…`: where updates are looked for.
    pub reference: String,
    /// The tote's directory in the repository, `""` for its root.
    pub dir: String,
    /// The project its revisions are known as in the indexes a trust policy
    /// names, `sha256:<hex>`: when a project has a policy, what it adopts
    /// from here must be eligible under it.
    pub project: Option<String>,
}

impl GitSource {
    pub fn check(&self) -> Result<(), String> {
        check_url(&self.url)?;
        check_ref(&self.reference)?;
        check_dir(&self.dir)?;
        if let Some(p) = &self.project {
            crate::index::strict::sha256(p).map_err(|e| e.to_string())?;
        }
        Ok(())
    }

    pub fn project_id(&self) -> Option<[u8; 32]> {
        self.project
            .as_deref()
            .map(|p| crate::index::strict::sha256(p).expect("checked"))
    }

    pub fn is_local(&self) -> bool {
        self.url.starts_with("file:///")
    }
}

impl fmt::Display for GitSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.url, self.reference)?;
        if !self.dir.is_empty() {
            write!(f, " ({})", self.dir)?;
        }
        Ok(())
    }
}

pub fn check_url(url: &str) -> Result<(), String> {
    use crate::core::generated::api::{TbUrlProblem as P, tb_check_url};
    let why = match tb_check_url(Text::from(url)) {
        None => return Ok(()),
        Some(P::UrlCharacters) => "totebag-url-characters",
        Some(P::UrlQuery) => "totebag-url-query",
        Some(P::UrlNoHost) => "totebag-url-no-host",
        Some(P::UrlCredentials) => "totebag-url-credentials",
        Some(P::UrlFilePath) => "totebag-url-file-path",
        Some(P::UrlNotNormal) => "totebag-url-not-normal",
        Some(P::UrlScheme) => "totebag-url-scheme",
    };
    Err(say!(
        "totebag-bad-url",
        url = format!("{url:?}"),
        why = tauto_message::Message::new(why)
    ))
}

/// A full ref under `refs/heads/` or `refs/tags/`, as `git check-ref-format`
/// takes it, without `HEAD`, patterns or `@{`.
pub fn check_ref(r: &str) -> Result<(), String> {
    if crate::core::generated::api::tb_check_ref(Text::from(r)) {
        Ok(())
    } else {
        Err(say!("totebag-bad-ref", reference = format!("{r:?}")))
    }
}

/// A relative directory of plain components (`semver`, `libs/text`), or `""`.
pub fn check_dir(dir: &str) -> Result<(), String> {
    if crate::core::generated::api::tb_check_dir(Text::from(dir)) {
        Ok(())
    } else {
        Err(say!("totebag-bad-dir", dir = format!("{dir:?}")))
    }
}

/// A full commit ID with its object format: `sha1:<40 hex>` or `sha256:<64 hex>`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rev(String);

impl Rev {
    pub fn parse(s: &str) -> Result<Rev, String> {
        if crate::core::generated::api::tb_check_rev(Text::from(s)) {
            Ok(Rev(s.to_string()))
        } else {
            Err(say!("totebag-bad-rev", rev = format!("{s:?}")))
        }
    }

    /// The commit ID as Git prints it, `0123…`.
    pub fn from_git(hex: &str) -> Result<Rev, String> {
        match hex.len() {
            40 => Rev::parse(&format!("sha1:{hex}")),
            64 => Rev::parse(&format!("sha256:{hex}")),
            _ => Err(say!("totebag-bad-git-rev", rev = format!("{hex:?}"))),
        }
    }

    pub fn hex(&self) -> &str {
        self.0.split_once(':').map_or("", |(_, h)| h)
    }

    pub fn format(&self) -> &str {
        self.0.split_once(':').map_or("", |(f, _)| f)
    }

    /// The first 12 digits, for messages.
    pub fn short(&self) -> &str {
        &self.hex()[..12]
    }
}

impl fmt::Display for Rev {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// The SHA-256 of a source tree in the `source-v1` form: `sha256:<64 hex>`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceId(String);

impl SourceId {
    pub fn parse(s: &str) -> Result<SourceId, String> {
        if crate::core::generated::api::tb_check_source_id(Text::from(s)) {
            Ok(SourceId(s.to_string()))
        } else {
            Err(say!("totebag-bad-source-id", id = format!("{s:?}")))
        }
    }

    pub(crate) fn from_hex(hex: String) -> SourceId {
        SourceId(format!("sha256:{hex}"))
    }

    pub fn hex(&self) -> &str {
        &self.0["sha256:".len()..]
    }

    pub fn short(&self) -> &str {
        &self.hex()[..12]
    }
}

impl fmt::Display for SourceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn urls() {
        assert!(check_url("https://example.com/tauto/monorepo").is_ok());
        assert!(check_url("file:///srv/git/text.git").is_ok());
        for bad in [
            "http://github.com/a/b",
            "https://user:pw@github.com/a/b",
            "https://github.com/a/b?x=1",
            "https://github.com/a/b#main",
            "https://",
            "file://relative/path",
            "file:///srv/../etc",
            "git@github.com:a/b",
            "https://github.com/a b",
        ] {
            assert!(check_url(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn refs() {
        for good in [
            "refs/heads/main",
            "refs/tags/v1.0.0",
            "refs/heads/release/1.x",
        ] {
            assert!(check_ref(good).is_ok(), "{good}");
        }
        for bad in [
            "main",
            "HEAD",
            "refs/heads/",
            "refs/remotes/origin/main",
            "refs/heads/a..b",
            "refs/heads/*",
            "refs/heads/.hidden",
            "refs/heads/a.lock",
            "refs/heads/a//b",
            "refs/heads/a@{1}",
            "refs/heads/a.",
        ] {
            assert!(check_ref(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn dirs() {
        for good in ["", "semver", "libs/text", "a.b_c-d"] {
            assert!(check_dir(good).is_ok(), "{good}");
        }
        for bad in ["/abs", "a/", "a//b", "..", "a/../b", ".", "a b", "a\\b"] {
            assert!(check_dir(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn ids() {
        let hex = "0123456789abcdef0123456789abcdef01234567";
        let rev = Rev::from_git(hex).unwrap();
        assert_eq!(rev.to_string(), format!("sha1:{hex}"));
        assert_eq!(rev.format(), "sha1");
        assert!(Rev::parse("sha1:0123").is_err());
        assert!(Rev::parse(&format!("sha1:{}", hex.to_uppercase())).is_err());
        assert!(SourceId::parse(&format!("sha256:{}", "a".repeat(64))).is_ok());
        assert!(SourceId::parse(&"a".repeat(64)).is_err());
    }
}
