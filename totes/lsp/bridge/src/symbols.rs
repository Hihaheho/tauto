//! The signs a backslash name stands for in the editor: those the syntax reads
//! (`tauto::fmt::ESCAPES`), short names in common mathematical use, and every
//! sign of the mathematical and symbol blocks of Unicode under a name read
//! from its Unicode name (`symbols.txt`). A sign need not be part of the
//! syntax: a macro gives it its meaning.

use std::sync::OnceLock;

/// Short names, before the names read from Unicode. A name here also reaches
/// its sign under its Unicode name.
const SHORT: &[(&str, &str)] = &[
    // Arrows
    ("to", "→"),
    ("r", "→"),
    ("l", "←"),
    ("gets", "←"),
    ("u", "↑"),
    ("d", "↓"),
    ("lr", "↔"),
    ("rightarrow", "→"),
    ("leftarrow", "←"),
    ("leftrightarrow", "↔"),
    ("uparrow", "↑"),
    ("downarrow", "↓"),
    ("Rightarrow", "⇒"),
    ("Leftarrow", "⇐"),
    ("Leftrightarrow", "⇔"),
    ("implies", "⇒"),
    ("mapsto", "↦"),
    ("longrightarrow", "⟶"),
    ("longleftarrow", "⟵"),
    ("longmapsto", "⟼"),
    ("hookrightarrow", "↪"),
    ("twoheadrightarrow", "↠"),
    ("rightsquigarrow", "⇝"),
    ("leadsto", "⇝"),
    // Relations
    ("ne", "≠"),
    ("neq", "≠"),
    ("le", "≤"),
    ("leq", "≤"),
    ("ge", "≥"),
    ("geq", "≥"),
    ("ll", "≪"),
    ("gg", "≫"),
    ("equiv", "≡"),
    ("approx", "≈"),
    ("sim", "∼"),
    ("simeq", "≃"),
    ("cong", "≅"),
    ("defeq", "≝"),
    ("prec", "≺"),
    ("succ", "≻"),
    ("preceq", "≼"),
    ("succeq", "≽"),
    ("propto", "∝"),
    ("in", "∈"),
    ("notin", "∉"),
    ("ni", "∋"),
    ("subset", "⊂"),
    ("supset", "⊃"),
    ("subseteq", "⊆"),
    ("supseteq", "⊇"),
    ("ssubset", "⊊"),
    ("sqsubseteq", "⊑"),
    ("sqsupseteq", "⊒"),
    ("mid", "∣"),
    ("nmid", "∤"),
    ("parallel", "∥"),
    ("perp", "⟂"),
    ("models", "⊨"),
    ("vDash", "⊨"),
    ("dashv", "⊣"),
    ("nvdash", "⊬"),
    // Operators
    ("and", "∧"),
    ("or", "∨"),
    ("not", "¬"),
    ("wedge", "∧"),
    ("vee", "∨"),
    ("top", "⊤"),
    ("bot", "⊥"),
    ("cap", "∩"),
    ("inter", "∩"),
    ("union", "∪"),
    ("bigcap", "⋂"),
    ("bigcup", "⋃"),
    ("sqcap", "⊓"),
    ("sqcup", "⊔"),
    ("uplus", "⊎"),
    ("setminus", "∖"),
    ("emptyset", "∅"),
    ("empty", "∅"),
    ("compl", "∁"),
    ("circ", "∘"),
    ("comp", "∘"),
    ("cdot", "·"),
    ("centerdot", "⬝"),
    ("bullet", "∙"),
    ("star", "⋆"),
    ("ast", "∗"),
    ("pm", "±"),
    ("mp", "∓"),
    ("div", "÷"),
    ("oplus", "⊕"),
    ("ominus", "⊖"),
    ("otimes", "⊗"),
    ("oslash", "⊘"),
    ("odot", "⊙"),
    ("sum", "∑"),
    ("prod", "∏"),
    ("coprod", "∐"),
    ("int", "∫"),
    ("oint", "∮"),
    ("partial", "∂"),
    ("nabla", "∇"),
    ("sqrt", "√"),
    ("infty", "∞"),
    ("inf", "⊓"),
    ("sup", "⊔"),
    ("dagger", "†"),
    ("ddagger", "‡"),
    ("wr", "≀"),
    ("lhd", "◁"),
    ("rhd", "▷"),
    ("triangle", "△"),
    ("diamond", "◇"),
    ("Box", "□"),
    ("blacksquare", "■"),
    ("qed", "∎"),
    ("nexists", "∄"),
    ("therefore", "∴"),
    ("because", "∵"),
    // Brackets and dots
    ("langle", "⟨"),
    ("rangle", "⟩"),
    ("lceil", "⌈"),
    ("rceil", "⌉"),
    ("lfloor", "⌊"),
    ("rfloor", "⌋"),
    ("ldots", "…"),
    ("cdots", "⋯"),
    ("vdots", "⋮"),
    ("ddots", "⋱"),
    ("prime", "′"),
    // Letters
    ("lam", "λ"),
    ("fun", "λ"),
    ("Pi", "Π"),
    ("Sigma", "Σ"),
    ("aleph", "ℵ"),
    ("ell", "ℓ"),
    ("hbar", "ℏ"),
    ("nat", "ℕ"),
    ("rat", "ℚ"),
    ("real", "ℝ"),
    ("complex", "ℂ"),
    ("N", "ℕ"),
    ("Z", "ℤ"),
    ("Q", "ℚ"),
    ("R", "ℝ"),
    ("C", "ℂ"),
    ("deg", "°"),
];

/// The names read from Unicode, in the order of their code points.
const FROM_UNICODE: &str = include_str!("symbols.txt");

/// Every name and its sign: the syntax's escapes first, then the short names,
/// then the names read from Unicode. A name is listed once, with its first sign.
/// With it, how many come before those read from Unicode.
fn table() -> &'static (Vec<(&'static str, &'static str)>, usize) {
    static ALL: OnceLock<(Vec<(&str, &str)>, usize)> = OnceLock::new();
    ALL.get_or_init(|| {
        let mut seen = std::collections::HashSet::new();
        let mut all: Vec<(&str, &str)> = tauto::fmt::ESCAPES
            .iter()
            .chain(SHORT)
            .copied()
            .filter(|(name, _)| seen.insert(*name))
            .collect();
        let named = all.len();
        all.extend(
            FROM_UNICODE
                .lines()
                .filter(|l| !l.starts_with('#'))
                .filter_map(|l| l.split_once(' '))
                .filter(|(name, _)| seen.insert(*name)),
        );
        (all, named)
    })
}

/// Every name and its sign, the syntax's escapes and the short names first.
pub fn symbols() -> &'static [(&'static str, &'static str)] {
    &table().0
}

/// Whether the `i`th of `symbols()` is a short name or an escape of the syntax.
pub fn is_short(i: usize) -> bool {
    i < table().1
}

/// The sign `name` stands for.
pub fn sign_of(name: &str) -> Option<&'static str> {
    symbols().iter().find(|(n, _)| *n == name).map(|(_, s)| *s)
}
