//! `tauto fmt`: lays a file out again without changing a single token, except that an ASCII
//! escape (`\times`, `\forall`, …) is written as its sign (`×`, `∀`, …), and the members of a
//! product type (`A × B`) and of a tuple pattern (`#(@a x, y)`) are put in their one order: the
//! labelled ones by their labels, then the others by their types as written. A tuple value is
//! evaluated in the order it is written, so it is left as it is.
//!
//! A line is a run of tokens up to a newline that ends a statement (one
//! outside `( )` and `[ ]`). It is indented two spaces for each enclosing
//! `{`, and its tokens are spaced one way: a space after `,`, none inside
//! brackets, otherwise one space wherever the source had whitespace. A line
//! longer than [`WIDTH`] is broken at its outermost bracket that does not
//! fit (a `{ }` closed on the line, such as a record literal, counts), one argument per line, and so on inward. A line that holds a comment
//! inside brackets, or a block whose newlines matter inside brackets, is left
//! as written. The tokens of the result are checked against the source's.

use tauto_message::msg;

/// The widest a line is laid out flat.
pub const WIDTH: usize = 100;

#[derive(Debug, Clone, PartialEq)]
enum Kind {
    Word,
    Open,
    Close,
    Comma,
    Comment,
    Punct,
}

#[derive(Debug, Clone)]
struct Token {
    text: String,
    kind: Kind,
    /// Whitespace came before it.
    spaced: bool,
    /// How many newlines came before it.
    newlines: usize,
    /// Where it is in the source, in bytes.
    start: usize,
    end: usize,
    /// It is an ASCII escape (`\times`), whose text here is the sign.
    escaped: bool,
}

/// Where a syntax literal starting at `i` ends: `` name`text` ``,
/// `` name<`text`> `` (one to three `<`), or a block of three to six
/// backticks, each with its name before (or, for a block, after) the opener.
/// Its text is a language of its own, so it is one token, kept as written.
fn literal_end(chars: &[char], i: usize, word: impl Fn(char) -> bool) -> Option<usize> {
    let at = |k: usize| chars.get(k).copied();
    let mut j = i;
    if at(j).is_some_and(|c| word(c) && !c.is_ascii_digit()) {
        while at(j).is_some_and(&word) {
            j += 1;
        }
    }
    let ticks = chars[j.min(chars.len())..]
        .iter()
        .take_while(|c| **c == '`')
        .count();
    if (3..=6).contains(&ticks) {
        let mut k = j + ticks;
        while at(k).is_some_and(&word) {
            k += 1;
        }
        while matches!(at(k), Some(' ' | '\t')) {
            k += 1;
        }
        if at(k) == Some('\r') {
            k += 1;
        }
        if at(k) == Some('\n') {
            let close = vec!['`'; ticks];
            let rest = chars.get(k + 1..)?;
            let found = rest.windows(ticks).position(|w| w == close.as_slice())?;
            return Some(k + 1 + found + ticks);
        }
        return None;
    }
    let angles = chars[j.min(chars.len())..]
        .iter()
        .take_while(|c| **c == '<')
        .count();
    if (1..=3).contains(&angles) && at(j + angles) == Some('`') {
        let close: Vec<char> = std::iter::once('`')
            .chain(std::iter::repeat_n('>', angles))
            .collect();
        let rest = chars.get(j + angles + 1..)?;
        let found = rest
            .windows(close.len())
            .position(|w| w == close.as_slice())?;
        return Some(j + angles + 1 + found + close.len());
    }
    if ticks == 1 {
        let rest = chars.get(j + 1..)?;
        let found = rest.iter().position(|c| matches!(c, '`' | '\n' | '\r'))?;
        return (rest[found] == '`').then_some(j + 1 + found + 1);
    }
    None
}

/// The ASCII escapes of signs, `\times` for `×`, and the sign each stands for.
const ESCAPES: [(&str, &str); 13] = [
    ("times", "×"),
    ("land", "∧"),
    ("lor", "∨"),
    ("iff", "↔"),
    ("neg", "¬"),
    ("vdash", "⊢"),
    ("omega", "ω"),
    ("forall", "∀"),
    ("exists", "∃"),
    ("cup", "∪"),
    ("llbracket", "⟦"),
    ("rrbracket", "⟧"),
    ("square", "□"),
];

/// The escape that starts at `i` (a `\` and a whole word), the sign it stands for and where it ends.
fn escape(chars: &[char], i: usize, word: impl Fn(char) -> bool) -> Option<(&'static str, usize)> {
    if chars[i] != '\\' {
        return None;
    }
    let mut end = i + 1;
    while end < chars.len() && word(chars[end]) {
        end += 1;
    }
    let name: String = chars[i + 1..end].iter().collect();
    ESCAPES
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, sign)| (*sign, end))
}

fn lex(source: &str) -> Result<Vec<Token>, String> {
    let indexed: Vec<(usize, char)> = source.char_indices().collect();
    let chars: Vec<char> = indexed.iter().map(|(_, c)| *c).collect();
    let byte = |i: usize| indexed.get(i).map_or(source.len(), |(b, _)| *b);
    let mut out = Vec::new();
    let (mut i, mut spaced, mut newlines) = (0, false, 0);
    let word = |c: char| c.is_alphanumeric() || c == '_';
    let mut escaped: Option<&str> = None;
    while i < chars.len() {
        let c = chars[i];
        let start = i;
        let kind = if c == '\n' {
            newlines += 1;
            i += 1;
            continue;
        } else if c.is_whitespace() {
            spaced = true;
            i += 1;
            continue;
        } else if c == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            Kind::Comment
        } else if c == '/' && chars.get(i + 1) == Some(&'*') {
            i += 2;
            while i < chars.len() && !(chars[i] == '*' && chars.get(i + 1) == Some(&'/')) {
                i += 1;
            }
            if i >= chars.len() {
                return Err(msg!("tauto-fmt-unclosed-comment").to_string());
            }
            i += 2;
            Kind::Comment
        } else if c == '"' {
            i += 1;
            while i < chars.len() && chars[i] != '"' {
                i += if chars[i] == '\\' { 2 } else { 1 };
            }
            if i >= chars.len() {
                return Err(msg!("tauto-fmt-unclosed-string").to_string());
            }
            i += 1;
            Kind::Word
        } else if c == '\'' {
            i += 1;
            while i < chars.len() && chars[i] != '\'' {
                i += 1;
            }
            if i >= chars.len() {
                return Err(msg!("tauto-fmt-unclosed-string").to_string());
            }
            i += 1;
            Kind::Word
        } else if let Some(end) = literal_end(&chars, i, word) {
            i = end;
            Kind::Word
        } else if chars[i..].iter().take(10).collect::<String>() == "plaintext`" {
            i += 10;
            while i < chars.len() && chars[i] != '`' && chars[i] != '\n' {
                i += 1;
            }
            if chars.get(i) != Some(&'`') {
                return Err(msg!("tauto-fmt-unclosed-string").to_string());
            }
            i += 1;
            Kind::Word
        } else if let Some((sign, end)) = escape(&chars, i, word) {
            // `\times` is written `×`.
            i = end;
            escaped = Some(sign);
            if sign == "ω" {
                Kind::Word
            } else {
                Kind::Punct
            }
        } else if word(c) {
            // `r#name` is one word.
            if c == 'r'
                && chars.get(i + 1) == Some(&'#')
                && chars
                    .get(i + 2)
                    .is_some_and(|n| n.is_alphabetic() || *n == '_')
            {
                i += 2;
            }
            while i < chars.len() && word(chars[i]) {
                i += 1;
            }
            // `pub(open)` is one word, never broken across lines.
            if chars[start..i].iter().collect::<String>() == "pub"
                && chars[i..].iter().take(6).collect::<String>() == "(open)"
            {
                i += 6;
            }
            Kind::Word
        } else {
            i += 1;
            match c {
                '(' | '[' | '{' => Kind::Open,
                ')' | ']' | '}' => Kind::Close,
                ',' => Kind::Comma,
                _ => Kind::Punct,
            }
        };
        out.push(Token {
            escaped: escaped.is_some(),
            text: escaped
                .take()
                .map_or_else(|| chars[start..i].iter().collect(), String::from),
            kind,
            spaced: spaced || newlines > 0,
            newlines,
            start: byte(start),
            end: byte(i),
        });
        spaced = false;
        newlines = 0;
    }
    // A raw name that is not needed is written without its `r#`: one whose word is not reserved.
    // A reserved word is a name only with `r#`, wherever it stands.
    for t in out.iter_mut() {
        let Some(name) = t.text.strip_prefix("r#") else {
            continue;
        };
        if !tauto_surface::surface::print::RESERVED.contains(&name) {
            t.text = name.to_string();
        }
    }
    Ok(out)
}

/// A line, as a tree: tokens and bracketed groups of comma-separated items.
/// The most brackets open at once that `format` takes.
const MAX_BRACKETS: usize = 1_000;

/// Every bracket closes, and with its own kind; the rest of `format` relies on it.
fn balanced(tokens: &[Token]) -> Result<(), String> {
    let mut stack: Vec<&str> = Vec::new();
    for t in tokens {
        match t.kind {
            // `format` recurses into each group.
            Kind::Open if stack.len() >= MAX_BRACKETS => {
                return Err(msg!("tauto-fmt-too-deep").to_string());
            }
            Kind::Open => stack.push(&t.text),
            Kind::Close => {
                let pair = match stack.pop() {
                    Some("(") => ")",
                    Some("[") => "]",
                    Some(_) => "}",
                    None => return Err(msg!("tauto-fmt-unmatched", token = &t.text).to_string()),
                };
                if t.text != pair {
                    return Err(msg!("tauto-fmt-unmatched", token = &t.text).to_string());
                }
            }
            _ => {}
        }
    }
    match stack.last() {
        Some(open) => Err(msg!("tauto-fmt-unclosed", token = *open).to_string()),
        None => Ok(()),
    }
}

#[derive(Debug)]
enum Node {
    Tok(Token),
    Group {
        open: Token,
        items: Vec<Vec<Node>>,
        close: Token,
    },
}

/// Commas split a group's items only outside braces that stay open past the line; a line's own
/// commas (`<A, B>`) are plain tokens. A `{ }` closed on the line is a group, and so is any `{ }`
/// inside a group: there it closes on the line too, so a nested record literal can break in the
/// same pass as its parent rather than only once its parent's break gives it a line of its own.
/// An effect row (`! {Div, stdout}`) is never a group: a newline inside it does not parse.
fn tree(tokens: &[Token], i: &mut usize, in_group: bool) -> Vec<Node> {
    let mut out = Vec::new();
    let mut braces = 0usize;
    while *i < tokens.len() {
        let t = &tokens[*i];
        match t.kind {
            Kind::Close if t.text != "}" => return out,
            Kind::Close if in_group && braces == 0 => return out,
            Kind::Comma if in_group && braces == 0 => return out,
            Kind::Open
                if t.text != "{"
                    || (!after_bang(&out) && (in_group || closes_on_line(tokens, *i))) =>
            {
                let open = t.clone();
                *i += 1;
                let mut items = Vec::new();
                loop {
                    items.push(tree(tokens, i, true));
                    match tokens.get(*i) {
                        Some(t) if t.kind == Kind::Comma => *i += 1,
                        _ => break,
                    }
                }
                let close = tokens[*i].clone();
                *i += 1;
                if items.len() == 1 && items[0].is_empty() {
                    items.clear();
                }
                out.push(Node::Group { open, items, close });
            }
            _ => {
                if t.text == "{" {
                    braces += 1;
                } else if t.text == "}" {
                    braces = braces.saturating_sub(1);
                }
                out.push(Node::Tok(t.clone()));
                *i += 1;
            }
        }
    }
    out
}

/// Whether the last node is a `!`, so that a `{` after it opens an effect row.
fn after_bang(nodes: &[Node]) -> bool {
    matches!(nodes.last(), Some(Node::Tok(t)) if t.text == "!")
}

/// Whether the `{` at `i` closes on the same line, as a record literal does: then, outside other
/// brackets (where a newline would not end a field), it is a group
/// like `( )`, broken at its commas, and not a block.
fn closes_on_line(tokens: &[Token], i: usize) -> bool {
    let mut depth = 0usize;
    for t in &tokens[i..] {
        match t.kind {
            Kind::Open => depth += 1,
            Kind::Close => {
                depth -= 1;
                if depth == 0 {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// The text between two tokens laid out on one line.
fn gap(prev: Option<&str>, t: &Token) -> &'static str {
    match prev {
        None => "",
        Some("(" | "[") => "",
        Some(",") => " ",
        _ if matches!(t.text.as_str(), ")" | "]" | ",") => "",
        // A macro's `!` is joined to its argument list: `m! (x)` is laid out as `m!(x)`.
        Some("!") if t.text == "(" => "",
        _ if t.spaced => " ",
        _ => "",
    }
}

fn flat(nodes: &[Node], prev: &mut Option<String>, out: &mut String) {
    for n in nodes {
        match n {
            Node::Tok(t) => push(t, prev, out),
            Node::Group { open, items, close } => {
                push(open, prev, out);
                for (k, item) in items.iter().enumerate() {
                    if k > 0 {
                        out.push(',');
                        *prev = Some(",".into());
                    }
                    flat(item, prev, out);
                }
                push(close, prev, out);
            }
        }
    }
}

fn push(t: &Token, prev: &mut Option<String>, out: &mut String) {
    out.push_str(gap(prev.as_deref(), t));
    out.push_str(&t.text);
    *prev = Some(t.text.clone());
}

fn flat_text(nodes: &[Node]) -> String {
    let mut s = String::new();
    flat(nodes, &mut None, &mut s);
    s
}

fn width(s: &str) -> usize {
    s.chars().count()
}

/// The width of what follows a group on the same line, as far as the group must fit. Up to a
/// `=>`, all of it, with `tail`. After a `=>` the rest can break on its own, so only through
/// the next group's opening bracket: `Cons(y, ys) => f(…)` breaks inside `f(`, keeping the
/// pattern whole, and `(z: Nat) => g(…)` likewise keeps the parameter whole.
fn unbroken_width(nodes: &[Node], tail: usize) -> usize {
    let mut prev: Option<String> = None;
    let mut s = String::new();
    let mut arrow = false;
    for n in nodes {
        match n {
            Node::Group { open, items, .. } if arrow && !items.is_empty() => {
                push(open, &mut prev, &mut s);
                return width(&s);
            }
            // `=>` is two tokens, `=` and `>`.
            Node::Tok(t) if t.text == ">" && !t.spaced && prev.as_deref() == Some("=") => {
                arrow = true;
            }
            _ => {}
        }
        flat(std::slice::from_ref(n), &mut prev, &mut s);
    }
    width(&s) + tail
}

/// The width of `nodes` with `tail` after them, if the first group among them that can break does:
/// up to its opening bracket.
fn least_width(nodes: &[Node], tail: usize) -> usize {
    match nodes
        .iter()
        .position(|n| matches!(n, Node::Group { items, .. } if !items.is_empty()))
    {
        Some(g) => {
            let Node::Group { open, .. } = &nodes[g] else {
                unreachable!()
            };
            let mut s = String::new();
            let mut prev = None;
            flat(&nodes[..g], &mut prev, &mut s);
            push(open, &mut prev, &mut s);
            width(&s)
        }
        None => width(&flat_text(nodes)) + tail,
    }
}

/// Whether a `=>` comes later in `nodes`, at this level.
fn arrow_follows(nodes: &[Node]) -> bool {
    let mut prev: Option<&str> = None;
    for n in nodes {
        match n {
            Node::Tok(t) => {
                if t.text == ">" && !t.spaced && prev == Some("=") {
                    return true;
                }
                prev = Some(t.text.as_str());
            }
            Node::Group { close, .. } => prev = Some(close.text.as_str()),
        }
    }
    false
}

/// Lays out `nodes` starting at column `col` of a line indented `indent`,
/// breaking the groups that do not fit. `tail` is the width of what follows
/// on the same line. On an attribute line (`@m!(…) => inductive R`) the `=>` names what the
/// attribute is on, not a pattern's body, so the call before it may break.
fn layout(nodes: &[Node], indent: usize, tail: usize, out: &mut String) {
    let attribute = matches!(nodes.first(), Some(Node::Tok(t)) if t.text == "@");
    let mut prev: Option<String> = None;
    for (k, n) in nodes.iter().enumerate() {
        let col = out.rsplit('\n').next().map_or(0, width);
        let rest = unbroken_width(&nodes[k + 1..], tail);
        match n {
            Node::Tok(t) => push(t, &mut prev, out),
            Node::Group { open, items, close } => {
                let mut here = String::new();
                let mut p = prev.clone();
                flat(std::slice::from_ref(n), &mut p, &mut here);
                // A `{ }` breaks last: only if it does not fit with what follows broken.
                let rest = if open.text == "{" {
                    least_width(&nodes[k + 1..], tail)
                } else {
                    rest
                };
                // A group before a `=>` (an arm's pattern, a parameter) stays on one line.
                if col + width(&here) + rest <= WIDTH
                    || items.is_empty()
                    || (!attribute && arrow_follows(&nodes[k + 1..]))
                {
                    out.push_str(&here);
                    prev = p;
                    continue;
                }
                push(open, &mut prev, out);
                let inner = indent + 2;
                for (j, item) in items.iter().enumerate() {
                    out.push('\n');
                    out.push_str(&" ".repeat(inner));
                    let comma = usize::from(j + 1 < items.len());
                    layout(item, inner, comma, out);
                    if comma == 1 {
                        out.push(',');
                    }
                }
                out.push('\n');
                out.push_str(&" ".repeat(indent));
                out.push_str(&close.text);
                prev = Some(close.text.clone());
            }
        }
    }
}

/// The ASCII escapes written in `source` (`\times`, `\forall`, …), as byte ranges.
pub fn escapes(source: &str) -> Vec<(usize, usize)> {
    lex(source)
        .unwrap_or_default()
        .iter()
        .filter(|t| t.escaped)
        .map(|t| (t.start, t.end))
        .collect()
}

/// Lays out the source, returning an error for lexing failures, unmatched
/// brackets detected during layout, or changes to the token sequence.
///
/// # Panics
///
/// An unclosed parenthesis or square bracket can exhaust the tokens while
/// constructing a group, before the final bracket check.
pub fn format(source: &str) -> Result<String, String> {
    // The members of a product type and of a tuple pattern, in their one order.
    let sorted = crate::order::sort_written(source);
    let source = sorted.as_str();
    let tokens = lex(source)?;
    balanced(&tokens)?;
    let mut out = String::new();
    let mut stack: Vec<String> = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        // A line: up to a newline where only braces are open.
        let start = i;
        let depth = stack.iter().filter(|o| *o == "{").count();
        let mut verbatim = false;
        let mut j = i;
        loop {
            let t = &tokens[j];
            if t.kind == Kind::Open {
                stack.push(t.text.clone());
            } else if t.kind == Kind::Close && stack.pop().is_none() {
                return Err(msg!("tauto-fmt-unmatched", token = &t.text).to_string());
            }
            if t.kind == Kind::Comment && stack.iter().any(|o| o != "{") {
                verbatim = true;
            }
            j += 1;
            match tokens.get(j) {
                None => break,
                Some(next) if next.newlines > 0 => {
                    let only_braces = stack.iter().all(|o| o == "{");
                    if only_braces {
                        if !continues_list(&tokens[start..j], next) {
                            break;
                        }
                        // A list of what a declaration makes is kept as it was broken.
                        verbatim = true;
                        continue;
                    }
                    if stack.last().is_some_and(|o| o == "{") {
                        verbatim = true;
                    }
                }
                _ => {}
            }
        }
        let line = &tokens[start..j];
        if start > 0 {
            out.push_str(if line[0].newlines > 1 { "\n\n" } else { "\n" });
        }
        let indent = 2 * (depth - usize::from(line[0].text == "}").min(depth));
        if verbatim {
            write_verbatim(source, line, indent, &mut out);
        } else {
            out.push_str(&" ".repeat(indent));
            let mut k = 0;
            let nodes = tree(line, &mut k, false);
            if k != line.len() {
                return Err(msg!("tauto-fmt-unmatched", token = &line[k].text).to_string());
            }
            layout(&nodes, indent, 0, &mut out);
        }
        i = j;
    }
    if !stack.is_empty() {
        return Err(msg!("tauto-fmt-unclosed-bracket").to_string());
    }
    out.push('\n');
    let same = |a: &[Token], b: &[Token]| {
        let raw = |t: &str| t.strip_prefix("r#").unwrap_or(t).to_string();
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| raw(&x.text) == raw(&y.text))
    };
    if !same(&tokens, &lex(&out)?) {
        return Err(msg!("tauto-fmt-changes-tokens").to_string());
    }
    Ok(out)
}

/// Whether a list of what a declaration makes (`=> fn a, theorem b`) goes on at `next`, on a new
/// line: after its `=>` or after one of its commas.
fn continues_list(line: &[Token], next: &Token) -> bool {
    const KINDS: [&str; 6] = ["fn", "theorem", "def", "inductive", "struct", "enum"];
    let is_kind = |t: &Token| t.kind == Kind::Word && KINDS.contains(&t.text.as_str());
    // `=>` is two tokens, `=` and `>`.
    let arrow = |w: &[Token]| w[0].text == "=" && w[1].text == ">" && !w[1].spaced;
    let n = line.len();
    if n >= 2 && arrow(&line[n - 2..]) {
        return is_kind(next);
    }
    n >= 1
        && line[n - 1].text == ","
        && is_kind(next)
        && line
            .windows(4)
            .any(|w| arrow(&w[..2]) && is_kind(&w[2]) && w[3].kind == Kind::Word)
}

/// The line as written, its first line indented anew and its other lines
/// as they were, without trailing whitespace.
fn write_verbatim(source: &str, line: &[Token], indent: usize, out: &mut String) {
    let text = &source[line[0].start..line[line.len() - 1].end];
    out.push_str(&" ".repeat(indent));
    let lines: Vec<&str> = text.split('\n').map(str::trim_end).collect();
    out.push_str(&lines.join("\n"));
}

#[cfg(test)]
mod tests {
    use super::format;

    #[test]
    fn a_deep_nesting_is_an_error() {
        tauto_messages::install();
        let deep = format!("let x := {}1{}\n", "(".repeat(50_000), ")".repeat(50_000));
        assert_eq!(format(&deep), Err("the source nests too deeply".into()));
    }
}
