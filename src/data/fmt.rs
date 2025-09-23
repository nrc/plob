use std::fmt::Write;

use crate::data::{
    self, CLOSE_DELIMS,
    lex::{Token, TokenKind},
    parse::{Node, NodeKind},
};

const FMT_MAX_WIDTH: usize = 100;
const FMT_TAB: &str = "  ";
const FMT_TAB_WIDTH: usize = FMT_TAB.len();

#[derive(Clone, Debug, Default)]
pub struct FmtOptions {
    pub depth: Option<usize>,
}

impl Node {
    pub fn fmt(&self, w: &mut impl Write, opts: &FmtOptions) -> std::fmt::Result {
        write!(w, "{}", self.kind.render(0, FMT_MAX_WIDTH, 0, opts))
    }

    fn next_char(&self) -> char {
        match &self.kind {
            NodeKind::Tok(token) | NodeKind::Trivia(token) => match &token.kind {
                TokenKind::Word(s) | TokenKind::Symbol(s) => s.chars().next().unwrap(),
                TokenKind::Delimiter(c) => *c,
                TokenKind::String(_) => '"',
                TokenKind::Newline => '\n',
                TokenKind::Comment(_) => '/',
                TokenKind::Eof => '\n',
            },
            NodeKind::Seq(nodes) => nodes[0].next_char(),
        }
    }
}

impl NodeKind {
    fn render(&self, indent: usize, available: usize, depth: usize, opts: &FmtOptions) -> String {
        match self {
            NodeKind::Tok(Token {
                kind: TokenKind::String(s),
                ..
            }) => format!("{}", s.replace('\n', "\\n").replace('\t', "\\t")),
            NodeKind::Tok(Token {
                kind: TokenKind::Delimiter(c),
                ..
            }) => c.to_string(),
            NodeKind::Tok(Token {
                kind: TokenKind::Word(s) | TokenKind::Symbol(s),
                ..
            }) => s.clone(),
            NodeKind::Trivia(_) => unreachable!(),
            NodeKind::Seq(nodes) => Self::render_seq(nodes, indent, available, depth, opts),
            _ => unreachable!(),
        }
    }

    fn render_seq(
        nodes: &[Node],
        indent: usize,
        available: usize,
        depth: usize,
        opts: &FmtOptions,
    ) -> String {
        let mut result = String::new();
        let mut hide = false;
        for n in nodes {
            if hide {
                if is_close_delimiter(n.next_char()) {
                    result.push_str(" ... ");
                    hide = false;
                } else {
                    continue;
                }
            }

            if n.is_trivial() {
                continue;
            }

            let mut available = available.saturating_sub(result.len());

            // If it is likely we'll exceed the available space, skip to multiline layout without even trying
            // to make the node fit on one line.
            if n.count() >= available / 2 {
                return Self::render_seq_multiline(nodes, indent, available, depth, opts);
            }

            if let Some(prev) = result.chars().next_back() {
                if is_open_delimiter(prev)
                    && !is_close_delimiter(n.next_char())
                    && let Some(max_depth) = opts.depth
                    && depth > max_depth
                {
                    hide = true;
                    continue;
                }

                if CharSpacing::should_space(prev, n) {
                    result.push(' ');
                    available = available.saturating_sub(1);
                }
            }

            let next = n.kind.render(indent, available, depth + 1, opts);
            result.push_str(&next);

            if next.contains('\n') || result.len() > available {
                return Self::render_seq_multiline(nodes, indent, available, depth, opts);
            }
        }
        result
    }

    fn render_seq_multiline(
        nodes: &[Node],
        indent: usize,
        mut available: usize,
        depth: usize,
        opts: &FmtOptions,
    ) -> String {
        let mut result = String::new();
        let mut hide = false;
        for n in nodes {
            if hide {
                if is_close_delimiter(n.next_char()) {
                    result.push_str(" ... ");
                    hide = false;
                } else {
                    continue;
                }
            }
            if n.is_trivial() {
                continue;
            }

            if let Some(prev) = result.chars().next_back() {
                let next = n.next_char();

                if is_open_delimiter(prev)
                    && !is_close_delimiter(next)
                    && let Some(max_depth) = opts.depth
                    && depth > max_depth
                {
                    hide = true;
                    continue;
                }

                if indent > 0
                    && data::CLOSE_DELIMS.contains(&next)
                    && !data::OPEN_DELIMS.contains(&prev)
                {
                    result.push('\n');
                    result.push_str(&FMT_TAB.repeat(indent - 1));
                    available = FMT_MAX_WIDTH.saturating_sub((indent - 1) * FMT_TAB_WIDTH);
                } else if (data::OPEN_DELIMS.contains(&prev) && !NEWLINE_CHARS.contains(&next))
                    || (NEWLINE_CHARS.contains(&prev) && !NEWLINE_CHARS.contains(&next))
                    || (available == 0
                        && CLOSE_DELIMS.contains(&prev)
                        && !NEWLINE_CHARS.contains(&next))
                {
                    result.push('\n');
                    result.push_str(&FMT_TAB.repeat(indent));
                    available = FMT_MAX_WIDTH.saturating_sub(indent * FMT_TAB_WIDTH);
                } else if CharSpacing::should_space(prev, n) {
                    result.push(' ');
                    available = available.saturating_sub(1);
                }
            }

            let next = n.kind.render(indent + 1, available, depth + 1, opts);
            available = available.saturating_sub(next.len());
            result.push_str(&next);
        }
        result
    }
}

fn is_close_delimiter(c: char) -> bool {
    data::CLOSE_DELIMS.contains(&c)
}

fn is_open_delimiter(c: char) -> bool {
    data::OPEN_DELIMS.contains(&c)
}

const NEWLINE_CHARS: [char; 2] = [',', ';'];

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum CharSpacing {
    WhiteSpace,
    Tight,
    Loose,
    OpenDelim,
    CloseDelim,
}

// TODO not reporting parsing errors? USe code for a blob, but it isn't assigned into a variable, probably a parse error?
impl CharSpacing {
    fn should_space(c: char, n: &Node) -> bool {
        let prev = CharSpacing::from_for_left(c);
        let next = CharSpacing::from_for_right(n);

        if prev == CharSpacing::WhiteSpace
            || next == CharSpacing::WhiteSpace
            || prev == CharSpacing::Tight
            || next == CharSpacing::Tight
        {
            return false;
        }

        !matches!(
            (prev, next),
            (CharSpacing::OpenDelim, CharSpacing::Loose)
                | (CharSpacing::Loose, CharSpacing::CloseDelim)
                | (CharSpacing::OpenDelim, CharSpacing::CloseDelim)
        )
    }

    fn from_for_left(c: char) -> Self {
        match c {
            '\'' | '"' => CharSpacing::Loose,
            ' ' | '\n' | '\t' => CharSpacing::WhiteSpace,
            ')' | ']' => CharSpacing::CloseDelim,
            '(' | '<' | '[' => CharSpacing::OpenDelim,
            '{' | '}' | '>' => CharSpacing::Loose,
            _ if c.is_alphabetic() => CharSpacing::Loose,
            _ if c.is_numeric() => CharSpacing::Loose,
            '.' => CharSpacing::Tight,
            _ => CharSpacing::Loose,
        }
    }

    fn from_for_right(n: &Node) -> Self {
        match &n.kind {
            NodeKind::Tok(token) | NodeKind::Trivia(token) => match &token.kind {
                TokenKind::Word(_) | TokenKind::String(_) | TokenKind::Comment(_) => {
                    CharSpacing::Loose
                }
                TokenKind::Delimiter(')' | ']') => CharSpacing::CloseDelim,
                TokenKind::Delimiter('(' | '<' | '[') => CharSpacing::OpenDelim,
                TokenKind::Delimiter(_) => CharSpacing::Loose,
                TokenKind::Newline | TokenKind::Eof => CharSpacing::WhiteSpace,
                TokenKind::Symbol(s) if matches!(&**s, "." | ":" | ";" | ",") => CharSpacing::Tight,
                _ => CharSpacing::Loose,
            },
            NodeKind::Seq(nodes) => CharSpacing::from_for_right(&nodes[0]),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    // TODO test fmt with depth
    #[test]
    fn fmt_smoke() {
        let text = r#"Command {
  source: "$foo = $bar",
  kind: Assign (Some ("foo",), Var ("bar",),),
  line: 0,
}
Command {
  source: "$foo",
  kind: Echo (Var ("foo\n",),),
  line: 0,
}"#;
        let parsed = crate::data::parse(text, 0, &crate::Runtime::new_test()).unwrap();
        let node = parsed.unwrap_structural();
        let formatted = node.kind.render(0, 80, 0, &FmtOptions::default());
        assert_eq!(
            formatted, text,
            "\nfound:```\n{formatted}\n```\nexpected:```\n{text}\n```"
        );
    }

    #[test]
    fn fmt_code() {
        let text = r#"fn from_for_left (c: char) -> Self {
  match c {
    '\'' | '"' => CharSpacing :: Loose,
    ' ' | '\n' | '\t' => CharSpacing :: WhiteSpace,
    '(' | ')' | '<' | '[' | ']' => CharSpacing :: Delim,
    '{' | '}' | '>' => CharSpacing :: Loose,
    _ if c.is_alphabetic () => CharSpacing :: Loose,
    _ if c.is_numeric () => CharSpacing :: Loose,
    '.' => CharSpacing :: Tight,
    _ => CharSpacing :: Loose,
  }
}"#;

        let parsed = crate::data::parse(text, 0, &crate::Runtime::new_test()).unwrap();
        let node = parsed.unwrap_structural();
        let formatted = node.kind.render(0, 80, 0, &FmtOptions::default());
        assert_eq!(
            formatted, text,
            "\nfound:```\n{formatted}\n```\nexpected:```\n{text}\n```"
        );
    }
}
