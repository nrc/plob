use std::fmt::Write;

use crate::{
    Error,
    data::{
        self, FmtOptions,
        lex::{Token, TokenKind},
    },
};

pub(super) struct Parser {
    pub(super) errors: Vec<Error>,
    // TODO we don't currently produce any errors, but when we do we'll need to convert from erors
    // on data to error in the lang.
    tokens: Vec<Token>,
    cur_tok: usize,
}

impl Parser {
    pub fn new(tokens: impl Iterator<Item = Token>) -> Self {
        Parser {
            errors: Vec::new(),
            tokens: tokens.collect(),
            cur_tok: 0,
        }
    }

    fn next(&mut self) -> Token {
        let result = self.tokens[self.cur_tok].clone();
        if self.cur_tok < self.tokens.len() - 1 {
            self.cur_tok += 1;
        }
        result
    }

    fn peek(&self, lookahead: usize) -> &Token {
        let index = std::cmp::min(self.cur_tok + lookahead, self.tokens.len());
        &self.tokens[index]
    }

    pub fn seq_struct(&mut self) -> Option<Node> {
        let mut result = Vec::new();

        while let Some(node) = self.structural() {
            result.push(node);
        }

        Some(Node {
            kind: NodeKind::Seq(result),
        })
    }

    pub fn structural(&mut self) -> Option<Node> {
        Some(match &self.peek(0).kind {
            TokenKind::Delimiter(c @ '{')
            | TokenKind::Delimiter(c @ '(')
            | TokenKind::Delimiter(c @ '[') => {
                let c = *c;
                let opener = Node {
                    kind: NodeKind::Tok(self.next()),
                };
                let mut nodes = vec![opener];
                self.delimited(c, &mut nodes);
                Node {
                    kind: NodeKind::Seq(nodes),
                }
            }
            TokenKind::Word(_)
            | TokenKind::Symbol(_)
            | TokenKind::String(_)
            | TokenKind::Delimiter(_) => Node {
                kind: NodeKind::Tok(self.next()),
            },
            TokenKind::Newline | TokenKind::Comment(_) => Node {
                kind: NodeKind::Trivia(self.next()),
            },
            TokenKind::Eof => return None,
        })
    }

    // Parse a sequence up to and including a closing delimter
    fn delimited(&mut self, delimiter: char, result: &mut Vec<Node>) {
        while let Some(node) = self.structural() {
            if matches!(&node.kind, NodeKind::Tok(Token { kind: TokenKind::Delimiter(close), ..}) if data::delimiters_match(delimiter, *close))
            {
                result.push(node);
                return;
            }
            result.push(node);
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Node {
    pub(super) kind: NodeKind,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(super) enum NodeKind {
    Tok(Token),
    Trivia(Token),
    Seq(Vec<Node>),
}

const FMT_MAX_WIDTH: usize = 80;
const FMT_TAB: &str = "  ";
const FMT_TAB_WIDTH: usize = FMT_TAB.len();

impl Node {
    pub fn fmt(&self, w: &mut impl Write, opts: &FmtOptions) -> std::fmt::Result {
        write!(w, "{}", self.kind.render(0, FMT_MAX_WIDTH, 0, opts))
    }

    pub(super) fn is_trivial(&self) -> bool {
        matches!(self.kind, NodeKind::Trivia(_))
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
            }) => format!("\"{}\"", s.replace('\n', "\\n")),
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
            if let Some(prev) = result.chars().rev().next() {
                if is_open_delimiter(prev) && !is_close_delimiter(n.next_char()) {
                    if let Some(max_depth) = opts.depth {
                        if depth > max_depth {
                            hide = true;
                            continue;
                        }
                    }
                }

                use CharSpacing::*;
                match (
                    CharSpacing::from_for_left(prev),
                    CharSpacing::from_for_right(n.next_char()),
                ) {
                    (_, WhiteSpace) | (WhiteSpace, _) | (Tight, _) | (_, Tight) => {}
                    _ => {
                        result.push(' ');
                        available = available.saturating_sub(1);
                    }
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

            let mut available =
                available.saturating_sub(result.len() - result.rfind('\n').unwrap_or(0));
            if let Some(prev) = result.chars().rev().next() {
                if is_open_delimiter(prev) && !is_close_delimiter(n.next_char()) {
                    if let Some(max_depth) = opts.depth {
                        if depth > max_depth {
                            hide = true;
                            continue;
                        }
                    }
                }

                let next = n.next_char();
                if NEWLINE_CHARS.contains(&prev) && !NEWLINE_CHARS.contains(&next) {
                    result.push('\n');
                    result.push_str(&FMT_TAB.repeat(indent));
                    available = FMT_MAX_WIDTH - indent * FMT_TAB_WIDTH;
                } else if indent > 0 && data::CLOSE_DELIMS.contains(&next) {
                    result.push('\n');
                    result.push_str(&FMT_TAB.repeat(indent - 1));
                    available = FMT_MAX_WIDTH - (indent - 1) * FMT_TAB_WIDTH;
                } else {
                    use CharSpacing::*;
                    match (
                        CharSpacing::from_for_left(prev),
                        CharSpacing::from_for_right(next),
                    ) {
                        (_, WhiteSpace) | (WhiteSpace, _) | (Tight, _) | (_, Tight) => {}
                        _ => {
                            result.push(' ');
                            available = available.saturating_sub(1);
                        }
                    }
                }
            }

            let next = n.kind.render(indent + 1, available, depth + 1, opts);
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

const NEWLINE_CHARS: [char; 8] = ['{', '(', '[', '}', ')', ']', ',', ';'];

enum CharSpacing {
    WhiteSpace,
    Tight,
    Loose,
}

// TODO look at the whole token rather than just the first char (esp for symbols, two blocks next to each other should be whitespaced)
impl CharSpacing {
    fn from_for_left(c: char) -> Self {
        match c {
            '\'' | '"' => CharSpacing::Loose,
            ' ' | '\n' | '\t' => CharSpacing::WhiteSpace,
            '(' | ')' | '<' | '[' | ']' => CharSpacing::Tight,
            '{' | '}' | '>' => CharSpacing::Loose,
            _ if c.is_alphabetic() => CharSpacing::Loose,
            _ if c.is_numeric() => CharSpacing::Loose,
            '.' => CharSpacing::Tight,
            _ => CharSpacing::Loose,
        }
    }

    fn from_for_right(c: char) -> Self {
        match c {
            '\'' | '"' => CharSpacing::Loose,
            ' ' | '\n' | '\t' => CharSpacing::WhiteSpace,
            '(' | ')' | '<' | '[' | ']' => CharSpacing::Tight,
            '{' | '}' | '>' => CharSpacing::Loose,
            _ if c.is_alphabetic() => CharSpacing::Loose,
            _ if c.is_numeric() => CharSpacing::Loose,
            '.' | ':' | ';' | ',' => CharSpacing::Tight,
            _ => CharSpacing::Loose,
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
  kind: Assign(
    Some(
      "foo",
    ),
    Var(
      "bar",
    ),
  ),
  line: 0,
}
Command {
  source: "$foo",
  kind: Echo(
    Var(
      "foo\n",
    ),
  ),
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
    fn parse_struct_smoke() {
        let text = r#"Command {
source: "$foo = $bar",
kind: Assign(
    Some(
        "foo",
    ),
    Var(
        "bar",
    ),
),
line: 0,
}
Command {
source: "$foo",
kind: Echo(
    Var(
        "foo\n",
    ),
),
line: 0,
}"#;
        let result = crate::data::parse(text, 0, &crate::Runtime::new_test()).unwrap();
        eprintln!("{result}");
        result.unwrap_structural();
    }
}
