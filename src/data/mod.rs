use std::fmt;

pub fn parse(text: &str) -> Data {
    let tokens = lex::Lexer::new(text.char_indices());
    let eof = lex::Token {
        kind: lex::TokenKind::Eof,
        start: text.len(),
    };

    let mut parser = parse::Parser::new(tokens.chain(Some(eof)));
    // TODO errors
    let ast = parser.seq_struct();
    if let Some(ast) = ast {
        return Data::Struct(ast);
    }

    Data::Unknown
}

#[derive(Clone, Debug)]
pub enum Data {
    Unknown,
    Atom,
    Sequence,
    Struct(parse::Node),
    Tabular,
}

impl fmt::Display for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Data::Struct(node) => node.fmt_dbg(f, 0),
            _ => write!(f, "Data")?,
        }
        Ok(())
    }
}

mod parse {
    use std::fmt::Write;

    use crate::data::lex::{Token, TokenKind};

    pub(super) struct Parser {
        errors: Vec<(Token, String)>,
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
                TokenKind::Symbol(c @ '{')
                | TokenKind::Symbol(c @ '(')
                | TokenKind::Symbol(c @ '[') => {
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
                TokenKind::Word(_) | TokenKind::Symbol(_) | TokenKind::String(_) => Node {
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
                if matches!(&node.kind, NodeKind::Tok(Token { kind: TokenKind::Symbol(close), ..}) if delimiters_match(delimiter, *close))
                {
                    result.push(node);
                    return;
                }
                result.push(node);
            }
        }
    }

    fn delimiters_match(open: char, close: char) -> bool {
        match (open, close) {
            ('{', '}') | ('[', ']') | ('(', ')') | ('<', '>') => true,
            _ => false,
        }
    }

    #[derive(Debug, Clone, Eq, PartialEq)]
    pub struct Node {
        kind: NodeKind,
    }

    #[derive(Debug, Clone, Eq, PartialEq)]
    enum NodeKind {
        Tok(Token),
        Trivia(Token),
        Seq(Vec<Node>),
    }

    impl Node {
        pub(super) fn fmt_dbg(&self, w: &mut impl Write, indent: usize) {
            self.kind.fmt_dbg(w, indent);
        }

        pub(super) fn is_trivial(&self) -> bool {
            matches!(self.kind, NodeKind::Trivia(_))
        }
    }

    impl NodeKind {
        fn fmt_dbg(&self, w: &mut impl Write, indent: usize) {
            match self {
                NodeKind::Tok(Token {
                    kind: TokenKind::String(s),
                    ..
                }) => write!(w, "\"{s}\"").unwrap(),
                NodeKind::Tok(Token {
                    kind: TokenKind::Symbol(c),
                    ..
                }) => write!(w, "{c}").unwrap(),
                NodeKind::Tok(Token {
                    kind: TokenKind::Word(s),
                    ..
                }) => write!(w, "{s}").unwrap(),
                NodeKind::Trivia(_) => write!(w, "[..]").unwrap(),
                NodeKind::Seq(nodes) => {
                    if self.has_sub_seq() {
                        let mut first = true;
                        for n in nodes {
                            if n.is_trivial() {
                                continue;
                            }
                            if first {
                                first = false;
                                write!(w, "  ").unwrap();
                            } else {
                                write!(w, "\n").unwrap();
                                write!(w, "{}", "  ".repeat(indent)).unwrap();
                            }
                            n.fmt_dbg(w, indent + 1);
                        }
                    } else {
                        for n in nodes {
                            if n.is_trivial() {
                                continue;
                            }
                            n.fmt_dbg(w, 0);
                            write!(w, " ").unwrap();
                        }
                    }
                }
                _ => unreachable!(),
            }
        }

        fn has_sub_seq(&self) -> bool {
            match self {
                NodeKind::Seq(nodes) => nodes.iter().any(|n| matches!(n.kind, NodeKind::Seq(_))),
                _ => false,
            }
        }
    }

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn struct_smoke() {
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
            let result = crate::data::parse(text);
            assert!(matches!(result, crate::data::Data::Struct(_)));
            eprintln!("{result}");
        }
    }
}

mod lex {
    use std::mem;

    #[derive(Debug, Clone, Eq, PartialEq)]
    pub struct Token {
        pub(super) kind: TokenKind,
        // byte
        pub(super) start: usize,
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    pub(super) enum TokenKind {
        Word(String),
        Symbol(char),
        // Escaped and including quotes
        String(String),
        Newline,
        // Length of the comment
        Comment(usize),
        Eof,
    }

    #[derive(Copy, Clone, Debug)]
    enum LexState {
        Src,
        Slash,
        Comment,
        Word,
        Str(char),
        EscapeStr(char),
    }

    pub(super) struct Lexer<'a> {
        chars: std::str::CharIndices<'a>,
        lookahead: Option<(usize, char)>,
        buf: String,
        cur_start: usize,
        state: LexState,
    }

    impl Lexer<'_> {
        pub fn new(chars: std::str::CharIndices) -> Lexer<'_> {
            Lexer {
                chars: chars,
                lookahead: None,
                buf: String::new(),
                cur_start: 0,
                state: LexState::Src,
            }
        }

        // Postcondtion: self.state == Src && self.buf.is_empty()
        fn token(&mut self) -> Option<Token> {
            let text = mem::take(&mut self.buf);
            if text.is_empty() {
                self.state = LexState::Src;
                return None;
            }

            let kind = match self.state {
                LexState::Word => TokenKind::Word(text),
                LexState::Comment => TokenKind::Comment(text.len()),
                LexState::Str(_) | LexState::EscapeStr(_) => TokenKind::String(text),
                LexState::Slash => TokenKind::Symbol('/'),
                LexState::Src => unreachable!(),
            };

            self.state = LexState::Src;

            Some(Token {
                kind,
                start: self.cur_start,
            })
        }
    }

    impl Iterator for Lexer<'_> {
        type Item = Token;

        fn next(&mut self) -> Option<Token> {
            for (i, c) in self.lookahead.take().into_iter().chain(&mut self.chars) {
                if self.buf.is_empty() {
                    self.cur_start = i;
                }

                match (c, self.state) {
                    // Slash
                    ('/', LexState::Src) => self.state = LexState::Slash,
                    ('/', LexState::Slash) => {
                        self.state = LexState::Comment;
                        self.buf.push_str("//");
                    }
                    (_, LexState::Slash) => {
                        self.lookahead = Some((i, c));
                        self.state = LexState::Src;
                        return Some(Token {
                            kind: TokenKind::Symbol('/'),
                            start: self.cur_start - 1,
                        });
                    }

                    // Comments
                    ('\n', LexState::Comment) => {
                        self.lookahead = Some((i, c));
                        return self.token();
                    }
                    (_, LexState::Comment) => {
                        self.buf.push(c);
                    }

                    ('\n', LexState::Src) => {
                        return Some(Token {
                            kind: TokenKind::Newline,
                            start: self.cur_start,
                        });
                    }

                    // Words
                    (c, LexState::Src) if c.is_alphanumeric() => {
                        self.buf.push(c);
                        self.state = LexState::Word;
                    }
                    (c, LexState::Word) if c.is_alphanumeric() => {
                        self.buf.push(c);
                    }
                    ('.', LexState::Word) if self.buf.chars().all(|c| c.is_numeric()) => {
                        self.buf.push(c);
                    }
                    (_, LexState::Word) => {
                        self.lookahead = Some((i, c));
                        return self.token();
                    }

                    // Strings
                    ('\'', LexState::Src) | ('"', LexState::Src) => {
                        self.state = LexState::Str(c);
                    }
                    ('\\', LexState::Str(d)) => {
                        self.state = LexState::EscapeStr(d);
                    }
                    (_, LexState::EscapeStr(d)) => {
                        match c {
                            't' => self.buf.push('\t'),
                            'n' => self.buf.push('\n'),
                            '0' => self.buf.push('\0'),
                            '\\' => self.buf.push('\\'),
                            _ => {
                                self.buf.push('\\');
                                self.buf.push(c);
                            }
                        }
                        self.state = LexState::Str(d);
                    }
                    (d1, LexState::Str(d2)) if d1 == d2 => {
                        return self.token();
                    }
                    (_, LexState::Str(_)) => {
                        self.buf.push(c);
                    }

                    // Whitespace
                    (' ', LexState::Src) | ('\t', LexState::Src) => {}

                    // Symbols
                    (c, LexState::Src) if !c.is_alphanumeric() => {
                        return Some(Token {
                            kind: TokenKind::Symbol(c),
                            start: self.cur_start,
                        });
                    }

                    // To please the exhaustiveness checker.
                    (_, LexState::Src) => unreachable!(),
                }
            }
            self.token()
        }
    }

    #[cfg(test)]
    mod test {
        use super::{TokenKind::*, *};

        #[track_caller]
        fn assert_tokens(text: &str, expected: Vec<TokenKind>) {
            let tokens = Lexer::new(text.char_indices());
            let actual: Vec<_> = tokens.map(|t| t.kind).collect();
            assert_eq!(actual, expected);
        }

        fn s(s: &str) -> std::string::String {
            s.to_owned()
        }

        #[test]
        fn lex_simple() {
            // empty
            assert_tokens("", vec![]);
            assert_tokens("\n", vec![Newline]);

            // comment
            assert_tokens("// foo", vec![Comment(6)]);

            // word
            assert_tokens("foo", vec![Word(s("foo"))]);
            assert_tokens("4", vec![Word(s("4"))]);
            assert_tokens("4.324", vec![Word(s("4.324"))]);
            assert_tokens("3fgd", vec![Word(s("3fgd"))]);

            // symbols
            assert_tokens(
                "# ( , ; :",
                vec![
                    Symbol('#'),
                    Symbol('('),
                    Symbol(','),
                    Symbol(';'),
                    Symbol(':'),
                ],
            );

            // string
            assert_tokens("'sdfsdfsdf'", vec![String(s("sdfsdfsdf"))]);
        }

        #[test]
        fn lex_escapes() {
            assert_tokens("'hel\nlo'", vec![String(s("hel\nlo"))]);
            assert_tokens(r#"'hel\nlo'"#, vec![String(s("hel\nlo"))]);
            assert_tokens(r#"'hel\\lo'"#, vec![String(s("hel\\lo"))]);
            assert_tokens(r#"'hel\xlo'"#, vec![String(s("hel\\xlo"))]);
        }

        #[test]
        fn lex_smoke() {
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
            let tokens = Lexer::new(text.char_indices());
            let _: Vec<_> = tokens.collect();
        }
    }
}
