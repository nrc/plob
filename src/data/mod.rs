use std::fmt;

pub fn parse(text: &str) -> Result<Data, Vec<crate::Error>> {
    let tokens = lex::Lexer::new(text.char_indices());
    let eof = lex::Token {
        kind: lex::TokenKind::Eof,
        start: text.len(),
    };

    let mut parser = parse::Parser::new(tokens.chain(Some(eof)));
    let ast = parser.seq_struct();
    if parser.errors.is_empty() {
        if let Some(ast) = ast {
            Ok(Data::Struct(ast))
        } else {
            Ok(Data::Unknown)
        }
    } else {
        // TODO properly process errors
        Err(parser
            .errors
            .into_iter()
            .map(|(_, msg)| crate::Error { msg })
            .collect())
    }
}

#[derive(Clone, Debug)]
pub enum Data {
    Unknown,
    Atom,
    Sequence,
    Struct(parse::Node),
    Tabular,
}

impl Data {
    pub fn unwrap_structural(self) -> parse::Node {
        match self {
            Data::Struct(n) => n,
            _ => unreachable!(),
        }
    }
}

impl fmt::Display for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Data::Struct(node) => node.fmt(f),
            _ => write!(f, "Data"),
        }
    }
}

mod parse {
    use std::fmt::Write;

    use crate::data::lex::{Token, TokenKind};

    pub(super) struct Parser {
        pub(super) errors: Vec<(Token, String)>,
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

    const FMT_MAX_WIDTH: usize = 80;
    const FMT_TAB: &str = "  ";
    const FMT_TAB_WIDTH: usize = FMT_TAB.len();

    impl Node {
        pub(super) fn fmt(&self, w: &mut impl Write) -> std::fmt::Result {
            write!(w, "{}", self.kind.render(0, FMT_MAX_WIDTH))
        }

        pub(super) fn is_trivial(&self) -> bool {
            matches!(self.kind, NodeKind::Trivia(_))
        }

        fn next_char(&self) -> char {
            match &self.kind {
                NodeKind::Tok(token) | NodeKind::Trivia(token) => match &token.kind {
                    TokenKind::Word(s) => s.chars().next().unwrap(),
                    TokenKind::Symbol(c) => *c,
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
        fn render(&self, indent: usize, available: usize) -> String {
            match self {
                NodeKind::Tok(Token {
                    kind: TokenKind::String(s),
                    ..
                }) => format!("\"{}\"", s.replace('\n', "\\n")),
                NodeKind::Tok(Token {
                    kind: TokenKind::Symbol(c),
                    ..
                }) => c.to_string(),
                NodeKind::Tok(Token {
                    kind: TokenKind::Word(s),
                    ..
                }) => s.clone(),
                NodeKind::Trivia(_) => unreachable!(),
                NodeKind::Seq(nodes) => Self::render_seq(nodes, indent, available),
                _ => unreachable!(),
            }
        }

        fn render_seq(nodes: &[Node], indent: usize, available: usize) -> String {
            let mut result = String::new();
            for n in nodes {
                if n.is_trivial() {
                    continue;
                }

                let mut available = available.saturating_sub(result.len());
                if let Some(prev) = result.chars().rev().next() {
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

                let next = n.kind.render(indent, available);
                result.push_str(&next);

                if next.contains('\n') || result.len() > available {
                    return Self::render_seq_multiline(nodes, indent, available);
                }
            }
            result
        }

        fn render_seq_multiline(nodes: &[Node], indent: usize, available: usize) -> String {
            let mut result = String::new();
            for n in nodes {
                if n.is_trivial() {
                    continue;
                }

                let mut available =
                    available.saturating_sub(result.len() - result.rfind('\n').unwrap_or(0));
                if let Some(prev) = result.chars().rev().next() {
                    let next = n.next_char();
                    if NEWLINE_CHARS.contains(&prev) && !NEWLINE_CHARS.contains(&next) {
                        result.push('\n');
                        result.push_str(&FMT_TAB.repeat(indent));
                        available = FMT_MAX_WIDTH - indent * FMT_TAB_WIDTH;
                    } else if indent > 0 && CLOSE_DELIMS.contains(&next) {
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

                let next = n.kind.render(indent + 1, available);
                result.push_str(&next);
            }
            result
        }
    }

    const NEWLINE_CHARS: [char; 8] = ['{', '(', '[', '}', ')', ']', ',', ';'];
    const CLOSE_DELIMS: [char; 3] = ['}', ')', ']'];
    enum CharSpacing {
        WhiteSpace,
        Tight,
        Loose,
    }

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
        //use super::*;

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
            let parsed = crate::data::parse(text).unwrap();
            let node = parsed.unwrap_structural();
            let formatted = node.kind.render(0, 80);
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
            let result = crate::data::parse(text).unwrap();
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
