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
