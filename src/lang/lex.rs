use std::mem;

/// We have to do some very basic lexing to reliably split up the source text.
pub(super) struct ScriptSplitter<'a> {
    chars: std::str::Chars<'a>,
    buf: String,
    state: SplitterState,
}

#[derive(Copy, Clone, Debug)]
enum SplitterState {
    Src,
    // The slash is pending
    Slash,
    Comment,
    Str(char),
    // The backslash has been pushed
    EscapeStr(char),
    Blob,
    // A string within a blob
    BlobStr(char),
    BlobEscapeStr(char),
}

impl ScriptSplitter<'_> {
    pub fn new(chars: std::str::Chars) -> ScriptSplitter {
        ScriptSplitter {
            chars,
            buf: String::new(),
            state: SplitterState::Src,
        }
    }
}

impl Iterator for ScriptSplitter<'_> {
    type Item = String;

    fn next(&mut self) -> Option<String> {
        for c in &mut self.chars {
            match (c, self.state) {
                ('/', SplitterState::Src) => self.state = SplitterState::Slash,
                ('/', SplitterState::Slash) => {
                    self.state = SplitterState::Comment;
                    if !self.buf.is_empty() {
                        return Some(mem::take(&mut self.buf));
                    }
                }

                ('\\', SplitterState::Str(d)) => {
                    self.buf.push(c);
                    self.state = SplitterState::EscapeStr(d);
                }
                ('\\', SplitterState::BlobStr(d)) => {
                    self.buf.push(c);
                    self.state = SplitterState::BlobEscapeStr(d);
                }

                ('\n', SplitterState::Src) | (';', SplitterState::Src) => {
                    self.state = SplitterState::Src;
                    if !self.buf.is_empty() {
                        return Some(mem::take(&mut self.buf));
                    }
                }
                ('\n', SplitterState::Slash) | (';', SplitterState::Slash) => {
                    self.buf.push('/');
                    self.state = SplitterState::Src;
                    if !self.buf.is_empty() {
                        return Some(mem::take(&mut self.buf));
                    }
                }
                ('\n', SplitterState::Comment) => {
                    self.state = SplitterState::Src;
                }

                ('`', SplitterState::Src) => {
                    self.buf.push(c);
                    self.state = SplitterState::Blob;
                }
                ('`', SplitterState::Blob) => {
                    self.buf.push(c);
                    self.state = SplitterState::Src;
                }

                ('\'', SplitterState::Src) | ('"', SplitterState::Src) => {
                    self.buf.push(c);
                    self.state = SplitterState::Str(c);
                }
                ('\'', SplitterState::Slash) | ('"', SplitterState::Slash) => {
                    self.buf.push('/');
                    self.buf.push(c);
                    self.state = SplitterState::Str(c);
                }
                ('\'', SplitterState::Blob) | ('"', SplitterState::Blob) => {
                    self.buf.push(c);
                    self.state = SplitterState::BlobStr(c);
                }
                (d1, SplitterState::Str(d2)) if d1 == d2 => {
                    self.buf.push(c);
                    self.state = SplitterState::Src;
                }
                (d1, SplitterState::BlobStr(d2)) if d1 == d2 => {
                    self.buf.push(c);
                    self.state = SplitterState::Blob;
                }

                (_, SplitterState::Src)
                | (_, SplitterState::Str(_))
                | (_, SplitterState::Blob)
                | (_, SplitterState::BlobStr(_)) => {
                    self.buf.push(c);
                }
                (_, SplitterState::Comment) => {}
                (_, SplitterState::Slash) => {
                    self.buf.push('/');
                    self.buf.push(c);
                    self.state = SplitterState::Src;
                }
                (_, SplitterState::EscapeStr(d)) => {
                    self.buf.push(c);
                    self.state = SplitterState::Str(d);
                }
                (_, SplitterState::BlobEscapeStr(d)) => {
                    self.buf.push(c);
                    self.state = SplitterState::BlobStr(d);
                }
            }
        }
        if self.buf.is_empty() {
            None
        } else {
            Some(mem::take(&mut self.buf))
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    pub(super) kind: TokenKind,
    // Relative to the current line of the script.
    pub(super) char: usize,
    pub(super) len: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum TokenKind {
    // Without the preceeding `$`
    Var(String),
    Ident(String),
    Blob(String),
    Number(i64),
    // Unescaped and excluding delimiters.
    String(String),
    Operator(Operator),
    Unknown(char),
    Eof,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Operator {
    Equals,
    Comma,
    Dot,
    Bra,
    Ket,
    LeftArrow,
    RightArrow,
    Caret,
    Hyphen,
}

impl TryFrom<char> for Operator {
    type Error = ();

    fn try_from(c: char) -> Result<Self, Self::Error> {
        match c {
            '=' => Ok(Operator::Equals),
            '.' => Ok(Operator::Dot),
            ',' => Ok(Operator::Comma),
            '(' => Ok(Operator::Bra),
            ')' => Ok(Operator::Ket),
            '<' => Ok(Operator::LeftArrow),
            '>' => Ok(Operator::RightArrow),
            '^' => Ok(Operator::Caret),
            _ => Err(()),
        }
    }
}

const OPS: [char; 8] = ['=', '.', ',', '(', ')', '<', '>', '^'];

#[derive(Copy, Clone, Debug)]
enum LexState {
    Src,
    Ident,
    Number,
    Str(char),
    EscapeStr(char),
    Blob,
    // A string within a blob
    BlobStr(char),
    BlobEscapeStr(char),
}

pub(super) struct Lexer<'a> {
    chars: std::iter::Enumerate<std::str::Chars<'a>>,
    lookahead: Option<(usize, char)>,
    buf: String,
    cur_start: usize,
    state: LexState,
}

impl Lexer<'_> {
    pub fn new(chars: std::str::Chars) -> Lexer {
        Lexer {
            chars: chars.enumerate(),
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

        let mut len = text.len();

        let kind = match self.state {
            LexState::Ident if text.starts_with('$') => {
                len -= 1;
                TokenKind::Var(text[1..].to_owned())
            }
            LexState::Ident => TokenKind::Ident(text),
            LexState::Str(_) | LexState::EscapeStr(_) => TokenKind::String(text),
            LexState::Blob | LexState::BlobStr(_) | LexState::BlobEscapeStr(_) => {
                TokenKind::Blob(text)
            }
            LexState::Number => TokenKind::Number(text.parse().unwrap()),
            LexState::Src => unreachable!(),
        };

        self.state = LexState::Src;

        Some(Token {
            kind,
            char: self.cur_start,
            len,
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
                // Variables and identifiers
                (c, LexState::Src) if c == '$' || c.is_alphabetic() => {
                    self.buf.push(c);
                    self.state = LexState::Ident;
                }
                (c, LexState::Ident) if c.is_alphanumeric() => {
                    self.buf.push(c);
                }
                (_, LexState::Ident) => {
                    self.lookahead = Some((i, c));
                    return self.token();
                }

                // Numbers
                (c, LexState::Src) if c == '-' || c.is_numeric() => {
                    self.buf.push(c);
                    self.state = LexState::Number;
                }
                (c, LexState::Number) if c.is_numeric() => {
                    self.buf.push(c);
                }
                (c, LexState::Number) => {
                    self.lookahead = Some((i, c));
                    if self.buf == "-" {
                        self.buf.clear();
                        return Some(Token {
                            kind: TokenKind::Operator(Operator::Hyphen),
                            char: self.cur_start,
                            len: 1,
                        });
                    }
                    return self.token();
                }

                // Operators
                (c, LexState::Src) if OPS.contains(&c) => {
                    return Some(Token {
                        kind: TokenKind::Operator(c.try_into().unwrap()),
                        char: self.cur_start,
                        len: 1,
                    });
                }

                // Blobs and strings
                ('`', LexState::Src) => {
                    self.state = LexState::Blob;
                }
                ('`', LexState::Blob) => {
                    return self.token();
                }

                ('\'', LexState::Src) | ('"', LexState::Src) => {
                    self.state = LexState::Str(c);
                }
                ('\'', LexState::Blob) | ('"', LexState::Blob) => {
                    self.buf.push(c);
                    self.state = LexState::BlobStr(c);
                }
                ('\\', LexState::Str(d)) => {
                    self.state = LexState::EscapeStr(d);
                }
                ('\\', LexState::BlobStr(d)) => {
                    self.buf.push(c);
                    self.state = LexState::BlobEscapeStr(d);
                }
                (_, LexState::EscapeStr(d)) => {
                    self.buf.push(c);
                    self.state = LexState::Str(d);
                }
                (_, LexState::BlobEscapeStr(d)) => {
                    self.buf.push(c);
                    self.state = LexState::BlobStr(d);
                }
                (d1, LexState::Str(d2)) if d1 == d2 => {
                    return self.token();
                }
                (d1, LexState::BlobStr(d2)) if d1 == d2 => {
                    self.buf.push(c);
                    self.state = LexState::Blob;
                }
                (_, LexState::Str(_)) | (_, LexState::Blob) | (_, LexState::BlobStr(_)) => {
                    self.buf.push(c);
                }

                // Whitespace
                (' ', LexState::Src) | ('\t', LexState::Src) => {}

                (c, LexState::Src) => {
                    return Some(Token {
                        kind: TokenKind::Unknown(c),
                        char: self.cur_start,
                        len: 1,
                    });
                }
            }
        }
        self.token()
    }
}

#[cfg(test)]
mod test {
    use super::{Operator::*, TokenKind::*, *};

    #[track_caller]
    fn assert_tokens(text: &str, expected: Vec<TokenKind>) {
        let mut split = ScriptSplitter::new(text.chars());
        let Some(text) = split.next() else {
            assert!(expected.is_empty());
            return;
        };
        assert!(split.next().is_none());
        let tokens = Lexer::new(text.chars());
        let actual: Vec<_> = tokens.map(|t| t.kind).collect();
        assert_eq!(actual, expected);
    }

    #[track_caller]
    fn assert_len(text: &str, expected: usize) {
        let mut split = ScriptSplitter::new(text.chars());
        let Some(text) = split.next() else {
            assert_eq!(expected, 0);
            return;
        };
        assert!(split.next().is_none());
        let tokens = Lexer::new(text.chars());
        let actual = tokens.count();
        assert_eq!(actual, expected);
    }

    fn s(s: &str) -> std::string::String {
        s.to_owned()
    }

    #[test]
    fn lex_simple() {
        // empty
        assert_tokens("", vec![]);
        assert_tokens("\n", vec![]);

        // whitespace
        assert_tokens(" \t ", vec![]);

        // comments
        assert_tokens("// dsafd sdf asdf sad fasdfasdfdf //sfsdfsadf", vec![]);

        // ident
        assert_tokens("foo", vec![Ident(s("foo"))]);

        // var
        assert_tokens("$foo", vec![Var(s("foo"))]);

        // operator
        assert_tokens("(= )", vec![Operator(Bra), Operator(Equals), Operator(Ket)]);

        // strings/blob
        assert_tokens("'hello'", vec![String(s("hello"))]);
        assert_tokens("\"hello\"", vec![String(s("hello"))]);
        assert_tokens("`hello`", vec![Blob(s("hello"))]);

        // unknown
        assert_tokens(" !  @", vec![Unknown('!'), Unknown('@')]);
    }

    #[test]
    fn lex_escapes() {
        assert_tokens("'he\\\" \\' llo'", vec![String(s("he\" ' llo"))]);
        assert_tokens("\"h\\\" \\'e\\lo\\\\ \"", vec![String(s("h\" 'elo\\ "))]);
    }

    #[test]
    fn lex_smoke() {
        assert_len("", 0);
        assert_len(
            "// dsfasdf sdfsf\n lots of idents should still parse // but not the comments\n",
            6,
        );
        assert_len("$0 = foo + 2 * $1.foo(bar, $baz)", 14);
        assert_len("= ( 'hello' > sdfsfdsa342s34df2", 5);
    }
}
