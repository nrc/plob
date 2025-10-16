use std::fmt as sfmt;

pub use fmt::FmtOptions;

pub use crate::data::lex::Token;

mod fmt;
mod lex;
mod parse;
pub mod reparse;

const OPEN_DELIMS: [char; 3] = ['{', '(', '['];
const CLOSE_DELIMS: [char; 3] = ['}', ')', ']'];
const SEPERATORS: [&str; 2] = [",", ";"];
const PAIR_SEPERATORS: [&str; 2] = ["=", ":"];

fn delimiters_match(open: char, close: char) -> bool {
    matches!(
        (open, close),
        ('{', '}') | ('[', ']') | ('(', ')') | ('<', '>')
    )
}

pub fn parse(
    text: &str,
    _line: usize,
    runtime: &crate::Runtime,
) -> Result<Data, Vec<crate::Error>> {
    let tokens = lex::Lexer::new(text.char_indices());
    let eof = lex::Token {
        kind: lex::TokenKind::Eof,
        start: text.len(),
    };
    parse_tokens(tokens.chain(Some(eof)), runtime)
}

pub fn parse_tokens(
    tokens: impl Iterator<Item = Token>,
    runtime: &crate::Runtime,
) -> Result<Data, Vec<crate::Error>> {
    let mut parser = parse::Parser::new(tokens);
    let ast = parser.seq_struct();
    if parser.errors.is_empty() {
        if let Some(ast) = ast {
            Ok(Data::Struct(parser.tokens, ast, runtime.init_meta_data()))
        } else {
            Ok(Data::Unknown)
        }
    } else {
        Err(parser.errors)
    }
}
#[derive(Clone, Debug, PartialEq)]
pub enum Data {
    Unknown,
    Atom,
    Sequence,
    // Tokens of all data, parsed node, index into metadata
    Struct(Vec<Token>, parse::Node, usize),
    Tabular,
    None,
}

impl Data {
    pub fn unwrap_structural(self) -> (Vec<Token>, parse::Node) {
        match self {
            Data::Struct(ts, n, _) => (ts, n),
            _ => unreachable!(),
        }
    }

    pub fn ty(&self) -> String {
        match self {
            Data::Unknown => "unknown".to_owned(),
            Data::Atom => "atom".to_owned(),
            Data::Sequence => "sequence".to_owned(),
            Data::Struct(..) => "structured".to_owned(),
            Data::Tabular => "tabular".to_owned(),
            Data::None => "no data".to_owned(),
        }
    }

    // TODO formatting should use reparsed AST where available.
    pub fn fmt(&self, w: &mut impl sfmt::Write, opts: &FmtOptions) -> sfmt::Result {
        match self {
            Data::Struct(ts, node, _) => node.fmt(w, opts, ts),
            Data::None => Ok(()),
            _ => write!(w, "Data"),
        }
    }

    pub fn eq_reloc(&self, other: &Data) -> bool {
        match (self, other) {
            (Data::Struct(ts1, n1, _), Data::Struct(ts2, n2, _)) => n1.eq_reloc(n2, ts1, ts2),
            (Data::None, Data::None) => true,
            (Data::Unknown, Data::Unknown) => true,
            _ => false,
        }
    }
}

impl sfmt::Display for Data {
    fn fmt(&self, f: &mut sfmt::Formatter<'_>) -> sfmt::Result {
        match self {
            Data::Struct(ts, node, _) => node.fmt(f, &FmtOptions::default(), ts),
            Data::None => Ok(()),
            _ => write!(f, "Data"),
        }
    }
}
