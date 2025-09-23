use std::fmt as sfmt;

pub use fmt::FmtOptions;

mod fmt;
mod lex;
mod parse;
pub mod reparse;

const OPEN_DELIMS: [char; 3] = ['{', '(', '['];
const CLOSE_DELIMS: [char; 3] = ['}', ')', ']'];
const SEPERATORS: [&str; 2] = [",", ";"];
const PAIR_SEPERATORS: [&str; 2] = ["=", ":"];

fn delimiters_match(open: char, close: char) -> bool {
    match (open, close) {
        ('{', '}') | ('[', ']') | ('(', ')') | ('<', '>') => true,
        _ => false,
    }
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

    let mut parser = parse::Parser::new(tokens.chain(Some(eof)));
    let ast = parser.seq_struct();
    if parser.errors.is_empty() {
        if let Some(ast) = ast {
            Ok(Data::Struct(ast, runtime.init_meta_data()))
        } else {
            Ok(Data::Unknown)
        }
    } else {
        Err(parser.errors)
    }
}

#[derive(Clone, Debug)]
pub enum Data {
    Unknown,
    Atom,
    Sequence,
    Struct(parse::Node, usize),
    Tabular,
}

impl Data {
    pub fn unwrap_structural(self) -> parse::Node {
        match self {
            Data::Struct(n, _) => n,
            _ => unreachable!(),
        }
    }

    pub fn ty(&self) -> String {
        match self {
            Data::Unknown => "unknown".to_owned(),
            Data::Atom => "atom".to_owned(),
            Data::Sequence => "sequence".to_owned(),
            Data::Struct(_, _) => "structured".to_owned(),
            Data::Tabular => "tabular".to_owned(),
        }
    }

    // TODO formatting should use reparsed AST where available.
    pub fn fmt(&self, w: &mut impl sfmt::Write, opts: &FmtOptions) -> sfmt::Result {
        match self {
            Data::Struct(node, _) => node.fmt(w, opts),
            _ => write!(w, "Data"),
        }
    }
}

impl sfmt::Display for Data {
    fn fmt(&self, f: &mut sfmt::Formatter<'_>) -> sfmt::Result {
        match self {
            Data::Struct(node, _) => node.fmt(f, &FmtOptions::default()),
            _ => write!(f, "Data"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct NodePath {
    root: NodePathRoot,
    steps: Vec<usize>,
}

#[derive(Clone, Debug)]
pub enum NodePathRoot {
    Absolute,
    Parent,
}
