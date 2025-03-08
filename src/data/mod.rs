use std::fmt;

mod lex;
mod parse;

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

    pub fn ty(&self) -> String {
        match self {
            Data::Unknown => "unknown".to_owned(),
            Data::Atom => "atom".to_owned(),
            Data::Sequence => "sequence".to_owned(),
            Data::Struct(_) => "structured".to_owned(),
            Data::Tabular => "tabular".to_owned(),
        }
    }

    pub fn fmt(&self, w: &mut impl fmt::Write, opts: &FmtOptions) -> fmt::Result {
        match self {
            Data::Struct(node) => node.fmt(w, opts),
            _ => write!(w, "Data"),
        }
    }
}

impl fmt::Display for Data {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Data::Struct(node) => node.fmt(f, &FmtOptions::default()),
            _ => write!(f, "Data"),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct FmtOptions {
    pub depth: Option<usize>,
}
