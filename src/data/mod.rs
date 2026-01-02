use std::fmt as sfmt;

pub use fmt::FmtOptions;

pub use crate::data::lex::Token;
use crate::lang::ExecContext;

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

pub fn parse_tabular(input: &str, row_sep: char, col_sep: (Vec<char>, usize)) -> TabularMetaData {
    // TODO splitting columns by whitespace
    let mut data: Vec<Vec<_>> = input
        .split(row_sep)
        .map(|r| r.split(&*col_sep.0).map(|s| s.trim().to_owned()).collect())
        .collect();

    // Ensure all rows have the same length.
    if let Some(max_len) = data.iter().map(Vec::len).max() {
        data.iter_mut()
            .for_each(|r| r.extend((r.len()..max_len).map(|_| String::new())));
    }

    TabularMetaData {
        row_sep,
        col_sep,
        data,
    }
}

pub fn parse_structural(text: &str) -> Result<Option<StructMetaData>, Vec<crate::Error>> {
    let tokens = lex::Lexer::new(text.char_indices());
    let eof = lex::Token {
        kind: lex::TokenKind::Eof,
        start: text.len(),
    };
    parse_tokens_as_structural(tokens.chain(Some(eof)))
}

pub fn parse_tokens_as_structural(
    tokens: impl Iterator<Item = Token>,
) -> Result<Option<StructMetaData>, Vec<crate::Error>> {
    let mut parser = parse::Parser::new(tokens);
    let ast = parser.seq_struct();
    if parser.errors.is_empty() {
        Ok(ast.map(|ast| StructMetaData::new(parser.tokens, ast)))
    } else {
        Err(parser.errors)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Data {
    pub raw: Option<String>,
    pub meta: usize,
}

impl Data {
    pub fn new(raw: Option<String>, runtime: &crate::Runtime) -> Self {
        Data {
            raw,
            meta: runtime.init_meta_data(),
        }
    }

    pub fn ty(&self, runtime: &crate::Runtime) -> String {
        runtime.with_meta_data(self.meta, |metadata| metadata.ty())
    }

    pub fn fmt(
        &self,
        w: &mut impl sfmt::Write,
        opts: &FmtOptions,
        runtime: &crate::Runtime,
    ) -> sfmt::Result {
        runtime.with_meta_data(self.meta, |metadata| metadata.fmt(w, opts))
    }

    pub fn with_structural<T>(
        &self,
        runtime: &crate::Runtime,
        f: impl Fn(&StructMetaData) -> T,
    ) -> Option<T> {
        runtime.with_meta_data(self.meta, |metadata| match metadata {
            MetaData::Struct(smd) => Some(f(smd)),
            _ => None,
        })
    }

    pub fn with_tabular<T>(
        &self,
        runtime: &crate::Runtime,
        f: impl FnOnce(&mut TabularMetaData) -> T,
    ) -> Option<T> {
        runtime.with_meta_data(self.meta, |metadata| match metadata {
            MetaData::Tabular(tmd) => Some(f(tmd)),
            _ => None,
        })
    }

    pub fn resolve_structural(&self, runtime: &crate::Runtime) {
        if self.raw.is_none() {
            return;
        }
        runtime.with_meta_data(self.meta, |metadata| {
            if let MetaData::None = metadata {
                if let Ok(Some(smd)) = parse_structural(self.raw.as_ref().unwrap()) {
                    *metadata = MetaData::Struct(smd);
                }
            }
        })
    }

    pub fn resolve_structural_from_tokens(
        &self,
        tokens: impl Iterator<Item = Token>,
        runtime: &crate::Runtime,
    ) {
        runtime.with_meta_data(self.meta, |metadata| {
            if let MetaData::None = metadata {
                // TODO return the error rather than ignoring it
                if let Ok(Some(smd)) = parse_tokens_as_structural(tokens) {
                    *metadata = MetaData::Struct(smd);
                }
            }
        })
    }

    pub fn force_tabular(&self, row_sep: char, col_sep: (Vec<char>, usize), ctxt: &ExecContext) {
        if self.raw.is_none() {
            return;
        }
        ctxt.runtime.with_meta_data(self.meta, move |metadata| {
            if !matches!(metadata, MetaData::Tabular(_)) {
                *metadata =
                    MetaData::Tabular(parse_tabular(self.raw.as_ref().unwrap(), row_sep, col_sep));
            }
        })
    }
}

#[derive(Clone, Debug)]
pub enum MetaData {
    None,
    Struct(StructMetaData),
    Tabular(TabularMetaData),
    Atom,
    Sequence,
}

impl MetaData {
    pub fn ty(&self) -> String {
        match self {
            MetaData::Atom => "atom".to_owned(),
            MetaData::Sequence => "sequence".to_owned(),
            MetaData::Struct(..) => "structured".to_owned(),
            MetaData::Tabular(..) => "tabular".to_owned(),
            MetaData::None => "no data".to_owned(),
        }
    }

    // TODO formatting should use reparsed AST where available.
    pub fn fmt(&self, w: &mut impl sfmt::Write, opts: &FmtOptions) -> sfmt::Result {
        match self {
            MetaData::Struct(s) => s.parsed.fmt(w, opts, &s.tokens),
            MetaData::Tabular(t) => t.fmt(w, opts),
            MetaData::None => Ok(()),
            _ => write!(w, "Data"),
        }
    }

    pub fn eq_reloc(&self, other: &MetaData) -> bool {
        match (self, other) {
            (MetaData::Struct(s1), MetaData::Struct(s2)) => {
                s1.parsed.eq_reloc(&s2.parsed, &s1.tokens, &s2.tokens)
            }
            (MetaData::None, MetaData::None) => true,
            _ => false,
        }
    }
}

impl sfmt::Display for MetaData {
    fn fmt(&self, f: &mut sfmt::Formatter<'_>) -> sfmt::Result {
        self.fmt(f, &FmtOptions::default())
    }
}

#[derive(Clone, Debug)]
pub struct StructMetaData {
    tokens: Vec<Token>,
    parsed: parse::Node,
    reparsed: reparse::Node,
    reparse_depth: Option<usize>,
}

impl StructMetaData {
    fn new(tokens: Vec<Token>, parsed: parse::Node) -> Self {
        StructMetaData {
            tokens,
            parsed,
            reparsed: reparse::Node::Todo,
            reparse_depth: Some(0),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TabularMetaData {
    row_sep: char,
    col_sep: (Vec<char>, usize),
    /// Invariant: all rows must have the same length.
    data: Vec<Vec<String>>,
}

impl TabularMetaData {
    // TODO add option for row numbers
    fn fmt(&self, w: &mut impl sfmt::Write, opts: &FmtOptions) -> sfmt::Result {
        let widths = if opts.truncate.is_some() {
            Vec::new()
        } else {
            let mut result = Vec::new();
            for r in &self.data {
                for (i, c) in r.iter().enumerate() {
                    if i == result.len() {
                        result.push(0);
                    }
                    result[i] = std::cmp::max(result[i], c.len());
                }
            }
            result
        };
        let sep = format!(" {} ", self.col_sep.0[0]);
        for (i, row) in self.data.iter().enumerate() {
            w.write_char('\n')?;
            write!(w, "{i:4}")?;
            for (c, a) in row.iter().enumerate() {
                w.write_str(&sep)?;
                if let Some(width) = opts.truncate {
                    write_truncated(w, a, width)?;
                } else {
                    write!(w, "{a:0$}", widths[c])?;
                }
            }
        }
        Ok(())
    }

    pub fn transpose(&self) -> TabularMetaData {
        if self.data.is_empty() {
            return self.clone();
        }

        let col_len = self.data[0].len();
        let mut data = vec![Vec::new(); col_len];
        for (i, row) in data.iter_mut().enumerate() {
            for col in &self.data {
                row.push(col[i].clone());
            }
        }

        TabularMetaData {
            row_sep: self.row_sep,
            col_sep: self.col_sep.clone(),
            data,
        }
    }
}

fn write_truncated(w: &mut impl sfmt::Write, s: &str, len: usize) -> sfmt::Result {
    if s.chars().count() <= len {
        w.write_str(&s)?;
        (s.len()..len).for_each(|_| w.write_char(' ').unwrap());
        return Ok(());
    }

    s.chars()
        .take(len - 2)
        .for_each(|c| w.write_char(c).unwrap());
    w.write_str("..")
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_transpose() {
        // Empty
        let empty = TabularMetaData {
            row_sep: '\n',
            col_sep: (Vec::new(), 42),
            data: Vec::new(),
        };
        let transposed = empty.transpose();
        let twice = transposed.transpose();
        assert!(transposed.data.is_empty());
        assert_eq!(empty, twice);

        // Empty rows
        let empty_rows = TabularMetaData {
            row_sep: '\n',
            col_sep: (Vec::new(), 42),
            data: vec![Vec::new(); 3],
        };
        let transposed = empty_rows.transpose();
        let twice = transposed.transpose();
        assert!(transposed.data.is_empty());
        assert_eq!(empty, twice);

        // Non-empty
        let non_empty = TabularMetaData {
            row_sep: '\n',
            col_sep: (Vec::new(), 42),
            data: vec![
                vec![
                    "a1".to_owned(),
                    "b1".to_owned(),
                    "c1".to_owned(),
                    "d1".to_owned(),
                ],
                vec![
                    "a2".to_owned(),
                    "b2".to_owned(),
                    "c2".to_owned(),
                    "d2".to_owned(),
                ],
                vec![
                    "a3".to_owned(),
                    "b3".to_owned(),
                    "c3".to_owned(),
                    "d3".to_owned(),
                ],
            ],
        };
        let transposed = non_empty.transpose();
        let twice = transposed.transpose();
        assert_eq!(
            transposed.data,
            [
                ["a1".to_owned(), "a2".to_owned(), "a3".to_owned()],
                ["b1".to_owned(), "b2".to_owned(), "b3".to_owned()],
                ["c1".to_owned(), "c2".to_owned(), "c3".to_owned()],
                ["d1".to_owned(), "d2".to_owned(), "d3".to_owned()],
            ]
        );
        assert_eq!(non_empty, twice);
    }
}
