//! Convert the very simple, nearly always error-free initial parsing into something more useful.

use std::{
    cmp::{max, min},
    ops::RangeInclusive,
};

use crate::{
    Error,
    data::{
        self,
        lex::{Token, TokenKind},
        parse::{Node as PNode, NodeKind},
    },
};

#[derive(Debug, Clone, PartialEq, Default)]
pub enum Node {
    #[default]
    Todo,
    Error(String),
    None,
    List(List),
    Group(Vec<Node>),
    Pair(Box<Node>, Box<Node>, char),
    // Node, token
    Atom(usize, usize),
}

impl Node {
    pub fn count(&self) -> usize {
        match self {
            Node::Todo => 1,
            Node::Error(_) => 0,
            Node::None => 0,
            Node::List(l) => l.children.len(),
            Node::Group(..) => 1,
            Node::Pair(..) => 2,
            Node::Atom(..) => 1,
        }
    }

    // TODO should it use start_/end_token? Are there uses which should use those?
    pub fn token_range(&self) -> Option<RangeInclusive<usize>> {
        fn combine_opt_ranges(
            a: Option<RangeInclusive<usize>>,
            b: Option<RangeInclusive<usize>>,
        ) -> Option<RangeInclusive<usize>> {
            match (a, b) {
                (None, None) => None,
                (r, None) | (None, r) => r,
                (Some(a), Some(b)) => {
                    let a = a.into_inner();
                    let b = b.into_inner();
                    Some(min(a.0, b.0)..=max(a.1, b.1))
                }
            }
        }
        match self {
            Node::List(l) => Some(l.start_tok..=l.end_tok),
            Node::Group(ns) if ns.is_empty() => None,
            Node::Group(ns) => combine_opt_ranges(
                ns.first().unwrap().token_range(),
                ns.last().unwrap().token_range(),
            ),
            Node::Pair(n1, n2, _) => combine_opt_ranges(n1.token_range(), n2.token_range()),
            Node::Atom(_, t) => Some(*t..=*t),
            _ => None,
        }
    }

    pub fn tokens<'a>(&self, toks: &'a [Token]) -> &'a [Token] {
        match self.token_range() {
            Some(r) => &toks[r],
            None => &[],
        }
    }

    pub fn start_token(&self) -> Option<usize> {
        match self {
            Node::Todo | Node::Error(_) | Node::None => None,
            Node::List(l) => Some(l.start_tok),
            Node::Group(nodes) => nodes.first().and_then(Node::start_token),
            Node::Pair(n, ..) => n.start_token(),
            Node::Atom(_, t) => Some(*t),
        }
    }

    pub fn end_token(&self) -> Option<usize> {
        match self {
            Node::Todo | Node::Error(_) | Node::None => None,
            Node::List(l) => Some(l.end_tok),
            Node::Group(nodes) => nodes.last().and_then(Node::end_token),
            Node::Pair(_, n, _) => n.end_token(),
            Node::Atom(_, t) => Some(*t),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct List {
    pub children: Vec<Node>,
    pub delimiter: Option<char>,
    pub separator: Option<char>,
    pub start_tok: usize,
    pub end_tok: usize,
}

impl List {
    fn new(
        children: Vec<Node>,
        delimiter: Option<char>,
        separator: Option<char>,
        (start_tok, end_tok): (usize, usize),
    ) -> Self {
        List {
            children,
            delimiter,
            separator,
            start_tok,
            end_tok,
        }
    }

    // The front delimiter of the list.
    pub fn start_tok<'a>(&self, toks: &'a [Token]) -> Option<&'a Token> {
        self.delimiter?;
        Some(&toks[self.start_tok])
    }

    // The terminating delimiter of the list.
    pub fn end_tok<'a>(&self, toks: &'a [Token]) -> Option<&'a Token> {
        self.delimiter?;
        Some(&toks[self.end_tok])
    }

    // Includes following separator if present
    pub fn toks_for<'a>(&self, index: usize, toks: &'a [Token]) -> &'a [Token] {
        let Some(node_toks) = self.children[index].token_range() else {
            return &[];
        };

        let Some(next) = self.upper_bound(index) else {
            return &toks[node_toks];
        };

        &toks[*node_toks.start()..next]
    }

    // The upper bound token index of the `index`th node, if it is different to the last token of the
    // node itself
    pub fn upper_bound(&self, index: usize) -> Option<usize> {
        self.separator?;

        let next = if index == self.children.len() - 1 {
            self.end_tok
        } else {
            self.children[index + 1].start_token()?
        };

        Some(next)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]

pub enum Hint {
    None,
    StructSeq,
    SingleStruct,
    Seq,
}

pub fn with_reparsed<T>(
    data: &data::Data,
    depth: Option<usize>,
    runtime: &crate::Runtime,
    f: impl Fn(&Node, &[Token]) -> Result<T, Vec<Error>>,
) -> Result<T, Vec<Error>> {
    runtime.with_meta_data(data.meta, |metadata| {
        match metadata {
            // TODO create an error here, but how to make a data error without using lang stuff?
            data::MetaData::Tabular(_) => Err(vec![]),
            data::MetaData::Struct(smd) => {
                match (smd.reparse_depth, depth) {
                    (None, _) => {}
                    (Some(md), Some(d)) if md >= d => {}
                    _ => {
                        smd.reparsed = reparse(&smd.parsed, Hint::StructSeq, depth, &smd.tokens);
                        smd.reparse_depth = depth;
                    }
                }

                f(&smd.reparsed, &smd.tokens)
            }
            data::MetaData::None => f(&Node::None, &[]),
            data::MetaData::Atom => unimplemented!(),
            data::MetaData::Sequence => unimplemented!(),
        }
    })
}

fn reparse(input: &PNode, hint: Hint, depth: Option<usize>, toks: &[Token]) -> Node {
    if let Some(depth) = depth
        && depth == 0
    {
        return Node::Todo;
    }

    match &input.kind {
        NodeKind::Seq(nodes) => {
            // delimiters always start/end a seq. Seq is either top level or started and ended by a delimiter
            // e.g. `foo, bar, baz`  = seq of 5
            // `foo { a, b } bar { }` = seq of 4, 1 and 3 are seqs of len 5 and 2

            let mut nodes = &**nodes;
            let mut skipped = 0;
            loop {
                if nodes.is_empty() {
                    return Node::None;
                }
                if nodes[0].is_trivial() {
                    skipped += 1;
                    nodes = &nodes[1..];
                } else {
                    break;
                }
            }

            let mut open_delim = None;
            let mut sep = None;

            if let Some(c) = tok_delimiter(nodes.first().unwrap(), toks)
                && data::OPEN_DELIMS.contains(&c)
            {
                open_delim = Some(c);
                nodes = &nodes[1..];
                skipped += 1;
            }

            let mut children = Vec::new();
            let mut buf = Vec::new();
            let mut pair: Option<Node> = None;

            macro_rules! finish_child {
                () => {
                    #[allow(unused_assignments)]
                    if !buf.is_empty() {
                        match pair {
                            Some(Node::Pair(_, ref mut second, _)) => {
                                match buf.len() {
                                    0 => {}
                                    1 => *second = Box::new(buf.pop().unwrap()),
                                    _ => *second = Box::new(Node::Group(buf)),
                                }

                                children.push(pair.unwrap());
                                pair = None;
                            }
                            _ => match buf.len() {
                                0 => {}
                                1 => children.push(buf.pop().unwrap()),
                                _ => children.push(Node::Group(buf)),
                            },
                        }

                        buf = Vec::new();
                    }
                };
            }

            for (i, n) in nodes.iter().enumerate() {
                if n.is_trivial() {
                    continue;
                }
                if let Some(c) = tok_delimiter(n, toks)
                    && let Some(opener) = open_delim
                    && data::delimiters_match(opener, c)
                {
                    break;
                }
                if let Some(s) = tok_symbol(n, toks) {
                    if data::SEPERATORS.contains(&s) {
                        let c = s.chars().next().unwrap();
                        match sep {
                            Some(cc) => {
                                if c == cc {
                                    finish_child!();
                                } else {
                                    buf.push(Node::Atom(skipped + i, n.token().unwrap()));
                                }
                            }
                            None => {
                                sep = Some(c);
                                finish_child!();
                            }
                        }
                        continue;
                    }
                    if data::PAIR_SEPERATORS.contains(&s) {
                        let first = match buf.len() {
                            0 => Node::None,
                            1 => buf.pop().unwrap(),
                            _ => Node::Group(buf),
                        };
                        pair = Some(Node::Pair(
                            Box::new(first),
                            Box::new(Node::None),
                            s.chars().next().unwrap(),
                        ));
                        buf = Vec::new();
                        continue;
                    }
                }

                match &n.kind {
                    NodeKind::Tok(t) => buf.push(Node::Atom(i + skipped, *t)),
                    NodeKind::Seq(_) => {
                        let child = reparse(n, Hint::Seq, depth.map(|d| d - 1), toks);
                        buf.push(child);
                        if hint == Hint::StructSeq {
                            finish_child!();
                        }
                    }
                    NodeKind::Trivia(_) => unreachable!(),
                }
            }
            finish_child!();

            if children.is_empty() {
                return Node::None;
            }
            if children.len() == 1 {
                return match hint {
                    Hint::Seq | Hint::StructSeq => Node::List(List::new(
                        children,
                        open_delim,
                        sep,
                        input.expect_token_range(),
                    )),
                    _ => children.pop().unwrap(),
                };
            }

            Node::List(List::new(
                children,
                open_delim,
                sep,
                input.expect_token_range(),
            ))
        }
        NodeKind::Trivia(_) => Node::None,
        NodeKind::Tok(t) => Node::Atom(0, *t),
    }
}

fn tok_delimiter(n: &PNode, toks: &[Token]) -> Option<char> {
    match &n.kind {
        NodeKind::Tok(i) => match &toks[*i].kind {
            TokenKind::Delimiter(c) => Some(*c),
            _ => None,
        },
        _ => None,
    }
}
fn tok_symbol<'a>(n: &'a PNode, toks: &'a [Token]) -> Option<&'a str> {
    match &n.kind {
        NodeKind::Tok(i) => match &toks[*i].kind {
            TokenKind::Symbol(s) => Some(s),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod test {
    use std::assert_matches::assert_matches;

    use super::*;

    fn unwrap_group(n: &Node) -> &[Node] {
        match n {
            Node::Group(nodes) => nodes,
            _ => unreachable!(),
        }
    }

    fn unwrap_pair(n: &Node, sep: char) -> (&Node, &Node) {
        match n {
            Node::Pair(n1, n2, c) if *c == sep => (n1, n2),
            _ => unreachable!(),
        }
    }

    #[test]
    fn smoke_reparse() {
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
        let parsed = crate::data::parse_structural(text).unwrap().unwrap();
        eprintln!("{parsed:?}\n\n");
        let reparsed = reparse(&parsed.parsed, Hint::StructSeq, None, &parsed.tokens);
        eprintln!("{reparsed:?}");
        match reparsed {
            Node::List(l) => {
                assert_eq!(l.children.len(), 2);
                assert!(l.delimiter.is_none());
                assert!(l.separator.is_none());

                let g1 = unwrap_group(&l.children[0]);
                assert_eq!(g1.len(), 2);
                assert_matches!(&g1[0], &Node::Atom(0, _));
                match &g1[1] {
                    Node::List(l) => {
                        assert_eq!(l.delimiter, Some('{'));
                        assert_eq!(l.separator, Some(','));
                        assert_eq!(l.children.len(), 3, "{:?}", l.children);
                        let (a, b) = unwrap_pair(&l.children[0], ':');
                        assert_matches!(a, &Node::Atom(2, _));
                        assert_matches!(b, &Node::Atom(4, _));
                        let (a, b) = unwrap_pair(&l.children[1], ':');
                        assert_matches!(a, &Node::Atom(7, _));
                        let b = unwrap_group(b);
                        assert_eq!(b.len(), 2, "{b:?}");
                        assert_matches!(&b[0], &Node::Atom(9, _));
                        match &b[1] {
                            Node::List(l) => {
                                assert_eq!(l.delimiter, Some('('));
                                assert_eq!(l.separator, Some(','));
                                assert_eq!(l.children.len(), 2, "{:?}", l.children);
                            }
                            _ => unreachable!(),
                        }
                        let (a, b) = unwrap_pair(&l.children[2], ':');
                        assert_matches!(a, &Node::Atom(13, _));
                        assert_matches!(b, &Node::Atom(15, _));
                    }
                    _ => unreachable!(),
                }

                let g2 = unwrap_group(&l.children[1]);
                assert_eq!(g2.len(), 2);
                assert_matches!(&g2[0], &Node::Atom(3, _));
                match &g2[1] {
                    Node::List(l) => {
                        assert_eq!(l.delimiter, Some('{'));
                        assert_eq!(l.separator, Some(','));
                        assert_eq!(l.children.len(), 3, "{:?}", l.children);
                        let (a, b) = unwrap_pair(&l.children[0], ':');
                        assert_matches!(a, &Node::Atom(2, _));
                        assert_matches!(b, &Node::Atom(4, _));
                        let (a, b) = unwrap_pair(&l.children[1], ':');
                        assert_matches!(a, &Node::Atom(7, _));
                        let b = unwrap_group(b);
                        assert_eq!(b.len(), 2, "{b:?}");
                        assert_matches!(&b[0], &Node::Atom(9, _));
                        match &b[1] {
                            Node::List(l) => {
                                assert_eq!(l.delimiter, Some('('));
                                assert_eq!(l.separator, Some(','));
                                assert_eq!(l.children.len(), 1, "{:?}", l.children);
                            }
                            _ => unreachable!(),
                        }
                        let (a, b) = unwrap_pair(&l.children[2], ':');
                        assert_matches!(a, &Node::Atom(13, _));
                        assert_matches!(b, &Node::Atom(15, _));
                    }
                    _ => unreachable!(),
                }
            }
            n => panic!("Expected list, found {n:?}"),
        }
    }

    #[test]
    fn smoke_reparse_depth() {
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
        let parsed = crate::data::parse_structural(text).unwrap().unwrap();
        eprintln!("{parsed:?}\n\n");
        let reparsed = reparse(&parsed.parsed, Hint::StructSeq, Some(0), &parsed.tokens);
        eprintln!("{reparsed:?}");
        assert_eq!(reparsed, Node::Todo);

        let reparsed = reparse(&parsed.parsed, Hint::StructSeq, Some(1), &parsed.tokens);
        eprintln!("{reparsed:?}");
        match reparsed {
            Node::List(l) => {
                assert_eq!(l.children.len(), 2);
                assert!(l.delimiter.is_none());
                assert!(l.separator.is_none());

                let g1 = unwrap_group(&l.children[0]);
                assert_eq!(g1.len(), 2);
                assert_matches!(&g1[0], &Node::Atom(0, _));
                assert_eq!(&g1[1], &Node::Todo);

                let g2 = unwrap_group(&l.children[1]);
                assert_eq!(g2.len(), 2);
                assert_matches!(&g2[0], &Node::Atom(3, _));
                assert_eq!(&g2[1], &Node::Todo);
            }
            _ => unreachable!(),
        }

        let reparsed = reparse(&parsed.parsed, Hint::StructSeq, Some(2), &parsed.tokens);
        eprintln!("{reparsed:?}");
        match reparsed {
            Node::List(l) => {
                assert_eq!(l.children.len(), 2);
                assert!(l.delimiter.is_none());
                assert!(l.separator.is_none());

                let g1 = unwrap_group(&l.children[0]);
                assert_eq!(g1.len(), 2);
                assert_matches!(&g1[0], &Node::Atom(0, _));
                assert!(matches!(&g1[1], &Node::List(..)));

                let g2 = unwrap_group(&l.children[1]);
                assert_eq!(g2.len(), 2);
                assert_matches!(&g2[0], &Node::Atom(3, _));
                assert!(matches!(&g2[1], &Node::List(..)));
            }
            _ => unreachable!(),
        }
    }
}
