//! Convert the very simple, nearly always error-free initial parsing into something more useful.

use crate::data::{
    self,
    lex::{Token, TokenKind},
    parse::{Node as PNode, NodeKind},
};

#[derive(Debug, Clone, PartialEq, Default)]
pub enum Node {
    #[default]
    Todo,
    Error(String),
    None,
    // Nodes in the list, delimiter, seperator.
    List(Vec<Node>, Option<char>, Option<char>),
    Group(Vec<Node>),
    Pair(Box<Node>, Box<Node>, char),
    Atom(usize),
}

impl Node {
    pub fn count(&self) -> usize {
        match self {
            Node::Todo => 1,
            Node::Error(_) => 0,
            Node::None => 0,
            Node::List(nodes, _, _) => nodes.len(),
            Node::Group(_) => 1,
            Node::Pair(..) => 2,
            Node::Atom(_) => 1,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]

pub enum Hint {
    None,
    StructSeq,
    SingleStruct,
    Seq,
}

pub fn require_reparsed(data: &data::Data, depth: Option<usize>, runtime: &crate::Runtime) {
    match data {
        data::Data::Unknown | data::Data::Atom => {}
        data::Data::Struct(node, r) => {
            let mut metas = runtime.metadata.borrow_mut();
            let metadata = metas.get_mut(r).unwrap();
            match (metadata.reparse_depth, depth) {
                (None, _) => return,
                (Some(md), Some(d)) if md >= d => return,
                _ => {}
            }

            metadata.reparsed = reparse(node, Hint::StructSeq, depth);
            metadata.reparse_depth = depth;
        }
        data::Data::Sequence => unimplemented!(),
        data::Data::Tabular => unimplemented!(),
    }
}

pub fn reparse(input: &PNode, hint: Hint, depth: Option<usize>) -> Node {
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

            if let Some(c) = tok_delimiter(nodes.first().unwrap())
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
                if let Some(c) = tok_delimiter(n)
                    && let Some(opener) = open_delim
                    && data::delimiters_match(opener, c)
                {
                    break;
                }
                if let Some(s) = tok_symbol(n) {
                    if data::SEPERATORS.contains(&s) {
                        let c = s.chars().next().unwrap();
                        match sep {
                            Some(cc) => {
                                if c == cc {
                                    finish_child!();
                                } else {
                                    buf.push(Node::Atom(skipped + i));
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
                    NodeKind::Tok(_) => buf.push(Node::Atom(i + skipped)),
                    NodeKind::Seq(_) => {
                        let child = reparse(n, Hint::Seq, depth.map(|d| d - 1));
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
                    Hint::Seq | Hint::StructSeq => Node::List(children, open_delim, sep),
                    _ => children.pop().unwrap(),
                };
            }

            Node::List(children, open_delim, sep)
        }
        NodeKind::Trivia(_) => Node::None,
        NodeKind::Tok(_) => Node::Atom(0),
    }
}

fn tok_delimiter(n: &PNode) -> Option<char> {
    match &n.kind {
        NodeKind::Tok(Token {
            kind: TokenKind::Delimiter(c),
            ..
        }) => Some(*c),
        _ => None,
    }
}
fn tok_symbol(n: &PNode) -> Option<&str> {
    match &n.kind {
        NodeKind::Tok(Token {
            kind: TokenKind::Symbol(s),
            ..
        }) => Some(s),
        _ => None,
    }
}

#[cfg(test)]
mod test {
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
        let parsed = crate::data::parse(text, 0, &crate::Runtime::new_test()).unwrap();
        eprintln!("{parsed:?}\n\n");
        let p_node = parsed.unwrap_structural();
        let reparsed = reparse(&p_node, Hint::StructSeq, None);
        eprintln!("{reparsed:?}");
        match reparsed {
            Node::List(nodes, delim, sep) => {
                assert_eq!(nodes.len(), 2);
                assert!(delim.is_none());
                assert!(sep.is_none());

                let g1 = unwrap_group(&nodes[0]);
                assert_eq!(g1.len(), 2);
                assert_eq!(&g1[0], &Node::Atom(0));
                match &g1[1] {
                    Node::List(nodes, Some('{'), Some(',')) => {
                        assert_eq!(nodes.len(), 3, "{nodes:?}");
                        let (a, b) = unwrap_pair(&nodes[0], ':');
                        assert_eq!(a, &Node::Atom(2));
                        assert_eq!(b, &Node::Atom(4));
                        let (a, b) = unwrap_pair(&nodes[1], ':');
                        assert_eq!(a, &Node::Atom(7));
                        let b = unwrap_group(b);
                        assert_eq!(b.len(), 2, "{b:?}");
                        assert_eq!(&b[0], &Node::Atom(9));
                        match &b[1] {
                            Node::List(nodes, Some('('), Some(',')) => {
                                assert_eq!(nodes.len(), 2, "{nodes:?}");
                            }
                            _ => unreachable!(),
                        }
                        let (a, b) = unwrap_pair(&nodes[2], ':');
                        assert_eq!(a, &Node::Atom(13));
                        assert_eq!(b, &Node::Atom(15));
                    }
                    _ => unreachable!(),
                }

                let g2 = unwrap_group(&nodes[1]);
                assert_eq!(g2.len(), 2);
                assert_eq!(&g2[0], &Node::Atom(3));
                match &g2[1] {
                    Node::List(nodes, Some('{'), Some(',')) => {
                        assert_eq!(nodes.len(), 3, "{nodes:?}");
                        let (a, b) = unwrap_pair(&nodes[0], ':');
                        assert_eq!(a, &Node::Atom(2));
                        assert_eq!(b, &Node::Atom(4));
                        let (a, b) = unwrap_pair(&nodes[1], ':');
                        assert_eq!(a, &Node::Atom(7));
                        let b = unwrap_group(b);
                        assert_eq!(b.len(), 2, "{b:?}");
                        assert_eq!(&b[0], &Node::Atom(9));
                        match &b[1] {
                            Node::List(nodes, Some('('), Some(',')) => {
                                assert_eq!(nodes.len(), 1, "{nodes:?}");
                            }
                            _ => unreachable!(),
                        }
                        let (a, b) = unwrap_pair(&nodes[2], ':');
                        assert_eq!(a, &Node::Atom(13));
                        assert_eq!(b, &Node::Atom(15));
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
        let parsed = crate::data::parse(text, 0, &crate::Runtime::new_test()).unwrap();
        eprintln!("{parsed:?}\n\n");
        let p_node = parsed.unwrap_structural();
        let reparsed = reparse(&p_node, Hint::StructSeq, Some(0));
        eprintln!("{reparsed:?}");
        assert_eq!(reparsed, Node::Todo);

        let reparsed = reparse(&p_node, Hint::StructSeq, Some(1));
        eprintln!("{reparsed:?}");
        match reparsed {
            Node::List(nodes, delim, sep) => {
                assert_eq!(nodes.len(), 2);
                assert!(delim.is_none());
                assert!(sep.is_none());

                let g1 = unwrap_group(&nodes[0]);
                assert_eq!(g1.len(), 2);
                assert_eq!(&g1[0], &Node::Atom(0));
                assert_eq!(&g1[1], &Node::Todo);

                let g2 = unwrap_group(&nodes[1]);
                assert_eq!(g2.len(), 2);
                assert_eq!(&g2[0], &Node::Atom(3));
                assert_eq!(&g2[1], &Node::Todo);
            }
            _ => unreachable!(),
        }

        let reparsed = reparse(&p_node, Hint::StructSeq, Some(2));
        eprintln!("{reparsed:?}");
        match reparsed {
            Node::List(nodes, delim, sep) => {
                assert_eq!(nodes.len(), 2);
                assert!(delim.is_none());
                assert!(sep.is_none());

                let g1 = unwrap_group(&nodes[0]);
                assert_eq!(g1.len(), 2);
                assert_eq!(&g1[0], &Node::Atom(0));
                assert!(matches!(&g1[1], &Node::List(..)));

                let g2 = unwrap_group(&nodes[1]);
                assert_eq!(g2.len(), 2);
                assert_eq!(&g2[0], &Node::Atom(3));
                assert!(matches!(&g2[1], &Node::List(..)));
            }
            _ => unreachable!(),
        }
    }
}
