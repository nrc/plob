use crate::{
    Error,
    data::{
        self,
        lex::{Token, TokenKind},
    },
};

pub(super) struct Parser {
    pub(super) errors: Vec<Error>,
    // TODO we don't currently produce any errors, but when we do we'll need to convert from erors
    // on data to error in the lang.
    pub(super) tokens: Vec<Token>,
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

    fn next(&mut self) -> usize {
        let result = self.cur_tok;
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
            TokenKind::Delimiter(c @ '{')
            | TokenKind::Delimiter(c @ '(')
            | TokenKind::Delimiter(c @ '[') => {
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
            TokenKind::Word(_)
            | TokenKind::Symbol(_)
            | TokenKind::String(_)
            | TokenKind::Delimiter(_) => Node {
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
            if let NodeKind::Tok(i) = &node.kind
                && let Token {
                    kind: TokenKind::Delimiter(close),
                    ..
                } = &self.tokens[*i]
                && data::delimiters_match(delimiter, *close)
            {
                result.push(node);
                return;
            }
            result.push(node);
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Node {
    pub(super) kind: NodeKind,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(super) enum NodeKind {
    Tok(usize),
    Trivia(usize),
    Seq(Vec<Node>),
}

impl Node {
    pub(super) fn is_trivial(&self) -> bool {
        matches!(self.kind, NodeKind::Trivia(_))
    }

    pub fn count(&self) -> usize {
        match &self.kind {
            NodeKind::Tok(_) => 1,
            NodeKind::Trivia(_) => 0,
            NodeKind::Seq(nodes) => nodes.iter().map(Node::count).sum(),
        }
    }

    pub fn token(&self) -> Option<usize> {
        match &self.kind {
            NodeKind::Tok(t) | NodeKind::Trivia(t) => Some(*t),
            NodeKind::Seq(_) => None,
        }
    }

    pub fn expect_token_range(&self) -> (usize, usize) {
        match &self.kind {
            NodeKind::Tok(t) | NodeKind::Trivia(t) => (*t, *t),
            NodeKind::Seq(nodes) => (
                nodes[0].expect_token_range().0,
                nodes.last().unwrap().expect_token_range().1,
            ),
        }
    }

    pub fn eq_reloc(&self, other: &Node, toks_self: &[Token], toks_other: &[Token]) -> bool {
        self.kind.eq_reloc(&other.kind, toks_self, toks_other)
    }
}

impl NodeKind {
    pub fn eq_reloc(&self, other: &NodeKind, toks_self: &[Token], toks_other: &[Token]) -> bool {
        match (self, other) {
            (NodeKind::Tok(t1), NodeKind::Tok(t2))
            | (NodeKind::Trivia(t1), NodeKind::Trivia(t2)) => {
                toks_self[*t1].eq_reloc(&toks_other[*t2])
            }
            (NodeKind::Seq(ns1), NodeKind::Seq(ns2)) => {
                let mut iter1 = ns1.iter().filter(|n| !n.is_trivial());
                let mut iter2 = ns2.iter().filter(|n| !n.is_trivial());
                std::iter::zip(&mut iter1, &mut iter2)
                    .all(|(n1, n2)| n1.eq_reloc(n2, toks_self, toks_other))
                    && iter1.next().is_none()
                    && iter2.next().is_none()
            }
            _ => false,
        }
    }
}

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub struct NodePath(Vec<usize>);

// impl NodePath {
//     pub fn new() -> Self {
//         NodePath(Vec::new())
//     }

//     pub fn step(&self, next: usize) -> Self {
//         let mut p = self.0.clone();
//         p.push(next);
//         NodePath(p)
//     }

//     pub fn resolve<'a>(&self, node: &'a Node) -> Option<&'a Node> {
//         fn resolve<'a>(path: &[usize], node: &'a Node) -> Option<&'a Node> {
//             if path.is_empty() {
//                 return Some(node);
//             }

//             match &node.kind {
//                 NodeKind::Seq(nodes) if path[0] < nodes.len() => resolve(&path[1..], &nodes[path[0]]),
//                 _ => None,
//             }
//         }

//         resolve(&self.0, node)
//     }
// }

#[cfg(test)]
mod test {
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
        let result = crate::data::parse(text, 0, &crate::Runtime::new_test()).unwrap();
        eprintln!("{result}");
        result.unwrap_structural();
    }
}
