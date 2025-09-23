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
            if matches!(&node.kind, NodeKind::Tok(Token { kind: TokenKind::Delimiter(close), ..}) if data::delimiters_match(delimiter, *close))
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
    Tok(Token),
    Trivia(Token),
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
}

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
