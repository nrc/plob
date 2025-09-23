use std::ops::Deref;

use crate::lang::{
    Token,
    lex::{self, Operator, TokenKind},
    make_err,
};

pub(super) fn parse_cmd_inner(text: &str, line: usize) -> (Command, Vec<crate::Error>) {
    let tokens = lex::Lexer::new(text.chars());
    let mut parser = CommandParser::new(tokens.chain(Some(Token {
        kind: TokenKind::Eof,
        char: text.chars().count(),
        len: 0,
    })));
    let result = parser.command();
    let tok = parser.next();
    if tok.kind != TokenKind::Eof {
        parser.errors.push(("Unexpected token".to_owned(), tok));
    }

    (
        Command {
            source: text.to_owned(),
            line,
            kind: result,
        },
        parser
            .errors
            .into_iter()
            .map(|(msg, tok)| make_err(msg, tok, line))
            .collect(),
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Node<T> {
    pub inner: T,
    pub location: NodeLoc,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct NodeLoc {
    pub char: usize,
    pub len: usize,
}

impl<T> Node<T> {
    pub fn new(inner: T, char: usize, len: usize) -> Self {
        Self {
            inner,
            location: NodeLoc { char, len },
        }
    }

    pub fn map<U>(self, f: impl Fn(T) -> U) -> Node<U> {
        Node {
            inner: f(self.inner),
            location: self.location,
        }
    }
}

impl NodeLoc {
    fn end(&self) -> usize {
        self.char + self.len
    }
}

impl<T> Deref for Node<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Clone, Debug)]
pub struct Command {
    pub(super) source: String,
    pub(super) kind: CmdKind,
    pub(super) line: usize,
}

impl Command {
    pub fn is_error(&self) -> bool {
        matches!(self.kind, CmdKind::Error(_))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum CmdKind {
    Assign(Option<Node<String>>, Node<Expr>),
    Echo(Node<Expr>),
    Error(Token),
}

impl From<Result<Node<Expr>, Token>> for CmdKind {
    fn from(e: Result<Node<Expr>, Token>) -> Self {
        match e {
            Ok(e) => CmdKind::Echo(e),
            Err(t) => CmdKind::Error(t),
        }
    }
}

impl From<Result<CmdKind, Token>> for CmdKind {
    fn from(c: Result<CmdKind, Token>) -> Self {
        match c {
            Ok(k) => k,
            Err(t) => CmdKind::Error(t),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Expr {
    Var(String),
    HistVar(usize),
    Int(i64),
    String(String),
    Blob(String),
    Action(Action),
    Pipe(Option<Box<Node<Expr>>>, Vec<Node<Action>>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Action {
    // Projection(Node<Selector>),
    Call(Node<String>, Vec<(Option<Node<String>>, Node<Expr>)>),
}

// #[derive(Clone, Debug, Eq, PartialEq)]
// pub(super) enum Selector {
//     Var(String),
//     Int(i64),
//     String(String),
//     Ident(String),
//     Seq(Vec<Selector>),
// }

pub(super) struct CommandParser {
    tokens: Vec<Token>,
    errors: Vec<(String, Token)>,
}

impl CommandParser {
    // tokens must be Eof-terminated
    pub fn new(tokens: impl Iterator<Item = Token>) -> CommandParser {
        let mut tokens: Vec<_> = tokens.collect();
        tokens.reverse();
        CommandParser {
            tokens,
            errors: Vec::new(),
        }
    }

    /// cmd ::= assign | expr
    pub fn command(&mut self) -> CmdKind {
        if matches!(self.peek(0).kind, TokenKind::Eof) {
            return CmdKind::Error(self.peek(0).clone());
        }

        if matches!(self.peek(0).kind, TokenKind::Operator(Operator::Equals))
            || matches!(self.peek(1).kind, TokenKind::Operator(Operator::Equals))
        {
            self.assign().into()
        } else {
            self.expr().into()
        }
    }

    fn next(&mut self) -> Token {
        let result = self.tokens.pop().unwrap();
        if result.kind == TokenKind::Eof {
            self.tokens.push(result.clone());
        }
        result
    }

    fn restore_tok(&mut self, t: Token) {
        self.tokens.push(t)
    }

    fn peek(&self, lookahead: usize) -> &Token {
        if 1 + lookahead > self.tokens.len() {}
        &self.tokens[self.tokens.len() - 1 - lookahead]
    }

    /// assign ::= var? `=` expr
    /// Precondition: `=` | _ `=`
    fn assign(&mut self) -> Result<CmdKind, Token> {
        let t = self.peek(0);
        let var = match &t.kind {
            TokenKind::Var(_) => {
                let tok = self.next();
                match tok.kind {
                    TokenKind::Var(name) => Some(Node::new(name, tok.char, tok.len)),
                    _ => unreachable!(),
                }
            }
            TokenKind::Operator(Operator::Equals) => None,
            _ => return Err(self.peek(0).clone()),
        };

        let t = self.next();
        match t.kind {
            TokenKind::Operator(Operator::Equals) => Ok(CmdKind::Assign(var, self.expr()?)),
            _ => unreachable!(),
        }
    }

    /// expr ::= var | hist_var | literal | pipe | pexpr
    fn expr(&mut self) -> Result<Node<Expr>, Token> {
        let t = self.peek(0);
        match &t.kind {
            TokenKind::Var(_) | TokenKind::Operator(Operator::Caret) => {
                let lhs = self.lexpr()?;
                if let TokenKind::Operator(Operator::RightArrow) = &self.peek(0).kind {
                    return self.pipe(Some(lhs));
                } else {
                    return Ok(lhs);
                }
            }
            TokenKind::Ident(_) => return self.pexpr().map(|a| a.map(|a| Expr::Action(a))),
            TokenKind::Operator(Operator::RightArrow) => {
                return self.pipe(None);
            }
            _ => {}
        }
        let t = self.next();
        match t.kind {
            TokenKind::Number(n) => Ok(Node::new(Expr::Int(n), t.char, t.len)),
            TokenKind::String(s) => Ok(Node::new(Expr::String(s), t.char, t.len)),
            TokenKind::Blob(s) => Ok(Node::new(Expr::Blob(s), t.char, t.len)),
            _ => {
                self.restore_tok(t.clone());
                Err(t)
            }
        }
    }

    /// lexpr ::= var | hist_var
    /// var ::= `$` ident
    fn lexpr(&mut self) -> Result<Node<Expr>, Token> {
        let t = self.next();
        match t.kind {
            TokenKind::Var(s) => Ok(Node::new(Expr::Var(s), t.char, t.len)),
            TokenKind::Operator(Operator::Caret) => self.hist_var(t),
            _ => {
                self.restore_tok(t.clone());
                Err(t)
            }
        }
    }

    /// hist_var ::= `^`+ | `^` int
    ///
    /// Precondition: `t` is `^`
    fn hist_var(&mut self, t: Token) -> Result<Node<Expr>, Token> {
        let mut offset = 1;
        let mut end = t.char + 1;
        while let TokenKind::Operator(Operator::Caret) = self.peek(0).kind {
            let t = self.next();
            end = t.char + 1;
            offset += 1;
        }
        if offset > 1 {
            return Ok(Node::new(Expr::HistVar(offset), t.char, end - t.char));
        }

        if let TokenKind::Number(_) = self.peek(0).kind {
            let num = self.next();
            match num.kind {
                TokenKind::Number(i) => {
                    if i <= 0 {
                        // TODO not unexpected error
                        return Err(num);
                    }
                    end = num.char + num.len;
                    return Ok(Node::new(Expr::HistVar(i as usize), t.char, end - t.char));
                }
                _ => unreachable!(),
            }
        }

        Ok(Node::new(Expr::HistVar(1), t.char, t.len))
    }

    /// pipe ::= lexpr? (`>` pexpr)+
    fn pipe(&mut self, lhs: Option<Node<Expr>>) -> Result<Node<Expr>, Token> {
        let mut start = None;
        if let Some(e) = &lhs {
            start = Some(e.location.char);
        }
        let mut actions = Vec::new();
        while let TokenKind::Operator(Operator::RightArrow) = &self.peek(0).kind {
            let arrow = self.next();
            if start.is_none() {
                start = Some(arrow.char);
            }
            actions.push(self.pexpr()?);
        }
        let end = actions.last().unwrap().location.end();
        Ok(Node::new(
            Expr::Pipe(lhs.map(|e| Box::new(e)), actions),
            start.unwrap(),
            end - start.unwrap(),
        ))
    }

    /// pexpr ::= call
    /// call ::= ident `(` (arg),* `)`
    fn pexpr(&mut self) -> Result<Node<Action>, Token> {
        let ident = self.ident()?;
        self.op(Operator::Bra)?;
        let mut args = Vec::new();
        loop {
            if let TokenKind::Operator(Operator::Ket) = &self.peek(0).kind {
                break;
            }
            args.push(self.arg()?);
            if &self.peek(0).kind == &TokenKind::Operator(Operator::Comma) {
                self.next();
            } else {
                break;
            }
        }
        let ket = self.op(Operator::Ket)?;

        let start = ident.location.char;
        let end = ket.location.char + 1;
        Ok(Node::new(Action::Call(ident, args), start, end - start))
    }

    /// arg ::= ident `=` expr | expr
    fn arg(&mut self) -> Result<(Option<Node<String>>, Node<Expr>), Token> {
        if let TokenKind::Ident(_) = self.peek(0).kind {
            let ident = self.ident()?;
            self.op(Operator::Equals)?;
            let expr = self.expr()?;
            return Ok((Some(ident), expr));
        }

        let expr = self.expr()?;
        Ok((None, expr))
    }

    fn ident(&mut self) -> Result<Node<String>, Token> {
        let t = self.next();
        match t.kind {
            TokenKind::Ident(s) => Ok(Node::new(s.clone(), t.char, t.len)),
            _ => {
                self.restore_tok(t.clone());
                Err(t)
            }
        }
    }

    fn op(&mut self, expected: Operator) -> Result<Node<Operator>, Token> {
        let t = self.next();
        match t.kind {
            TokenKind::Operator(op) if op == expected => Ok(Node::new(op.clone(), t.char, t.len)),
            _ => {
                self.restore_tok(t.clone());
                Err(t)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[track_caller]
    fn assert_assign(text: &str) -> (Option<String>, Expr) {
        let (cmd, errs) = crate::lang::parse_cmd(text, 0);
        assert!(errs.is_empty(), "{errs:#?}");
        match cmd.kind {
            CmdKind::Assign(n, e) => (n.map(|n| n.inner), e.inner),
            _ => unreachable!(),
        }
    }

    #[track_caller]
    fn assert_echo(text: &str) -> Expr {
        let (cmd, errs) = crate::lang::parse_cmd(text, 0);
        assert!(errs.is_empty(), "{errs:#?}");
        match cmd.kind {
            CmdKind::Echo(e) => e.inner,
            _ => unreachable!(),
        }
    }

    fn s(s: &str) -> std::string::String {
        s.to_owned()
    }

    #[test]
    fn parse_assign() {
        let (n, expr) = assert_assign("$foo = $bar");
        assert_eq!(n.unwrap(), "foo");
        assert_eq!(expr, Expr::Var(s("bar")));

        let (n, expr) = assert_assign(" = $bar");
        assert!(n.is_none());
        assert_eq!(expr, Expr::Var(s("bar")));
    }

    #[test]
    fn parse_echo() {
        let echoed = assert_echo("$foo");
        assert_eq!(echoed, Expr::Var(s("foo")));

        let echoed = assert_echo("^");
        assert_eq!(echoed, Expr::HistVar(1));
        let echoed = assert_echo("42");
        assert_eq!(echoed, Expr::Int(42));
    }

    #[test]
    fn parse_pipe() {
        let echoed = assert_echo("> foo()");
        // TODO

        let echoed = assert_echo("^ > foo()");
        let echoed = assert_echo("^^^^ > foo()");
        let echoed = assert_echo("^72 > foo()");

        let echoed = assert_echo("$bar > foo()");

        let echoed = assert_echo("$2 > foo() > bar()");
    }

    #[test]
    fn parse_call() {
        let echoed = assert_echo("foo()");
        // TODO
        let echoed = assert_echo("foo(x = $y, bar = qux())");
        let echoed = assert_echo("foo(x = $y,)");
    }
}
