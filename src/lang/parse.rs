use std::{fmt, ops::Deref};

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
    #[allow(dead_code)]
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
    // < 0 means most recent commands, i.e., multiple carets
    // We might want to support `^-n`, the implementation is already there, we just check and error
    // at the moment.
    HistVar(isize),
    Reapply(Node<isize>, NamedArgList),
    Int(i64),
    String(String),
    Blob(String),
    Action(Action),
    Pipe(Option<Box<Node<Expr>>>, Vec<Node<Action>>),
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var(s) => write!(f, "${s}"),
            Expr::HistVar(i) if *i < 0 => write!(f, "{}", "^".repeat(-i as usize)),
            Expr::HistVar(i) => write!(f, "^{i}"),
            Expr::Int(i) => write!(f, "{i}"),
            Expr::String(s) if s.len() < 40 => write!(f, "{s}"),
            Expr::String(s) => {
                let c = s.chars().next().unwrap();
                write!(f, "{c}...{c}")
            }
            Expr::Blob(_) => write!(f, "`...`"),
            Expr::Reapply(..) => write!(f, "<reapply>"),
            Expr::Action(_) => write!(f, "<action>"),
            Expr::Pipe(..) => write!(f, "<pipe>"),
        }
    }
}

type ArgList = Vec<(Option<Node<String>>, Node<Expr>)>;
type NamedArgList = Vec<(Node<String>, Node<Expr>)>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Action {
    Projection(Option<Box<Node<Expr>>>, Node<Selector>),
    Selection(Option<Box<Node<Expr>>>, Vec<Node<RangeSelector>>),
    Call(Node<String>, ArgList),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Selector {
    Single(SingleSelector),
    All,
    Seq(Vec<Node<SingleSelector>>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum RangeSelector {
    Single(SingleSelector),
    Range(Option<Node<SingleSelector>>, Option<Node<SingleSelector>>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SingleSelector {
    Int(i64),
    String(String),
    Ident(String),
}

impl Selector {
    #[allow(unused)]
    pub fn int(n: i64) -> Self {
        Selector::Single(SingleSelector::Int(n))
    }

    #[allow(unused)]
    pub fn ident(s: String) -> Self {
        Selector::Single(SingleSelector::Ident(s))
    }

    #[allow(unused)]
    pub fn string(s: String) -> Self {
        Selector::Single(SingleSelector::String(s))
    }

    pub fn numeric(&self) -> Option<Vec<i64>> {
        match self {
            Selector::Single(SingleSelector::Int(i)) => Some(vec![*i]),
            Selector::Seq(ns) => ns
                .iter()
                .map(|n| match n.inner {
                    SingleSelector::Int(i) => Some(i),
                    _ => None,
                })
                .collect(),
            _ => None,
        }
    }

    pub fn matches(
        &self,
        node: &crate::data::reparse::Node,
        index: usize,
        list_len: usize,
        toks: &[crate::data::Token],
    ) -> bool {
        match self {
            Selector::Single(s) => s.matches(node, index, list_len, toks),
            Selector::All => true,
            Selector::Seq(s) => s
                .iter()
                .any(|s| s.inner.matches(node, index, list_len, toks)),
        }
    }
}

impl SingleSelector {
    pub fn matches(
        &self,
        node: &crate::data::reparse::Node,
        index: usize,
        list_len: usize,
        toks: &[crate::data::Token],
    ) -> bool {
        match self {
            SingleSelector::Int(n) => {
                let i = if *n < 0 {
                    list_len - (-n as usize)
                } else {
                    *n as usize
                };
                index == i
            }
            SingleSelector::String(s) | SingleSelector::Ident(s) => match node {
                crate::data::reparse::Node::Todo => true,
                crate::data::reparse::Node::Error(_) => true,
                crate::data::reparse::Node::None => false,
                crate::data::reparse::Node::List(..) => false,
                crate::data::reparse::Node::Group(_) => false,
                crate::data::reparse::Node::Pair(k, ..) => {
                    self.matches(k, usize::MAX, list_len, toks)
                }
                crate::data::reparse::Node::Atom(_, t) => toks[*t].matches_str(s),
            },
        }
    }

    pub fn unwrap_int(&self) -> i64 {
        match self {
            SingleSelector::Int(i) => *i,
            _ => unreachable!(),
        }
    }
}

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

    /// expr ::= var | hist_var | reapply | literal | pipe | pexpr
    fn expr(&mut self) -> Result<Node<Expr>, Token> {
        let t = self.peek(0);
        match &t.kind {
            TokenKind::Var(_) | TokenKind::Operator(Operator::Caret) => {
                let is_hist_var = matches!(&t.kind, TokenKind::Operator(Operator::Caret));

                let lhs = self.lexpr()?;

                let peek = self.peek(0);

                if is_hist_var && let TokenKind::Operator(Operator::Bra) = &peek.kind {
                    return self.reapply(lhs);
                } else if let TokenKind::Operator(Operator::RightArrow) = &peek.kind {
                    return self.pipe(Some(lhs));
                } else if let TokenKind::Operator(Operator::Dot) = &peek.kind {
                    return Ok(self.projection(Some(lhs))?.map(Expr::Action));
                } else if let TokenKind::Operator(Operator::SquareBra) = &peek.kind {
                    return Ok(self.selection(Some(lhs))?.map(Expr::Action));
                } else {
                    return Ok(lhs);
                }
            }
            TokenKind::Ident(_) => return self.pexpr().map(|a| a.map(Expr::Action)),
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
            return Ok(Node::new(Expr::HistVar(-offset), t.char, end - t.char));
        }

        let var = if let TokenKind::Number(_) = self.peek(0).kind {
            let num = self.next();
            match num.kind {
                TokenKind::Number(i) => {
                    if i < 0 {
                        // TODO not unexpected error
                        return Err(num);
                    }
                    end = num.char + num.len;
                    Node::new(Expr::HistVar(i as isize), t.char, end - t.char)
                }
                _ => unreachable!(),
            }
        } else {
            Node::new(Expr::HistVar(-1), t.char, t.len)
        };

        Ok(var)
    }

    /// reapply ::= hist_var `(` (ident = expr),* `)`
    ///
    /// precondition: `(` && `lhs` is `hist_var`
    fn reapply(&mut self, lhs: Node<Expr>) -> Result<Node<Expr>, Token> {
        let lhs = lhs.map(|e| match e {
            Expr::HistVar(n) => n,
            _ => unreachable!(),
        });

        let bra = self.peek(0).clone();
        self.op(Operator::Bra).unwrap();
        let args = self.arg_list()?;
        let ket = self.op(Operator::Ket)?;

        let start = lhs.location.char;
        let len = ket.location.char + 1 - start;

        Ok(Node::new(
            Expr::Reapply(
                lhs,
                args.into_iter()
                    .map(|(a, e)| match a {
                        Some(a) => Ok((a, e)),
                        // TODO stupid token to error on
                        None => Err(bra.clone()),
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            start,
            len,
        ))
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
            Expr::Pipe(lhs.map(Box::new), actions),
            start.unwrap(),
            end - start.unwrap(),
        ))
    }

    /// pexpr ::= call | `.` selector | `[` range_selector_list `]`
    /// call ::= ident `(` (arg),* `)`
    fn pexpr(&mut self) -> Result<Node<Action>, Token> {
        if let TokenKind::Operator(Operator::Dot) = &self.peek(0).kind {
            return self.projection(None);
        }

        if let TokenKind::Operator(Operator::SquareBra) = &self.peek(0).kind {
            return self.selection(None);
        }

        let ident = self.ident()?;
        self.op(Operator::Bra)?;
        let args = self.arg_list()?;
        let ket = self.op(Operator::Ket)?;

        let start = ident.location.char;
        let end = ket.location.char + 1;
        Ok(Node::new(Action::Call(ident, args), start, end - start))
    }

    /// projection ::= lexpr? `.` selector
    fn projection(&mut self, lhs: Option<Node<Expr>>) -> Result<Node<Action>, Token> {
        let dot = self.op(Operator::Dot)?;
        let selector = self.selector()?;
        let len = selector.location.char - dot.location.char + selector.location.len;

        Ok(Node::new(
            Action::Projection(lhs.map(Box::new), selector),
            dot.location.char,
            len,
        ))
    }

    /// selection ::= lexpr? `[` (range_selector `,`)* `]`
    pub fn selection(&mut self, lhs: Option<Node<Expr>>) -> Result<Node<Action>, Token> {
        let square_bra = self.op(Operator::SquareBra)?;

        let mut selectors = Vec::new();
        loop {
            if let TokenKind::Operator(Operator::SquareKet) = &self.peek(0).kind {
                break;
            }
            selectors.push(self.range_selector()?);
            if self.peek(0).kind == TokenKind::Operator(Operator::Comma) {
                self.next();
            } else {
                break;
            }
        }

        let square_ket = self.op(Operator::SquareKet)?;
        let len = square_ket.location.char - square_bra.location.char + 1;

        Ok(Node::new(
            Action::Selection(lhs.map(Box::new), selectors),
            square_bra.location.char,
            len,
        ))
    }

    /// (arg),*
    fn arg_list(&mut self) -> Result<ArgList, Token> {
        let mut args = Vec::new();
        loop {
            if let TokenKind::Operator(Operator::Ket) = &self.peek(0).kind {
                break;
            }
            args.push(self.arg()?);
            if self.peek(0).kind == TokenKind::Operator(Operator::Comma) {
                self.next();
            } else {
                break;
            }
        }

        Ok(args)
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

    /// selector ::= single_selector | `*` | `(` single_selector,* `)`
    fn selector(&mut self) -> Result<Node<Selector>, Token> {
        if let TokenKind::Operator(Operator::Bra) = &self.peek(0).kind {
            let bra = self.next();
            let mut nested = Vec::new();
            loop {
                if let TokenKind::Operator(Operator::Ket) = &self.peek(0).kind {
                    break;
                }
                nested.push(self.single_selector()?);
                if self.peek(0).kind == TokenKind::Operator(Operator::Comma) {
                    self.next();
                } else {
                    break;
                }
            }
            let ket = self.op(Operator::Ket)?;
            return Ok(Node::new(
                Selector::Seq(nested),
                bra.char,
                ket.location.char - bra.char + 1,
            ));
        }

        if let TokenKind::Operator(Operator::Star) = &self.peek(0).kind {
            let t = self.next();
            return Ok(Node::new(Selector::All, t.char, t.len));
        }

        self.single_selector().map(|s| s.map(Selector::Single))
    }

    /// single_selector ::= int | ident | string
    fn single_selector(&mut self) -> Result<Node<SingleSelector>, Token> {
        let t = self.next();
        match t.kind {
            TokenKind::Number(n) => Ok(Node::new(SingleSelector::Int(n), t.char, t.len)),
            TokenKind::Ident(s) => Ok(Node::new(SingleSelector::Ident(s), t.char, t.len)),
            TokenKind::String(s) => Ok(Node::new(SingleSelector::String(s), t.char, t.len)),
            _ => {
                self.restore_tok(t.clone());
                Err(t)
            }
        }
    }

    /// range_selector ::= single_selector | single_selector? `..` single_selector?
    fn range_selector(&mut self) -> Result<Node<RangeSelector>, Token> {
        let start_tok = self.peek(0).clone();

        // Try to parse the first single_selector
        let first = self.single_selector().ok();

        // Check if we have `..` (two consecutive dots)
        if matches!(self.peek(0).kind, TokenKind::Operator(Operator::Dot))
            && matches!(self.peek(1).kind, TokenKind::Operator(Operator::Dot))
        {
            // Consume both dots
            self.next();
            let second_dot = self.next();

            // Try to parse the second single_selector (optional)
            let second = self.single_selector().ok();

            let end_char = second
                .as_ref()
                .map(|s| s.location.end())
                .unwrap_or_else(|| second_dot.char + 1);

            return Ok(Node::new(
                RangeSelector::Range(first, second),
                start_tok.char,
                end_char - start_tok.char,
            ));
        }

        // If we have a first selector but no `..`, return it as Single
        if let Some(first) = first {
            let len = first.location.len;
            return Ok(Node::new(
                RangeSelector::Single(first.inner),
                first.location.char,
                len,
            ));
        }

        // No first selector and no `..`, so this is an error
        Err(start_tok)
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
            TokenKind::Operator(op) if op == expected => Ok(Node::new(op, t.char, t.len)),
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
        assert_eq!(echoed, Expr::HistVar(-1));
        let echoed = assert_echo("42");
        assert_eq!(echoed, Expr::Int(42));
    }

    #[test]
    fn parse_pipe() {
        let _echoed = assert_echo("> foo()");
        // TODO

        let _echoed = assert_echo("^ > foo()");
        let _echoed = assert_echo("^^^^ > foo()");
        let _echoed = assert_echo("^72 > foo()");

        let _echoed = assert_echo("$bar > foo()");

        let _echoed = assert_echo("$2 > foo() > bar()");
    }

    #[test]
    fn parse_call() {
        let _echoed = assert_echo("foo()");
        // TODO
        let _echoed = assert_echo("foo(x = $y, bar = qux())");
        let _echoed = assert_echo("foo(x = $y,)");
    }

    #[track_caller]
    fn parse_range_selector(text: &str) -> RangeSelector {
        let tokens = lex::Lexer::new(text.chars());
        let mut parser = CommandParser::new(tokens.chain(Some(Token {
            kind: TokenKind::Eof,
            char: text.chars().count(),
            len: 0,
        })));
        let result = parser.range_selector();
        assert!(result.is_ok(), "Failed to parse range selector: {text}");
        result.unwrap().inner
    }

    #[test]
    fn parse_range_selector_single() {
        // Single int selector
        let rs = parse_range_selector("42");
        assert!(matches!(rs, RangeSelector::Single(SingleSelector::Int(42))));

        // Single ident selector
        let rs = parse_range_selector("foo");
        assert!(matches!(rs, RangeSelector::Single(SingleSelector::Ident(ref s)) if s == "foo"));

        // Single string selector
        let rs = parse_range_selector("\"bar\"");
        assert!(matches!(rs, RangeSelector::Single(SingleSelector::String(ref s)) if s == "bar"));
    }

    #[test]
    fn parse_range_selector_range() {
        // Range with both bounds
        let rs = parse_range_selector("1..5");
        match rs {
            RangeSelector::Range(Some(start), Some(end)) => {
                assert!(matches!(start.inner, SingleSelector::Int(1)));
                assert!(matches!(end.inner, SingleSelector::Int(5)));
            }
            _ => panic!("Expected Range with both bounds"),
        }

        // Range with start only
        let rs = parse_range_selector("10..");
        match rs {
            RangeSelector::Range(Some(start), None) => {
                assert!(matches!(start.inner, SingleSelector::Int(10)));
            }
            _ => panic!("Expected Range with start only"),
        }

        // Range with end only
        let rs = parse_range_selector("..20");
        match rs {
            RangeSelector::Range(None, Some(end)) => {
                assert!(matches!(end.inner, SingleSelector::Int(20)));
            }
            _ => panic!("Expected Range with end only"),
        }

        // Full range
        let rs = parse_range_selector("..");
        assert!(matches!(rs, RangeSelector::Range(None, None)));

        // Range with identifiers
        let rs = parse_range_selector("foo..bar");
        match rs {
            RangeSelector::Range(Some(start), Some(end)) => {
                assert!(matches!(start.inner, SingleSelector::Ident(ref s) if s == "foo"));
                assert!(matches!(end.inner, SingleSelector::Ident(ref s) if s == "bar"));
            }
            _ => panic!("Expected Range with both ident bounds"),
        }
    }

    #[track_caller]
    fn assert_selection(text: &str) -> Vec<Node<RangeSelector>> {
        let echoed = assert_echo(text);
        match echoed {
            // Pipe with selection
            Expr::Pipe(None, mut actions) if actions.len() == 1 => {
                match actions.pop().unwrap().inner {
                    Action::Selection(None, selectors) => selectors,
                    _ => panic!("Expected Action::Selection in pipe"),
                }
            }
            // Direct selection with lhs
            Expr::Action(Action::Selection(_, selectors)) => selectors,
            _ => panic!("Expected selection expression, got: {echoed:?}"),
        }
    }

    #[test]
    fn parse_selection() {
        // Single range selector
        let selectors = assert_selection("> [1..5]");
        assert_eq!(selectors.len(), 1);
        match &selectors[0].inner {
            RangeSelector::Range(Some(start), Some(end)) => {
                assert!(matches!(start.inner, SingleSelector::Int(1)));
                assert!(matches!(end.inner, SingleSelector::Int(5)));
            }
            _ => panic!("Expected Range with both bounds"),
        }

        // Multiple range selectors
        let selectors = assert_selection("> [1..3, 5..7]");
        assert_eq!(selectors.len(), 2);
        match &selectors[0].inner {
            RangeSelector::Range(Some(start), Some(end)) => {
                assert!(matches!(start.inner, SingleSelector::Int(1)));
                assert!(matches!(end.inner, SingleSelector::Int(3)));
            }
            _ => panic!("Expected Range 1..3"),
        }
        match &selectors[1].inner {
            RangeSelector::Range(Some(start), Some(end)) => {
                assert!(matches!(start.inner, SingleSelector::Int(5)));
                assert!(matches!(end.inner, SingleSelector::Int(7)));
            }
            _ => panic!("Expected Range 5..7"),
        }

        // Range with start only
        let selectors = assert_selection("> [10..]");
        assert_eq!(selectors.len(), 1);
        match &selectors[0].inner {
            RangeSelector::Range(Some(start), None) => {
                assert!(matches!(start.inner, SingleSelector::Int(10)));
            }
            _ => panic!("Expected Range with start only"),
        }

        // Range with end only
        let selectors = assert_selection("> [..20]");
        assert_eq!(selectors.len(), 1);
        match &selectors[0].inner {
            RangeSelector::Range(None, Some(end)) => {
                assert!(matches!(end.inner, SingleSelector::Int(20)));
            }
            _ => panic!("Expected Range with end only"),
        }

        // Full range
        let selectors = assert_selection("> [..]");
        assert_eq!(selectors.len(), 1);
        assert!(matches!(
            &selectors[0].inner,
            RangeSelector::Range(None, None)
        ));

        // Empty selection
        let selectors = assert_selection("> []");
        assert_eq!(selectors.len(), 0);

        // Selection with lhs
        let selectors = assert_selection("$foo[1..3]");
        assert_eq!(selectors.len(), 1);

        // Single selector (not a range)
        let selectors = assert_selection("> [5]");
        assert_eq!(selectors.len(), 1);
        assert!(matches!(
            &selectors[0].inner,
            RangeSelector::Single(SingleSelector::Int(5))
        ));

        // Trailing comma
        let selectors = assert_selection("> [1..3,]");
        assert_eq!(selectors.len(), 1);

        // Mixed: single and range selectors
        let selectors = assert_selection("> [1, 3..5, 10..]");
        assert_eq!(selectors.len(), 3);
        assert!(matches!(
            &selectors[0].inner,
            RangeSelector::Single(SingleSelector::Int(1))
        ));
        match &selectors[1].inner {
            RangeSelector::Range(Some(start), Some(end)) => {
                assert!(matches!(start.inner, SingleSelector::Int(3)));
                assert!(matches!(end.inner, SingleSelector::Int(5)));
            }
            _ => panic!("Expected Range 3..5"),
        }
        match &selectors[2].inner {
            RangeSelector::Range(Some(start), None) => {
                assert!(matches!(start.inner, SingleSelector::Int(10)));
            }
            _ => panic!("Expected Range 10.."),
        }
    }
}
