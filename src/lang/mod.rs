pub use lex::Token;
pub use parse::Command;

pub fn parse_script(text: &str) -> (Vec<Command>, Vec<crate::Error>) {
    let iter = lex::ScriptSplitter::new(text.chars());
    let (cmds, errs): (Vec<_>, Vec<Vec<_>>) = iter
        .enumerate()
        .map(|(i, line)| parse::parse_cmd_inner(&line, i))
        .unzip();
    (cmds, errs.into_iter().flatten().collect())
}

// TODO `<<`
/// # Grammar
///
/// cmd ::= assign | expr
/// assign ::= var? `=` expr
/// expr ::= var | hist_var | literal | expr project | pipe | repipe | call
/// pipe ::= lexpr? (`>` pexpr)+
/// lexpr ::= var | hist_var | `(` expr `)`
/// pexpr ::= project | call | `where` pexpr
/// repipe ::= var? (`<` rexpr)+  // replay
/// rexpr ::= hist_var,+ | pexpr
/// project ::= `.` selector
/// selector ::= int | ident | var | string | `(` selector,* `)`
/// call ::= ident `(` (ident = expr),* `)`
/// var ::= `$` ident
/// hist_var ::= `^`+ | `^` int
/// literal ::= int | string | blob
pub fn parse_cmd(text: &str, line: usize) -> (Command, Vec<crate::Error>) {
    let mut iter = lex::ScriptSplitter::new(text.chars());
    let Some(text) = iter.next() else {
        return (
            Command {
                source: text.to_owned(),
                line,
                kind: parse::CmdKind::Error(Token {
                    kind: lex::TokenKind::Eof,
                    char: text.chars().count(),
                    len: 0,
                }),
            },
            Vec::new(),
        );
    };
    parse::parse_cmd_inner(&text, line)
}

fn make_err(msg: String, tok: Token, line: usize) -> crate::Error {
    crate::Error {
        msg: format!("ERROR: {msg}\n\n{}, {}: {:?}", line, tok.char, tok.kind,),
    }
}

#[derive(Debug, Clone)]
pub enum ExecResult {
    Echo(crate::Value),
    Variable(String),
    Error(Vec<crate::Error>),
}

pub fn run_cmd(cmd: Command, runtime: &mut crate::Runtime) -> ExecResult {
    let mut ctxt = exec::Context {
        runtime,
        source: cmd.source,
        src_line: cmd.line,
    };
    match cmd.kind {
        parse::CmdKind::Assign(name, expr) => {
            let value = match expr.exec(&mut ctxt) {
                Ok(v) => v,
                Err(e) => return ExecResult::Error(e),
            };
            let name = runtime.save_variable(name.map(|n| n.inner), value);
            runtime.report(&format!("${name}"));
            ExecResult::Variable(name)
        }
        parse::CmdKind::Echo(expr) => {
            let value = match expr.exec(&mut ctxt) {
                Ok(v) => v,
                Err(e) => return ExecResult::Error(e),
            };
            runtime.echo(&value);
            ExecResult::Echo(value)
        }
        parse::CmdKind::Error(_) => unreachable!(),
    }
}

mod exec {
    use crate::{
        Error, Value, ValueKind, data,
        lang::parse::{Action, Expr, Node, NodeLoc},
    };

    pub struct Context<'a> {
        pub runtime: &'a crate::Runtime,
        pub source: String,
        pub src_line: usize,
    }

    impl Context<'_> {
        fn make_err(&self, msg: &str, loc: NodeLoc) -> crate::Error {
            Error {
                msg: format!(
                    // TODO account for width of line number
                    "ERROR: {msg}\n\n{}: {}\n   {}",
                    self.src_line,
                    self.source,
                    loc.highlight()
                ),
            }
        }

        fn call(
            &mut self,
            fn_name: &str,
            lhs: Option<Value>,
            args: Vec<(Node<String>, Node<Expr>)>,
            loc: NodeLoc,
        ) -> Result<Value, Vec<Error>> {
            match fn_name {
                "fmt" => {
                    let Some(lhs) = lhs else {
                        return Err(vec![self.make_err(
                            "`fmt` requires data as input, but called with no input",
                            loc,
                        )]);
                    };
                    let data = match lhs.kind {
                        ValueKind::Data(d) => d,
                        k => {
                            return Err(vec![self.make_err(
                                &format!("`fmt` expected data as input, found: `{k}`"),
                                loc,
                            )]);
                        }
                    };

                    let mut opts = data::FmtOptions::default();
                    let mut errors = Vec::new();
                    for (name, expr) in args {
                        match &*name.inner {
                            "depth" => {
                                let loc = expr.location;
                                let val = expr.exec(self)?;
                                match val.kind {
                                    ValueKind::Number(n) => {
                                        if n < 0 {
                                            errors.push(self.make_err(
                                                &format!(
                                                    "depth argument to `fmt` must be a positive integer"
                                                ),
                                                loc,
                                            ));
                                            continue;
                                        }
                                        let n = n as usize;
                                        opts.depth = Some(n);
                                    }
                                    _ => {
                                        errors.push(self.make_err(
                                            &format!("depth argument to `fmt` must be an integer"),
                                            loc,
                                        ));
                                        continue;
                                    }
                                }
                            }
                            n => errors.push(self.make_err(
                                &format!("unexpected argument to `fmt`: `{n}`"),
                                name.location,
                            )),
                        }
                    }

                    if !errors.is_empty() {
                        return Err(errors);
                    }

                    let mut buf = String::new();
                    data.fmt(&mut buf, &opts).unwrap();
                    Ok(Value {
                        kind: ValueKind::String(buf),
                    })
                }
                "ty" => {
                    let Some(lhs) = lhs else {
                        return Err(vec![
                            self.make_err("`ty` requires input, but called with no input", loc),
                        ]);
                    };
                    if !args.is_empty() {
                        return Err(vec![self.make_err("`ty` expects no arguments", loc)]);
                    }
                    Ok(Value {
                        kind: ValueKind::String(lhs.kind.to_string()),
                    })
                }
                _ => {
                    Err(vec![self.make_err(
                        &format!("Unknown function name: `{fn_name}`"),
                        loc,
                    )])
                }
            }
        }
    }

    impl Node<Expr> {
        pub fn exec(self, ctxt: &mut Context) -> Result<Value, Vec<Error>> {
            match self.inner {
                Expr::Var(name) => ctxt
                    .runtime
                    .get_variable(&name)
                    .map(|v| v.clone())
                    .ok_or(vec![ctxt.make_err(
                        &format!("Unknown variable: `${name}`"),
                        self.location,
                    )]),
                Expr::HistVar(n) => ctxt.runtime.get_history(n).map(|v| v.clone()).ok_or(vec![
                    ctxt.make_err(&format!("Invalid historic value: `^{n}`"), self.location),
                ]),
                Expr::Int(n) => Ok(Value {
                    kind: ValueKind::Number(n),
                }),
                Expr::String(s) => Ok(Value {
                    kind: ValueKind::String(s),
                }),
                Expr::Blob(b) => {
                    let data = data::parse(&b)?;
                    Ok(Value {
                        kind: ValueKind::Data(data),
                    })
                }
                Expr::Pipe(lhs, actions) => {
                    let mut result = match lhs {
                        Some(expr) => expr.exec(ctxt)?,
                        None => ctxt
                            .runtime
                            .get_history(1)
                            .ok_or(vec![ctxt.make_err(
                                "Pipe with no lhs and no previous statement",
                                self.location,
                            )])?
                            .clone(),
                    };

                    for action in actions {
                        result = match action.inner {
                            Action::Call(name, args) => {
                                ctxt.call(&name.inner, Some(result), args, action.location)?
                            }
                        }
                    }

                    Ok(result)
                }
                Expr::Action(action) => match action {
                    Action::Call(name, args) => ctxt.call(&name.inner, None, args, self.location),
                },
            }
        }
    }
}

mod parse {
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
        pub fn highlight(&self) -> String {
            format!("{}{}", " ".repeat(self.char), "^".repeat(self.len))
        }

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
        Call(Node<String>, Vec<(Node<String>, Node<Expr>)>),
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
        /// call ::= ident `(` (ident `=` expr),* `)`
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

        /// arg ::= ident `=` expr
        fn arg(&mut self) -> Result<(Node<String>, Node<Expr>), Token> {
            let ident = self.ident()?;
            self.op(Operator::Equals)?;
            let expr = self.expr()?;
            Ok((ident, expr))
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
                TokenKind::Operator(op) if op == expected => {
                    Ok(Node::new(op.clone(), t.char, t.len))
                }
                _ => {
                    self.restore_tok(t.clone());
                    eprintln!("expected {expected:?}, found {:?}", t.kind);
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
}

mod lex {
    use std::mem;

    /// We have to do some very basic lexing to reliably split up the source text.
    pub(super) struct ScriptSplitter<'a> {
        chars: std::str::Chars<'a>,
        buf: String,
        state: SplitterState,
    }

    #[derive(Copy, Clone, Debug)]
    enum SplitterState {
        Src,
        // The slash is pending
        Slash,
        Comment,
        Str(char),
        // The backslash has been pushed
        EscapeStr(char),
        Blob,
        // A string within a blob
        BlobStr(char),
        BlobEscapeStr(char),
    }

    impl ScriptSplitter<'_> {
        pub fn new(chars: std::str::Chars) -> ScriptSplitter<'_> {
            ScriptSplitter {
                chars,
                buf: String::new(),
                state: SplitterState::Src,
            }
        }
    }

    impl Iterator for ScriptSplitter<'_> {
        type Item = String;

        fn next(&mut self) -> Option<String> {
            for c in &mut self.chars {
                match (c, self.state) {
                    ('/', SplitterState::Src) => self.state = SplitterState::Slash,
                    ('/', SplitterState::Slash) => {
                        self.state = SplitterState::Comment;
                        if !self.buf.is_empty() {
                            return Some(mem::take(&mut self.buf));
                        }
                    }

                    ('\\', SplitterState::Str(d)) => {
                        self.buf.push(c);
                        self.state = SplitterState::EscapeStr(d);
                    }
                    ('\\', SplitterState::BlobStr(d)) => {
                        self.buf.push(c);
                        self.state = SplitterState::BlobEscapeStr(d);
                    }

                    ('\n', SplitterState::Src) | (';', SplitterState::Src) => {
                        self.state = SplitterState::Src;
                        if !self.buf.is_empty() {
                            return Some(mem::take(&mut self.buf));
                        }
                    }
                    ('\n', SplitterState::Slash) | (';', SplitterState::Slash) => {
                        self.buf.push('/');
                        self.state = SplitterState::Src;
                        if !self.buf.is_empty() {
                            return Some(mem::take(&mut self.buf));
                        }
                    }
                    ('\n', SplitterState::Comment) => {
                        self.state = SplitterState::Src;
                    }

                    ('`', SplitterState::Src) => {
                        self.buf.push(c);
                        self.state = SplitterState::Blob;
                    }
                    ('`', SplitterState::Blob) => {
                        self.buf.push(c);
                        self.state = SplitterState::Src;
                    }

                    ('\'', SplitterState::Src) | ('"', SplitterState::Src) => {
                        self.buf.push(c);
                        self.state = SplitterState::Str(c);
                    }
                    ('\'', SplitterState::Slash) | ('"', SplitterState::Slash) => {
                        self.buf.push('/');
                        self.buf.push(c);
                        self.state = SplitterState::Str(c);
                    }
                    ('\'', SplitterState::Blob) | ('"', SplitterState::Blob) => {
                        self.buf.push(c);
                        self.state = SplitterState::BlobStr(c);
                    }
                    (d1, SplitterState::Str(d2)) if d1 == d2 => {
                        self.buf.push(c);
                        self.state = SplitterState::Src;
                    }
                    (d1, SplitterState::BlobStr(d2)) if d1 == d2 => {
                        self.buf.push(c);
                        self.state = SplitterState::Blob;
                    }

                    (_, SplitterState::Src)
                    | (_, SplitterState::Str(_))
                    | (_, SplitterState::Blob)
                    | (_, SplitterState::BlobStr(_)) => {
                        self.buf.push(c);
                    }
                    (_, SplitterState::Comment) => {}
                    (_, SplitterState::Slash) => {
                        self.buf.push('/');
                        self.buf.push(c);
                        self.state = SplitterState::Src;
                    }
                    (_, SplitterState::EscapeStr(d)) => {
                        self.buf.push(c);
                        self.state = SplitterState::Str(d);
                    }
                    (_, SplitterState::BlobEscapeStr(d)) => {
                        self.buf.push(c);
                        self.state = SplitterState::BlobStr(d);
                    }
                }
            }
            if self.buf.is_empty() {
                None
            } else {
                Some(mem::take(&mut self.buf))
            }
        }
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    pub struct Token {
        pub(super) kind: TokenKind,
        // Relative to the current line of the script.
        pub(super) char: usize,
        pub(super) len: usize,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub(super) enum TokenKind {
        // Without the preceeding `$`
        Var(String),
        Ident(String),
        Blob(String),
        Number(i64),
        // Unescaped and excluding delimiters.
        String(String),
        Operator(Operator),
        Unknown(char),
        Eof,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(super) enum Operator {
        Equals,
        Comma,
        Dot,
        Bra,
        Ket,
        LeftArrow,
        RightArrow,
        Caret,
    }

    impl TryFrom<char> for Operator {
        type Error = ();

        fn try_from(c: char) -> Result<Self, Self::Error> {
            match c {
                '=' => Ok(Operator::Equals),
                '.' => Ok(Operator::Dot),
                ',' => Ok(Operator::Comma),
                '(' => Ok(Operator::Bra),
                ')' => Ok(Operator::Ket),
                '<' => Ok(Operator::LeftArrow),
                '>' => Ok(Operator::RightArrow),
                '^' => Ok(Operator::Caret),
                _ => Err(()),
            }
        }
    }

    const OPS: [char; 8] = ['=', '.', ',', '(', ')', '<', '>', '^'];

    #[derive(Copy, Clone, Debug)]
    enum LexState {
        Src,
        Ident,
        Number,
        Str(char),
        EscapeStr(char),
        Blob,
        // A string within a blob
        BlobStr(char),
        BlobEscapeStr(char),
    }

    pub(super) struct Lexer<'a> {
        chars: std::iter::Enumerate<std::str::Chars<'a>>,
        lookahead: Option<(usize, char)>,
        buf: String,
        cur_start: usize,
        state: LexState,
    }

    impl Lexer<'_> {
        pub fn new(chars: std::str::Chars) -> Lexer<'_> {
            Lexer {
                chars: chars.enumerate(),
                lookahead: None,
                buf: String::new(),
                cur_start: 0,
                state: LexState::Src,
            }
        }

        // Postcondtion: self.state == Src && self.buf.is_empty()
        fn token(&mut self) -> Option<Token> {
            let text = mem::take(&mut self.buf);
            if text.is_empty() {
                self.state = LexState::Src;
                return None;
            }

            let mut len = text.len();

            let kind = match self.state {
                LexState::Ident if text.starts_with('$') => {
                    len -= 1;
                    TokenKind::Var(text[1..].to_owned())
                }
                LexState::Ident => TokenKind::Ident(text),
                LexState::Str(_) | LexState::EscapeStr(_) => TokenKind::String(text),
                LexState::Blob | LexState::BlobStr(_) | LexState::BlobEscapeStr(_) => {
                    TokenKind::Blob(text)
                }
                LexState::Number => TokenKind::Number(text.parse().unwrap()),
                LexState::Src => unreachable!(),
            };

            self.state = LexState::Src;

            Some(Token {
                kind,
                char: self.cur_start,
                len,
            })
        }
    }

    impl Iterator for Lexer<'_> {
        type Item = Token;

        fn next(&mut self) -> Option<Token> {
            for (i, c) in self.lookahead.take().into_iter().chain(&mut self.chars) {
                if self.buf.is_empty() {
                    self.cur_start = i;
                }

                match (c, self.state) {
                    // Variables and identifiers
                    (c, LexState::Src) if c == '$' || c.is_alphabetic() => {
                        self.buf.push(c);
                        self.state = LexState::Ident;
                    }
                    (c, LexState::Ident) if c.is_alphanumeric() => {
                        self.buf.push(c);
                    }
                    (_, LexState::Ident) => {
                        self.lookahead = Some((i, c));
                        return self.token();
                    }

                    // Numbers
                    (c, LexState::Src) if c == '-' || c.is_numeric() => {
                        self.buf.push(c);
                        self.state = LexState::Number;
                    }
                    (c, LexState::Number) if c.is_numeric() => {
                        self.buf.push(c);
                    }
                    (c, LexState::Number) => {
                        self.lookahead = Some((i, c));
                        return self.token();
                    }

                    // Operators
                    (c, LexState::Src) if OPS.contains(&c) => {
                        return Some(Token {
                            kind: TokenKind::Operator(c.try_into().unwrap()),
                            char: self.cur_start,
                            len: 1,
                        });
                    }

                    // Blobs and strings
                    ('`', LexState::Src) => {
                        self.state = LexState::Blob;
                    }
                    ('`', LexState::Blob) => {
                        return self.token();
                    }

                    ('\'', LexState::Src) | ('"', LexState::Src) => {
                        self.state = LexState::Str(c);
                    }
                    ('\'', LexState::Blob) | ('"', LexState::Blob) => {
                        self.buf.push(c);
                        self.state = LexState::BlobStr(c);
                    }
                    ('\\', LexState::Str(d)) => {
                        self.state = LexState::EscapeStr(d);
                    }
                    ('\\', LexState::BlobStr(d)) => {
                        self.buf.push(c);
                        self.state = LexState::BlobEscapeStr(d);
                    }
                    (_, LexState::EscapeStr(d)) => {
                        self.buf.push(c);
                        self.state = LexState::Str(d);
                    }
                    (_, LexState::BlobEscapeStr(d)) => {
                        self.buf.push(c);
                        self.state = LexState::BlobStr(d);
                    }
                    (d1, LexState::Str(d2)) if d1 == d2 => {
                        return self.token();
                    }
                    (d1, LexState::BlobStr(d2)) if d1 == d2 => {
                        self.buf.push(c);
                        self.state = LexState::Blob;
                    }
                    (_, LexState::Str(_)) | (_, LexState::Blob) | (_, LexState::BlobStr(_)) => {
                        self.buf.push(c);
                    }

                    // Whitespace
                    (' ', LexState::Src) | ('\t', LexState::Src) => {}

                    (c, LexState::Src) => {
                        return Some(Token {
                            kind: TokenKind::Unknown(c),
                            char: self.cur_start,
                            len: 1,
                        });
                    }
                }
            }
            self.token()
        }
    }

    #[cfg(test)]
    mod test {
        use super::{Operator::*, TokenKind::*, *};

        #[track_caller]
        fn assert_tokens(text: &str, expected: Vec<TokenKind>) {
            let mut split = ScriptSplitter::new(text.chars());
            let Some(text) = split.next() else {
                assert!(expected.is_empty());
                return;
            };
            assert!(split.next().is_none());
            let tokens = Lexer::new(text.chars());
            let actual: Vec<_> = tokens.map(|t| t.kind).collect();
            assert_eq!(actual, expected);
        }

        #[track_caller]
        fn assert_len(text: &str, expected: usize) {
            let mut split = ScriptSplitter::new(text.chars());
            let Some(text) = split.next() else {
                assert_eq!(expected, 0);
                return;
            };
            assert!(split.next().is_none());
            let tokens = Lexer::new(text.chars());
            let actual = tokens.count();
            assert_eq!(actual, expected);
        }

        fn s(s: &str) -> std::string::String {
            s.to_owned()
        }

        #[test]
        fn lex_simple() {
            // empty
            assert_tokens("", vec![]);
            assert_tokens("\n", vec![]);

            // whitespace
            assert_tokens(" \t ", vec![]);

            // comments
            assert_tokens("// dsafd sdf asdf sad fasdfasdfdf //sfsdfsadf", vec![]);

            // ident
            assert_tokens("foo", vec![Ident(s("foo"))]);

            // var
            assert_tokens("$foo", vec![Var(s("foo"))]);

            // operator
            assert_tokens("(= )", vec![Operator(Bra), Operator(Equals), Operator(Ket)]);

            // strings/blob
            assert_tokens("'hello'", vec![String(s("hello"))]);
            assert_tokens("\"hello\"", vec![String(s("hello"))]);
            assert_tokens("`hello`", vec![Blob(s("hello"))]);

            // unknown
            assert_tokens(" !  @", vec![Unknown('!'), Unknown('@')]);
        }

        #[test]
        fn lex_escapes() {
            assert_tokens("'he\\\" \\' llo'", vec![String(s("he\" ' llo"))]);
            assert_tokens("\"h\\\" \\'e\\lo\\\\ \"", vec![String(s("h\" 'elo\\ "))]);
        }

        #[test]
        fn lex_smoke() {
            assert_len("", 0);
            assert_len(
                "// dsfasdf sdfsf\n lots of idents should still parse // but not the comments\n",
                6,
            );
            assert_len("$0 = foo + 2 * $1.foo(bar, $baz)", 14);
            assert_len("= ( 'hello' > sdfsfdsa342s34df2", 5);
        }
    }
}
