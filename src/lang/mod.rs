pub use lex::Token;
pub use parse::Command;

mod exec;
mod lex;
mod parse;

pub fn parse_script(text: &str) -> (Vec<Command>, Vec<crate::Error>) {
    let iter = lex::ScriptSplitter::new(text.chars());
    let (cmds, errs): (Vec<_>, Vec<Vec<_>>) = iter
        .enumerate()
        .map(|(i, line)| parse::parse_cmd_inner(&line, i))
        .unzip();
    (cmds, errs.into_iter().flatten().collect())
}

// TODO tasks/requirements
//
// errors
// read from file `read('foo.txt')`
// reapply, e.g., `$a > fmt()`; `^(depth=2)`
// project
// map `lexpr >> pexpr` e.g., `$0 >> .kind`
// flatten?
// concat
// search/select

/// # Grammar
///
/// cmd ::= assign | expr
/// assign ::= var? `=` expr
/// expr ::= var | hist_var | literal | expr project | pipe | repipe | call | reapply
/// pipe ::= lexpr? (`>` pexpr)+
/// lexpr ::= var | hist_var | `(` expr `)`
/// pexpr ::= project | call | `where` pexpr
/// repipe ::= var? (`<` `<`? rexpr)+  // replay
/// rexpr ::= hist_var,+ | pexpr
/// project ::= `.` selector
/// selector ::= int | ident | var | string | `(` selector,* `)`
/// call ::= ident `(` (ident = expr),* `)`
/// reapply ::= (var | hist_var) `(` (ident = expr),* `)`
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
