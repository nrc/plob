use std::{collections::HashMap, sync::LazyLock};

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
/// pipe ::= lexpr? (`>` `>`? pexpr)+
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
        msg,
        line,
        char: tok.char,
        len: tok.len,
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
        src_line: cmd.line,
    };
    match cmd.kind {
        parse::CmdKind::Assign(name, expr) => {
            let value = match expr.exec(&mut ctxt) {
                Ok(v) => v,
                Err(e) => return ExecResult::Error(e),
            };
            let name = runtime.save_variable(name.map(|n| n.inner), value);
            ExecResult::Variable(name)
        }
        parse::CmdKind::Echo(expr) => {
            let value = match expr.exec(&mut ctxt) {
                Ok(v) => v,
                Err(e) => return ExecResult::Error(e),
            };
            ExecResult::Echo(value)
        }
        parse::CmdKind::Error(_) => unreachable!(),
    }
}

pub fn help_message_for(cmd: &str, arg2: Option<&str>) -> String {
    if cmd == "lang" {
        if let Some(topic) = arg2 {
            return help_lang_for(topic);
        }
        return help_lang();
    }

    exec::help_message_for(cmd)
}

fn help_lang() -> String {
    format!(
        "For help on a specific topic use `h lang topic`, available topics:\n\n{}",
        HELP_TOPICS
            .iter()
            .map(|(k, (title, _))| format!("{k}: {title}\n"))
            .collect::<String>()
    )
}

fn help_lang_for(cmd: &str) -> String {
    match HELP_TOPICS.get(cmd) {
        Some((title, docs)) => format!("# {title}\n\n{docs}"),
        None => format!(
            "Unknown lnaguage topic; available topics:\n{}",
            HELP_TOPICS
                .iter()
                .map(|(k, (title, _))| format!("{k}: {title}\n"))
                .collect::<String>()
        ),
    }
}

static HELP_TOPICS: LazyLock<HashMap<&str, (&str, &str)>> = LazyLock::new(|| {
    [
        (
            "fn",
            ("Functions",
            "E.g.,`> fmt()`

Use `h all` to list functions or `h fn` to get help about a specific function `fn`.

Functions can have named or unnamed arguments, unnamed use their position in the argument list including any
named arguments. They can also take input through a pipeline (using `>`; for more help on pipelines use `h lang pipe`).
"),
        ),
        (
            "var",
            ("Variables",
            "Variables start with `$` and can be assigned into using `=`, e.g., `$foo = 42`.

Variables can be used by naming, e.g, `$bar > fmt()`

A history variable begins with `^` and can be one or more carets (referring to the output of the previous command, or the commands before that using the number of carets).
`^n` refers to the nth command to be successfully executed (i.e., the number displayed when a command is executed).

Using `=` without a lhs creates a new variable with a numeric name, e.g., `$42`. These can be used in the same way as regular variables (and are unrelated to history variables)."),
        ),
        (
            "pipe",
            ("Pipelines",
            "Use `>` to feed input into the next pipeline stage. Input can be a variable or a history variable.
If there is no explicit input, then the output of the previous command is used.
The right hand side of the pipe can be a function call.
"),
        ),
    ]
    .into_iter()
    .collect()
});
