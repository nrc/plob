use std::{collections::HashMap, sync::LazyLock};

pub use exec::Context as ExecContext;
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
// table functions: projection (by named columns), selection (should work for lists too), split col/row, insert col/row, apply complex layout
// convert struct data to tabular data
// more precise types for different kinds of data
// diff function to compare data
// np? map `lexpr >> pexpr` e.g., `$0 >> .kind` (should we even need syntax for this rather than just a pipe?)
// flatten?
// dbg should generate data (requires returning multiple values - could use sequence data, in which case need array access)
// project
//  - docs
//  - test on data with different structures
//  - how deeply do we need to reparse? (TODO in eval_projection)
//  - selectors with mix of numbers and idents
// search/select (extend range syntax to expressions)
// reapply in pipe, e.g., `$a > fmt()`; `$b > ^(depth=2)`
// function calls: revisit rules around named/unnamed args

/// # Grammar
///
/// cmd ::= assign | expr
/// assign ::= var? `=` expr
/// expr ::= var | hist_var | reapply | literal | lexpr project | lexpr select | pipe | repipe | call
/// pipe ::= lexpr? (`>` `>`? pexpr)+
/// lexpr ::= var | hist_var | `(` expr `)`
/// pexpr ::= project | select | call
/// repipe ::= var? (`<` `<`? rexpr)+  // replay
/// rexpr ::= hist_var,+ | pexpr
/// project ::= (`.` selector)+
/// select ::= `[` (range_selector `,`)+ `]`
/// selector ::= single_selector | `(` single_selector,* `)` | `*`
/// single_selector ::= int | ident | string
/// range_selector ::= single_selector | single_selector? `..` single_selector?
/// call ::= ident `(` (ident = expr),* `)`
/// reapply ::= hist_var `(` (ident = expr),* `)`
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
        history_position: runtime.history.len(),
    };
    match cmd.kind {
        parse::CmdKind::Assign(name, expr) => {
            let mut value = match expr.exec(&mut ctxt) {
                Ok(v) => v,
                Err(e) => return ExecResult::Error(e),
            };
            value.resolve(ctxt.runtime);
            let name = runtime.save_variable(name.map(|n| n.inner), value);
            ExecResult::Variable(name)
        }
        parse::CmdKind::Echo(expr) => {
            let mut value = match expr.exec(&mut ctxt) {
                Ok(v) => v,
                Err(e) => return ExecResult::Error(e),
            };
            value.resolve(ctxt.runtime);
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
        (
            "reapply",
            ("Function re-application",
            "E.g., `^(depth = 2)`

Where a previous expression (indicated by the history variable, which may be any history variable, see `h lang var`) is a function call,
calls the same function with the same input but with any specified parameters overriding parameters in the original call.
"),
        ),
    ]
    .into_iter()
    .collect()
});
