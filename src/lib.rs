#![feature(trait_alias)]

pub mod data;
pub mod lang;
pub mod stdio;
pub mod tui;

use std::{any::Any, cell::RefCell, collections::HashMap, fmt};

use data::Data;
use lang::ExecResult;

#[derive(Debug)]
pub struct Runtime {
    variables: HashMap<String, Value>,
    history: Vec<(String, ExecResult)>,
    out: Box<dyn Report>,

    metadata: RefCell<HashMap<usize, MetaData>>,
}

impl Runtime {
    fn new(out: Box<dyn Report>) -> Self {
        Runtime {
            variables: HashMap::new(),
            history: Vec::new(),
            out,
            metadata: RefCell::new(HashMap::new()),
        }
    }

    #[cfg(test)]
    fn new_test() -> Self {
        Self::new(Box::new(BlackHole))
    }

    fn exec_cmd(&mut self, src: &str, line: usize) {
        let (cmd, errs) = lang::parse_cmd(src, line);
        // TODO If cmd is an error command, then report it and return.

        for e in errs {
            self.out.report_err(&e, src);
        }

        if !cmd.is_error() {
            let result = lang::run_cmd(cmd, self);
            match &result {
                ExecResult::Error(errs) => {
                    for err in errs {
                        self.out.report_err(err, src);
                    }
                    return;
                }
                ExecResult::Echo(value) => {
                    self.out.echo(&format!("{}: {value}", self.history.len()));
                }
                ExecResult::Variable(name) => {
                    self.out.echo(&format!("{}: ${name}", self.history.len()));
                }
            }

            self.history.push((src.to_owned(), result));
        }
    }

    fn get_variable(&self, name: &str) -> Option<&Value> {
        self.variables.get(name)
    }

    fn get_history(&self, offset: isize) -> Option<&Value> {
        let index = if offset < 0 {
            if (-offset as usize) > self.history.len() {
                return None;
            }
            self.history.len() - (-offset as usize)
        } else {
            offset as usize
        };

        match &self.history.get(index)?.1 {
            ExecResult::Echo(v) => Some(v),
            ExecResult::Variable(v) => self.get_variable(v),
            _ => unreachable!(),
        }
    }

    fn save_variable(&mut self, name: Option<String>, value: Value) -> String {
        let name = name.unwrap_or_else(|| self.variables.len().to_string());
        self.variables.insert(name.clone(), value);
        name
    }

    fn init_meta_data(&self) -> usize {
        let id = self.metadata.borrow().len();
        self.metadata.borrow_mut().insert(id, MetaData::default());
        id
    }

    fn help_message<'a>(&self, mut args: impl Iterator<Item = &'a str>) -> String {
        if let Some(arg) = args.next() {
            return lang::help_message_for(arg, args.next());
        }
        r#"
plob

# Commands

q           quit
h [fn]      display this help message
              or display help for a function `fn`; use `all` to list all avaialble functions
              or use `h lang` for language help
"#
        .to_owned()
    }
}

#[derive(Debug, Clone)]
pub struct Value {
    kind: ValueKind,
}

impl Value {
    fn coerce_to(self, ty: &ValueType) -> Result<Value, Value> {
        use ValueKind::*;
        match (self.kind, ty) {
            (kind, ValueType::Any) => Ok(Value { kind }),

            (kind @ Data(_), ValueType::Data) => Ok(Value { kind }),
            (kind @ String(_), ValueType::String) => Ok(Value { kind }),
            (kind @ Number(_), ValueType::Number(NumberKind::Int)) => Ok(Value { kind }),
            (kind @ Number(n), ValueType::Number(NumberKind::UInt)) if n >= 0 => Ok(Value { kind }),

            (kind, _) => Err(Value { kind }),
        }
    }

    fn ty(&self) -> ValueType {
        use ValueKind::*;
        match &self.kind {
            Data(_) => ValueType::Data,
            String(_) => ValueType::String,
            Number(n) if *n >= 0 => ValueType::Number(NumberKind::UInt),
            Number(_) => ValueType::Number(NumberKind::Int),
            Error => ValueType::Error,
        }
    }
}

#[derive(Clone, Debug)]
pub enum ValueKind {
    Data(Data),
    String(String),
    Number(i64),
    Error,
}

impl ValueKind {
    #[track_caller]
    fn expect_data(self) -> Data {
        match self {
            ValueKind::Data(d) => d,
            _ => unreachable!(),
        }
    }

    #[track_caller]
    fn expect_str(self) -> String {
        match self {
            ValueKind::String(s) => s,
            _ => unreachable!(),
        }
    }

    // #[track_caller]
    // fn expect_int(self) -> i64 {
    //     match self {
    //         ValueKind::Number(n) => n,
    //         _ => unreachable!(),
    //     }
    // }

    #[track_caller]
    fn expect_uint(&self) -> u64 {
        match self {
            ValueKind::Number(n) if *n >= 0 => *n as u64,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
enum ValueType {
    #[allow(dead_code)]
    Any,
    Data,
    String,
    Number(NumberKind),
    Error,
}

#[derive(Clone, Debug)]
enum NumberKind {
    Int,
    UInt,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ValueKind::Data(data) => fmt::Display::fmt(data, f),
            ValueKind::String(s) => s.fmt(f),
            ValueKind::Number(n) => n.fmt(f),
            ValueKind::Error => write!(f, "ERROR"),
        }
    }
}

impl fmt::Display for ValueKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValueKind::Data(d) => write!(f, "data({})", d.ty()),
            ValueKind::String(_) => write!(f, "string"),
            ValueKind::Number(_) => write!(f, "number"),
            ValueKind::Error => write!(f, "error"),
        }
    }
}

impl fmt::Display for ValueType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValueType::Any => write!(f, "any type"),
            ValueType::Data => write!(f, "data"),
            ValueType::String => write!(f, "string"),
            ValueType::Number(NumberKind::Int) => write!(f, "integer"),
            ValueType::Number(NumberKind::UInt) => write!(f, "postiive integer"),
            ValueType::Error => write!(f, "error"),
        }
    }
}

#[derive(Clone, Debug)]
struct MetaData {
    reparsed: data::reparse::Node,
    reparse_depth: Option<usize>,
}

impl Default for MetaData {
    fn default() -> Self {
        MetaData {
            reparsed: data::reparse::Node::Todo,
            reparse_depth: Some(0),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Error {
    pub msg: String,
    pub line: usize,
    pub char: usize,
    pub len: usize,
}

impl Error {
    fn render(&self, src_line: &str) -> String {
        use std::fmt::Write;

        let mut result = self.msg.clone();
        result.push('\n');
        write!(result, "{}   > ", self.line).unwrap();
        result.push_str(src_line);
        result.push('\n');
        // TODO account for width of line number
        writeln!(
            result,
            "      {}{}",
            " ".repeat(self.char),
            "^".repeat(self.len)
        )
        .unwrap();

        result
    }
}

trait Report: Any + fmt::Debug {
    fn echo(&self, s: &str);
    fn report_err(&self, err: &Error, src_line: &str);
}

#[cfg(test)]
#[derive(Clone, Debug)]
struct BlackHole;

#[cfg(test)]
impl Report for BlackHole {
    fn echo(&self, _: &str) {}
    fn report_err(&self, _: &Error, _: &str) {}
}

#[cfg(test)]
mod test {
    use std::cell::RefCell;

    use super::*;

    #[derive(Debug, Clone, Default)]
    struct MockReporter {
        expected_errs: RefCell<Vec<String>>,
        expected_exact: RefCell<Vec<String>>,
        expected_contains: RefCell<Vec<String>>,
    }

    impl Drop for MockReporter {
        fn drop(&mut self) {
            assert!(
                self.expected_errs.borrow().is_empty(),
                "Expected error was not seen: {:#?}",
                self.expected_errs
            );
            assert!(
                self.expected_exact.borrow().is_empty(),
                "Expected report was not seen: {:#?}",
                self.expected_exact
            );
            assert!(
                self.expected_contains.borrow().is_empty(),
                "Expected report was not seen: {:#?}",
                self.expected_contains
            );
        }
    }

    impl Report for MockReporter {
        fn echo(&self, s: &str) {
            eprint!("recevied `{s}` ");
            let mut expected_exact = self.expected_exact.borrow_mut();

            if let Some((i, _)) = expected_exact.iter().enumerate().find(|(_, ss)| *ss == &s) {
                expected_exact.swap_remove(i);
                eprintln!("found (exact)");
                return;
            }

            let mut expected_contains = self.expected_contains.borrow_mut();

            if let Some((i, _)) = expected_contains
                .iter()
                .enumerate()
                .find(|(_, ss)| s.contains(*ss))
            {
                expected_contains.swap_remove(i);
                eprintln!("found (contains)");
                return;
            }

            eprintln!("skipped");
        }

        fn report_err(&self, err: &Error, _: &str) {
            eprint!("recevied {err:?} ");
            let mut expected_errs = self.expected_errs.borrow_mut();

            if let Some(i) = expected_errs
                .iter()
                .enumerate()
                .find(|(_, s)| *s == &err.msg)
                .map(|(i, _)| i)
            {
                expected_errs.swap_remove(i);
                eprintln!("found");
                return;
            }

            eprintln!("skipped");
        }
    }

    fn s(s: &str) -> std::string::String {
        s.to_owned()
    }

    #[test]
    fn test_echo() {
        let mut reporter = MockReporter::default();

        reporter.expected_exact = RefCell::new(vec![
            s("0: $0"),
            s("1: hello { }"),
            s("2: $foo"),
            s("3: hello { }"),
            s("4: hello { }"),
        ]);
        let mut runtime = Runtime::new(Box::new(reporter));
        runtime.exec_cmd("= `hello {}`", 0);
        runtime.exec_cmd("$0", 1);
        runtime.exec_cmd("$foo = $0", 1);
        runtime.exec_cmd("$foo", 1);
        runtime.exec_cmd("`hello {  }`", 0);
    }
}
