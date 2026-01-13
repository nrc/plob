#![feature(trait_alias)]
#![feature(assert_matches)]

pub mod data;
pub mod lang;
pub mod stdio;
pub mod tui;

use std::{any::Any, cell::RefCell, collections::HashMap, fmt};

use data::{Data, MetaData};
use lang::ExecResult;

#[derive(Debug)]
pub struct Runtime {
    variables: HashMap<String, Value>,
    history: Vec<(String, ExecResult)>,
    out: Box<dyn Report>,

    // Could be a Vec rather than a HashMap
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

        for e in &errs {
            self.out.report_err(e, src);
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
                    self.out.echo(&format!(
                        "{}: {}",
                        self.history.len(),
                        ValueDisplay(value, self)
                    ));
                }
                ExecResult::Variable(name) => {
                    self.out.echo(&format!("{}: ${name}", self.history.len()));
                }
            }

            self.history.push((src.to_owned(), result));
        } else if errs.is_empty() {
            self.out.report_err(
                &Error::new(format!("Unknown error: {cmd:?}"), line, 0, src.len()),
                src,
            );
        }
    }

    fn get_variable(&self, name: &str) -> Option<&Value> {
        self.variables.get(name)
    }

    fn get_history(&self, offset: isize, position: usize) -> Option<(&str, &Value, usize)> {
        let index = if offset < 0 {
            if (-offset as usize) > position {
                return None;
            }
            position - (-offset as usize)
        } else {
            offset as usize
        };

        let hist = self.history.get(index)?;
        match &hist.1 {
            ExecResult::Echo(v) => Some((&hist.0, v, index)),
            ExecResult::Variable(v) => Some((&hist.0, self.get_variable(v)?, index)),
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
        self.metadata.borrow_mut().insert(id, MetaData::None);
        id
    }

    fn with_meta_data<T>(&self, index: usize, f: impl FnOnce(&mut MetaData) -> T) -> T {
        let mut metas = self.metadata.borrow_mut();
        let metadata = metas.get_mut(&index).unwrap();
        f(metadata)
    }

    #[cfg(test)]
    fn with_meta_datas<T>(&self, indicies: &[usize], f: impl FnOnce(&[&MetaData]) -> T) -> T {
        let metas = self.metadata.borrow_mut();
        let metadata: Vec<&MetaData> = indicies.iter().map(|i| metas.get(i).unwrap()).collect();
        f(&metadata)
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
    fn new(kind: ValueKind) -> Value {
        Value { kind }
    }

    fn resolve(&mut self, runtime: &Runtime) {
        if let ValueKind::Data(d) = &mut self.kind {
            d.resolve_structural(runtime);
        }
    }

    fn coerce_to(self, ty: &ValueType) -> Result<Value, Value> {
        use ValueKind::*;
        match (self.kind, ty) {
            (kind, ValueType::Any) => Ok(Value { kind }),

            (kind @ Data(_), ValueType::Data) => Ok(Value { kind }),
            (kind @ String(_), ValueType::String) => Ok(Value { kind }),
            (kind @ Number(_), ValueType::Number(NumberKind::Int)) => Ok(Value { kind }),
            (kind @ Number(n), ValueType::Number(NumberKind::UInt)) if n >= 0 => Ok(Value { kind }),
            (kind @ Bool(_), ValueType::Bool) => Ok(Value { kind }),

            (kind, _) => Err(Value { kind }),
        }
    }

    fn ty(&self) -> ValueType {
        self.kind.ty()
    }

    pub fn fmt(&self, w: &mut impl fmt::Write, runtime: &crate::Runtime) -> fmt::Result {
        match &self.kind {
            ValueKind::Data(data) => data.fmt(w, &data::FmtOptions::default(), runtime),
            ValueKind::String(s) => w.write_str(s),
            ValueKind::Number(n) => write!(w, "{n}"),
            ValueKind::Bool(b) => write!(w, "{b}"),
            ValueKind::Error => write!(w, "ERROR"),
            ValueKind::None => Ok(()),
        }
    }
}

struct ValueDisplay<'a>(&'a Value, &'a Runtime);

impl<'a> fmt::Display for ValueDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f, self.1)
    }
}

#[derive(Clone, Debug)]
pub enum ValueKind {
    Data(Data),
    String(String),
    Number(i64),
    Bool(bool),
    None,
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
    fn expect_string(self) -> String {
        match self {
            ValueKind::String(s) => s,
            _ => unreachable!(),
        }
    }

    #[cfg(test)]
    #[track_caller]
    fn expect_str(&self) -> &str {
        match self {
            ValueKind::String(s) => s,
            _ => unreachable!(),
        }
    }

    fn ty(&self) -> ValueType {
        use ValueKind::*;
        match &self {
            Data(_) => ValueType::Data,
            String(_) => ValueType::String,
            Number(n) if *n >= 0 => ValueType::Number(NumberKind::UInt),
            Number(_) => ValueType::Number(NumberKind::Int),
            Bool(_) => ValueType::Bool,
            None => ValueType::Any,
            Error => ValueType::Error,
        }
    }

    // #[track_caller]
    // fn expect_int(&self) -> i64 {
    //     match self {
    //         ValueKind::Number(n) => *n,
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

    #[track_caller]
    fn expect_bool(&self) -> bool {
        match self {
            ValueKind::Bool(b) => *b,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
enum ValueType {
    Any,
    Data,
    String,
    Number(NumberKind),
    Bool,
    Error,
}

#[derive(Clone, Debug)]
enum NumberKind {
    Int,
    UInt,
}

impl fmt::Display for ValueType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValueType::Any => write!(f, "any type"),
            ValueType::Data => write!(f, "data"),
            ValueType::String => write!(f, "string"),
            ValueType::Number(NumberKind::Int) => write!(f, "integer"),
            ValueType::Number(NumberKind::UInt) => write!(f, "postiive integer"),
            ValueType::Bool => write!(f, "boolean"),
            ValueType::Error => write!(f, "error"),
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
    fn new(msg: String, line: usize, char: usize, len: usize) -> Self {
        Error {
            msg,
            line,
            char,
            len,
        }
    }

    fn render(&self, src_line: &str) -> String {
        use std::fmt::Write;

        let mut result = self.msg.clone();
        result.push('\n');
        // TODO report the line number when using a file rather than the command line
        //write!(result, "{}   > ", self.line).unwrap();
        result.push_str(src_line);
        result.push('\n');
        // TODO account for width of line number
        writeln!(result, "{}{}", " ".repeat(self.char), "^".repeat(self.len)).unwrap();

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

    fn report_err(&self, e: &Error, src: &str) {
        panic!("Error {e:?} at `{src}`");
    }
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

            if let Some((i, _)) = expected_exact.iter().enumerate().find(|(_, ss)| *ss == s) {
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

    #[test]
    fn test_history() {
        let mut reporter = MockReporter::default();

        reporter.expected_exact = RefCell::new(vec![
            s("0: a"),
            s("1: b"),
            s("2: c"),
            s("3: c"),
            s("4: c"),
            s("5: a"),
            s("6: b"),
        ]);
        let mut runtime = Runtime::new(Box::new(reporter));
        runtime.exec_cmd("`a`", 0);
        runtime.exec_cmd("`b`", 0);
        runtime.exec_cmd("`c`", 0);
        runtime.exec_cmd("^", 0);
        runtime.exec_cmd("^", 0);
        runtime.exec_cmd("^^^^^", 0);
        runtime.exec_cmd("^1", 0);
    }
}
