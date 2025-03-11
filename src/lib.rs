pub mod data;
pub mod lang;
pub mod stdio;

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

        for e in errs {
            self.out.report_err(&e);
        }

        if !cmd.is_error() {
            let result = lang::run_cmd(cmd, self);
            if let ExecResult::Error(errs) = &result {
                for err in errs {
                    self.out.report_err(err);
                }
            } else {
                self.history.push((src.to_owned(), result));
            }
        }
    }

    fn echo(&self, value: &Value) {
        self.out.echo(&value.to_string());
    }

    fn report(&self, s: &str) {
        self.out.echo(s);
    }

    fn get_variable(&self, name: &str) -> Option<&Value> {
        self.variables.get(name)
    }

    fn get_history(&self, offset: usize) -> Option<&Value> {
        if offset > self.history.len() {
            return None;
        }
        match &self.history[self.history.len() - offset].1 {
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
}

#[derive(Debug, Clone)]
pub struct Value {
    kind: ValueKind,
}

#[derive(Clone, Debug)]
pub enum ValueKind {
    Data(Data),
    String(String),
    Number(i64),
    Error,
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

// TODO structured error
#[derive(Clone, Debug)]
pub struct Error {
    pub msg: String,
}

trait Report: Any + fmt::Debug {
    fn echo(&self, s: &str);
    fn report_err(&self, err: &Error);
}

#[cfg(test)]
#[derive(Clone, Debug)]
struct BlackHole;

#[cfg(test)]
impl Report for BlackHole {
    fn echo(&self, _: &str) {}
    fn report_err(&self, _: &Error) {}
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

        fn report_err(&self, err: &Error) {
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
        // TODO formatting of `{}`
        reporter.expected_exact = RefCell::new(vec![
            s("$0"),
            s("hello { }"),
            s("$foo"),
            s("hello { }"),
            s("hello { }"),
        ]);
        let mut runtime = Runtime::new(Box::new(reporter));
        runtime.exec_cmd("= `hello {}`", 0);
        runtime.exec_cmd("$0", 1);
        runtime.exec_cmd("$foo = $0", 1);
        runtime.exec_cmd("$foo", 1);
        runtime.exec_cmd("`hello {  }`", 0);
    }
}
