pub mod data;
pub mod lang;
pub mod tui;

use std::collections::HashMap;

use data::Data;

#[derive(Debug)]
pub struct Runtime {
    variables: HashMap<String, Value>,
    history: Vec<Value>,
}

impl Runtime {
    fn new() -> Self {
        Runtime {
            variables: HashMap::new(),
            history: Vec::new(),
        }
    }

    fn exec_cmd(&mut self, src: &str, line: usize) {
        let (cmd, errs) = lang::parse_cmd(src, line);
        // TODO report errs
        if !cmd.is_error() {
            // TODO run command

            // TODO save result in history
        }
    }
}

#[derive(Clone, Debug)]
pub struct Value {
    kind: ValueKind,
}

#[derive(Clone, Debug)]
pub enum ValueKind {
    Data(Data),
    String(String),
    Number(usize),
    Error,
}

// TODO for reporting errors and results
trait Report {}
