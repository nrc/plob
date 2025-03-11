use std::{fs::File, io::read_to_string};

use crate::{
    Data, Error, Value, ValueKind, data,
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
                let ValueKind::Data(data) = lhs.kind else {
                    return Err(vec![self.make_err(
                        &format!("`fmt` expected data as input, found: `{}`", lhs.kind),
                        loc,
                    )]);
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
            "count" => {
                let Some(lhs) = lhs else {
                    return Err(vec![self.make_err(
                        "`count` requires data as input, but called with no input",
                        loc,
                    )]);
                };
                let ValueKind::Data(data) = lhs.kind else {
                    return Err(vec![self.make_err(
                        &format!("`count` expected data as input, found: `{}`", lhs.kind),
                        loc,
                    )]);
                };

                crate::data::reparse::require_reparsed(&data, Some(1), &self.runtime);
                match data {
                    Data::Struct(_, r) => {
                        let reparsed = &self.runtime.metadata.borrow()[&r].reparsed;
                        Ok(Value {
                            kind: ValueKind::Number(reparsed.count() as i64),
                        })
                    }
                    Data::Unknown => {
                        return Err(vec![self.make_err("unknown data input", loc)]);
                    }
                    _ => unimplemented!(),
                }
            }
            "read" => {
                if lhs.is_some() {
                    return Err(vec![self.make_err(
                        "`read` takes no input so should not appear in a pipeline",
                        loc,
                    )]);
                }

                let mut path = None;
                let mut errors = Vec::new();
                for (name, expr) in args {
                    match &*name.inner {
                        "path" => {
                            let loc = expr.location;
                            let val = expr.exec(self)?;
                            match val.kind {
                                ValueKind::String(s) => {
                                    path = Some(s);
                                }
                                _ => {
                                    errors.push(self.make_err(
                                        &format!("`path` argument to `read` must be a string"),
                                        loc,
                                    ));
                                    continue;
                                }
                            }
                        }
                        n => errors.push(self.make_err(
                            &format!("unexpected argument to `read`: `{n}`"),
                            name.location,
                        )),
                    }
                }

                if !errors.is_empty() {
                    return Err(errors);
                }

                let Some(path) = path else {
                    return Err(vec![
                        self.make_err("`read` requires a `path` argument but none found", loc),
                    ]);
                };

                let Ok(file) = File::open(&path) else {
                    return Err(vec![
                        self.make_err(&format!("could not open file: {path}"), loc),
                    ]);
                };

                let Ok(content) = read_to_string(file) else {
                    return Err(vec![
                        self.make_err(&format!("could not read file: {path}"), loc),
                    ]);
                };

                let data = data::parse(&content, &self.runtime)?;
                Ok(Value {
                    kind: ValueKind::Data(data),
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
                let data = data::parse(&b, &ctxt.runtime)?;
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
