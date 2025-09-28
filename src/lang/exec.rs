use std::{collections::HashMap, fs::File, io::read_to_string, sync::LazyLock};

use crate::{
    Data, Error, NumberKind, Value, ValueKind, ValueType, data,
    lang::parse::{Action, CmdKind, Expr, Node, NodeLoc},
};

pub fn help_message_for(cmd: &str) -> String {
    if cmd == "all" {
        return FUNCTIONS
            .values()
            .map(|f| format!("{}: {}\n", f.name, f.help_msg))
            .collect::<String>();
    }

    match FUNCTIONS.get(cmd) {
        Some(f) => format!("`{}`\n{}", f.signature, f.help_msg),
        None => format!(
            "Unknown function; available functions:\n{}",
            FUNCTIONS
                .values()
                .map(|f| format!("{}: {}\n", f.name, f.help_msg))
                .collect::<String>()
        ),
    }
}

#[derive(Clone)]
pub struct Context<'a> {
    pub runtime: &'a crate::Runtime,
    pub src_line: usize,
    pub history_position: usize,
}

impl Context<'_> {
    fn make_err(&self, msg: impl Into<String>, loc: NodeLoc) -> crate::Error {
        Error {
            msg: msg.into(),
            line: self.src_line,
            char: loc.char,
            len: loc.len,
        }
    }

    fn call(
        &mut self,
        fn_name: &str,
        lhs: Option<Value>,
        args: Vec<(Option<Node<String>>, Node<Expr>)>,
        arg_overrides: Vec<(Node<String>, Node<Expr>)>,
        loc: NodeLoc,
    ) -> Result<Value, Vec<Error>> {
        // Function lookup.
        let Some(f) = FUNCTIONS.get(fn_name) else {
            return Err(vec![
                self.make_err(format!("Unknown function name: `{fn_name}`"), loc),
            ]);
        };

        // Check input and args.
        let input = f.type_check_input(lhs, loc, self)?;
        let args = f.type_check_args(args, arg_overrides, loc, self)?;

        // Call the function
        (f.call)(input, args, loc, self)
    }
}

static FUNCTIONS: LazyLock<HashMap<&str, Function>> = LazyLock::new(|| {
    [
        Function::new(
            "fmt",
            Some(ValueType::Data),
            vec![("depth", ValueType::Number(NumberKind::UInt), true)],
            "data > fmt(depth?: int >= 0) > string",
            "formats data",
            &call_fmt,
        ),
        Function::new(
            "ty",
            Some(ValueType::Data),
            vec![],
            "data > ty() > string",
            "returns the type of data",
            &call_ty,
        ),
        Function::new(
            "count",
            Some(ValueType::Data),
            vec![],
            "data > count() > int",
            "count elements of data",
            &call_count,
        ),
        Function::new(
            "read",
            None,
            vec![("path", ValueType::String, false)],
            "read(path: string) > data",
            "read a file into data",
            &call_read,
        ),
        #[cfg(test)]
        Function::new(
            "test",
            Some(ValueType::Data),
            vec![
                ("a", ValueType::String, false),
                ("b", ValueType::String, false),
                ("c", ValueType::String, true),
            ],
            "data > test(a: string, b: string, c: string) > data",
            "test function",
            &call_test,
        ),
    ]
    .into_iter()
    .map(|f| (f.name, f))
    .collect()
});

trait FnCall = Fn(
    Option<ValueKind>,
    Vec<Option<ValueKind>>,
    NodeLoc,
    &mut Context,
) -> Result<Value, Vec<Error>>;

#[derive(Clone)]
struct Function {
    name: &'static str,
    // TODO generate signature
    signature: String,
    help_msg: String,
    input: Option<ValueType>,
    // Name, type, optional.
    args: Vec<(&'static str, ValueType, bool)>,
    call: &'static dyn FnCall,
}

impl Function {
    fn new(
        name: &'static str,
        input: Option<ValueType>,
        args: Vec<(&'static str, ValueType, bool)>,
        signature: impl Into<String>,
        help_msg: impl Into<String>,
        call: &'static dyn FnCall,
    ) -> Self {
        Function {
            name,
            input,
            args,
            signature: signature.into(),
            help_msg: help_msg.into(),
            call,
        }
    }

    fn type_check_input(
        &self,
        input: Option<Value>,
        loc: NodeLoc,
        ctxt: &mut Context,
    ) -> Result<Option<ValueKind>, Vec<Error>> {
        match (&self.input, input) {
            (Some(ty), Some(input)) => match (ty, input.kind) {
                (ValueType::Any, k) => Ok(Some(k)),
                (ValueType::Data, k @ ValueKind::Data(_)) => Ok(Some(k)),
                (ValueType::String, k @ ValueKind::String(_)) => Ok(Some(k)),
                (ValueType::Number(NumberKind::Int), k @ ValueKind::Number(_)) => Ok(Some(k)),
                (ValueType::Number(NumberKind::UInt), k @ ValueKind::Number(_)) => Ok(Some(k)),
                (ty, k) => Err(vec![ctxt.make_err(
                    format!("`{}` expected {ty} as input, found: `{k}`", self.name),
                    loc,
                )]),
            },
            (None, None) => Ok(None),
            (Some(_), None) => Err(vec![ctxt.make_err(
                format!(
                    "`{}` requires data as input, but called with no input",
                    self.name
                ),
                loc,
            )]),
            (None, Some(_)) => Err(vec![ctxt.make_err(
                format!(
                    "`{}` takes no input so should not appear in a pipeline",
                    self.name
                ),
                loc,
            )]),
        }
    }

    fn type_check_args(
        &self,
        args: Vec<(Option<Node<String>>, Node<Expr>)>,
        arg_overrides: Vec<(Node<String>, Node<Expr>)>,
        loc: NodeLoc,
        ctxt: &mut Context,
    ) -> Result<Vec<Option<ValueKind>>, Vec<Error>> {
        let mut args: Vec<_> = args.into_iter().map(|(n, e)| (n, Some(e))).collect();
        let mut arg_overrides: Vec<_> = arg_overrides
            .into_iter()
            .map(|(n, e)| (Some(n), Some(e)))
            .collect();

        let results: Vec<Result<Option<Value>, Vec<Error>>> = self.args.iter().enumerate().map(|(i, (n, ty, opt))| {
            let mut arg = if let Some(arg) = args.iter_mut().find(|(an, _)| matches!(an, Some(an) if &an.inner == n)) {
                arg.1.take()
            } else if args.len() > i && args[i].0.is_none() {
                args[i].1.take()
            } else {
                None
            };

            if let Some(ao) = arg_overrides.iter_mut().find(|(an, _)| matches!(an, Some(an) if &an.inner == n)) {
                arg = ao.1.take();
            }

            let Some(arg) = arg else {
                if *opt {
                    return Ok(None);
                } else {
                    return Err(vec![ctxt.make_err(format!("`{}` requires a `{n}` argument but none found", self.name), loc)]);
                }
            };

            let value = arg.exec(ctxt)?;
            value
                .coerce_to(ty)
                .map_err(|orig| vec![ctxt.make_err(format!("`{}` expects an argument `{n}` with type `{ty}`, but found type `{}`", self.name, orig.ty()), loc)])
                .map(Some)
        }).collect();

        let (results, errors): (Vec<_>, Vec<_>) = results.into_iter().partition(|r| r.is_ok());
        let mut errors: Vec<_> = errors.into_iter().flat_map(Result::unwrap_err).collect();

        // Check for extra args
        for (i, (l, e)) in args
            .iter()
            .enumerate()
            .chain(arg_overrides.iter().enumerate())
        {
            if e.is_some() {
                errors.push(ctxt.make_err(
                    format!(
                            "unexpected argument to `{}`: {}",
                            self.name,
                            l.as_ref()
                                .map(|a| format!("`{}`", a.inner))
                                .unwrap_or_else(|| format!("argument {i}"))
                        ),
                    loc,
                ));
            }
        }

        // return errors
        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(results
            .into_iter()
            .map(|v| v.unwrap().map(|v| v.kind))
            .collect())
    }
}

unsafe impl Send for Function {}
unsafe impl Sync for Function {}

fn call_fmt(
    lhs: Option<ValueKind>,
    mut args: Vec<Option<ValueKind>>,
    _loc: NodeLoc,
    _ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let data = lhs.unwrap().expect_data();
    let depth = args.pop().unwrap();

    let mut opts = data::FmtOptions::default();
    if let Some(depth) = depth {
        opts.depth = Some(depth.expect_uint() as usize);
    }

    let mut buf = String::new();
    data.fmt(&mut buf, &opts).unwrap();
    Ok(Value {
        kind: ValueKind::String(buf),
    })
}

fn call_ty(
    lhs: Option<ValueKind>,
    _args: Vec<Option<ValueKind>>,
    _loc: NodeLoc,
    _ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    Ok(Value {
        kind: ValueKind::String(lhs.unwrap().to_string()),
    })
}

fn call_count(
    lhs: Option<ValueKind>,
    _: Vec<Option<ValueKind>>,
    loc: NodeLoc,
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let data = lhs.unwrap().expect_data();

    crate::data::reparse::require_reparsed(&data, Some(1), ctxt.runtime);
    match data {
        Data::Struct(_, r) => {
            let reparsed = &ctxt.runtime.metadata.borrow()[&r].reparsed;
            Ok(Value {
                kind: ValueKind::Number(reparsed.count() as i64),
            })
        }
        Data::Unknown => Err(vec![ctxt.make_err("unknown data input", loc)]),
        _ => unimplemented!(),
    }
}

fn call_read(
    _: Option<ValueKind>,
    mut args: Vec<Option<ValueKind>>,
    loc: NodeLoc,
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let path = args.pop().unwrap().unwrap().expect_string();

    let Ok(file) = File::open(&path) else {
        return Err(vec![
            ctxt.make_err(format!("could not open file: {path}"), loc),
        ]);
    };

    let Ok(content) = read_to_string(file) else {
        return Err(vec![
            ctxt.make_err(format!("could not read file: {path}"), loc),
        ]);
    };

    let data = data::parse(&content, ctxt.src_line, ctxt.runtime)?;
    Ok(Value {
        kind: ValueKind::Data(data),
    })
}

#[cfg(test)]
static TEST_FN_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
#[cfg(test)]
static TEST_FN: std::sync::Mutex<
    Option<Box<fn(&Data, &[Option<ValueKind>], NodeLoc, &mut Context)>>,
> = std::sync::Mutex::new(None);

#[cfg(test)]
fn call_test(
    lhs: Option<ValueKind>,
    args: Vec<Option<ValueKind>>,
    loc: NodeLoc,
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let data = lhs.unwrap().expect_data();

    let f = TEST_FN.lock().unwrap();
    let f = f.as_ref().unwrap();
    f(&data, &args, loc, ctxt);

    Ok(Value {
        kind: ValueKind::Data(data),
    })
}

impl Node<Expr> {
    pub fn exec(self, ctxt: &mut Context) -> Result<Value, Vec<Error>> {
        match self.inner {
            Expr::Var(name) => ctxt.runtime.get_variable(&name).cloned().ok_or(vec![
                ctxt.make_err(format!("Unknown variable: `${name}`"), self.location),
            ]),
            Expr::HistVar(n) => ctxt
                .runtime
                .get_history(n, ctxt.history_position)
                .map(|(_, v, _)| v.clone())
                .ok_or(vec![ctxt.make_err(
                    format!("Invalid historic value: `{}`", self.inner),
                    self.location,
                )]),
            Expr::Reapply(n, args) => {
                let (src, pos) = ctxt
                    .runtime
                    .get_history(n.inner, ctxt.history_position)
                    .map(|(src, _, i)| (src.to_owned(), i))
                    .ok_or(vec![ctxt.make_err("Invalid historic value", self.location)])?;

                let (cmd, errs) = super::parse_cmd(&src, 0);
                if cmd.is_error() || !errs.is_empty() {
                    return Err(vec![
                        ctxt.make_err("Could not parse re-application command", self.location),
                    ]);
                }
                let expr = match cmd.kind {
                    CmdKind::Echo(e) => e,
                    CmdKind::Assign(_, e) => e,
                    _ => unreachable!(),
                };

                let mut ctxt = Context {
                    history_position: pos,
                    ..ctxt.clone()
                };
                let (lhs, name, prev_args) = match expr.inner {
                    Expr::Action(Action::Call(name, args)) => (None, name, args),
                    Expr::Pipe(lhs, mut actions) => {
                        let last = actions.pop().unwrap();
                        let pipe_result = eval_pipe(lhs, actions, &mut ctxt, self.location)?;
                        let (name, args) = match last.inner {
                            Action::Call(name, args) => (name, args),
                        };
                        (Some(pipe_result), name, args)
                    }
                    e => {
                        return Err(vec![ctxt.make_err(
                            format!("Re-applied command is not a function call (found {e:?})"),
                            self.location,
                        )]);
                    }
                };

                ctxt.call(&name.inner, lhs, prev_args, args, self.location)
            }
            Expr::Int(n) => Ok(Value {
                kind: ValueKind::Number(n),
            }),
            Expr::String(s) => Ok(Value {
                kind: ValueKind::String(s),
            }),
            Expr::Blob(b) => {
                let data = data::parse(&b, ctxt.src_line, ctxt.runtime)?;
                Ok(Value {
                    kind: ValueKind::Data(data),
                })
            }
            Expr::Pipe(lhs, actions) => eval_pipe(lhs, actions, ctxt, self.location),
            Expr::Action(action) => match action {
                Action::Call(name, args) => {
                    ctxt.call(&name.inner, None, args, Vec::new(), self.location)
                }
            },
        }
    }
}

fn eval_pipe(
    lhs: Option<Box<Node<Expr>>>,
    actions: Vec<Node<Action>>,
    ctxt: &mut Context,
    loc: NodeLoc,
) -> Result<Value, Vec<Error>> {
    let mut result = match lhs {
        Some(expr) => expr.exec(ctxt)?,
        None => ctxt
            .runtime
            .get_history(-1, ctxt.history_position)
            .map(|(_, v, _)| v.clone())
            .ok_or(vec![
                ctxt.make_err("Pipe with no lhs and no previous statement", loc),
            ])?,
    };

    for action in actions {
        result = match action.inner {
            Action::Call(name, args) => {
                ctxt.call(&name.inner, Some(result), args, Vec::new(), action.location)?
            } // TODO reapply in pipe
        }
    }

    Ok(result)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn override_args() {
        let _lock = TEST_FN_LOCK.lock().unwrap();

        let mut rt = crate::Runtime::new_test();
        rt.exec_cmd("$a = `foo`", 0);

        {
            let mut f = TEST_FN.lock().unwrap();
            *f = Some(Box::new(|input, args, _, _| {
                assert_eq!(args.len(), 3);
                assert_eq!(args[0].as_ref().unwrap().expect_str(), "a");
                assert_eq!(args[1].as_ref().unwrap().expect_str(), "b");
                assert!(args[2].is_none());

                assert_eq!(input.to_string(), "foo");
            }));
        }
        rt.exec_cmd("> test(a = 'a', b = 'b')", 1);

        {
            let mut f = TEST_FN.lock().unwrap();
            *f = Some(Box::new(|input, args, _, _| {
                assert_eq!(args.len(), 3);
                assert_eq!(args[0].as_ref().unwrap().expect_str(), "d");
                assert_eq!(args[1].as_ref().unwrap().expect_str(), "b");
                assert_eq!(args[2].as_ref().unwrap().expect_str(), "c");

                assert_eq!(input.to_string(), "foo");
            }));
        }
        rt.exec_cmd("^(a = 'd', c = 'c')", 2);

        // TODO test overriding the input (reapply in pipe)
    }
}
