use std::{collections::HashMap, fs::File, io::read_to_string, sync::LazyLock};

use crate::{
    Error, NumberKind, Value, ValueKind, ValueType,
    data::{self, Data, MetaData, TabularMetaData, Token, reparse::Node as RNode},
    lang::parse::{Action, CmdKind, Expr, Node, NodeLoc, RangeSelector, Selector, SingleSelector},
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
            vec![
                ("depth", ValueType::Number(NumberKind::UInt), true),
                ("width", ValueType::Number(NumberKind::UInt), true),
                ("row_numbers", ValueType::Bool, true),
            ],
            "data > fmt(depth?: int >= 0, width?: int >= 0, row_numbers?: bool) > string",
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
        Function::new(
            "table",
            Some(ValueType::Data),
            vec![("col", ValueType::String, false), ("row", ValueType::String, true)],
            "data > table(col: string, row?: string) > data",
            "parse data into tabular data\nTakes a column separator and an optional row separator (defaults to newlines).",
            &call_table,
        ),
        Function::new(
            "transpose",
            Some(ValueType::Data),
            vec![],
            "data > transpose() > data",
            "swap the rows and columns of a table",
            &call_transpose,
        ),
        Function::new(
            "dbg",
            Some(ValueType::Data),
            vec![],
            "data > read() > string",
            "returns debug information about the input",
            &call_dbg,
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
            "data > test(a: string, b: string, c?: string) > data",
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
                (ValueType::Bool, k @ ValueKind::Bool(_)) => Ok(Some(k)),
                (ty, k) => Err(vec![ctxt.make_err(
                    format!(
                        "`{}` expected {ty} as input, found: `{}`",
                        self.name,
                        crate::ValueDisplay(&Value { kind: k }, ctxt.runtime)
                    ),
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
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let data = lhs.unwrap().expect_data();
    data.resolve_structural(ctxt.runtime);

    let row_numbers = args.pop().unwrap();
    let width = args.pop().unwrap();
    let depth = args.pop().unwrap();

    let mut opts = data::FmtOptions::default();
    if let Some(depth) = depth {
        opts.depth = Some(depth.expect_uint() as usize);
    }

    if let Some(width) = width {
        let width = width.expect_uint();
        if width == 0 {
            opts.truncate = None;
        } else {
            opts.truncate = Some(width as usize);
        }
    }

    if let Some(row_numbers) = row_numbers {
        opts.row_numbers = row_numbers.expect_bool();
    }

    let mut buf = String::new();
    data.fmt(&mut buf, &opts, ctxt.runtime).unwrap();
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
        kind: ValueKind::String(lhs.unwrap().ty().to_string()),
    })
}

fn call_dbg(
    lhs: Option<ValueKind>,
    _args: Vec<Option<ValueKind>>,
    _loc: NodeLoc,
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let data = lhs.unwrap().expect_data();
    data.resolve_structural(ctxt.runtime);
    let reparsed = data::reparse::with_reparsed(&data, None, ctxt.runtime, |reparsed, _| {
        Ok(format!("{reparsed:?}"))
    })?;

    Ok(Value {
        kind: ValueKind::String(format!("{data:?}\n\n{reparsed}")),
    })
}

fn call_count(
    lhs: Option<ValueKind>,
    _: Vec<Option<ValueKind>>,
    _loc: NodeLoc,
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let data = lhs.unwrap().expect_data();
    data.resolve_structural(ctxt.runtime);

    crate::data::reparse::with_reparsed(&data, Some(1), ctxt.runtime, |reparsed, _| {
        Ok(Value {
            kind: ValueKind::Number(reparsed.count() as i64),
        })
    })
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

    Ok(Value {
        kind: ValueKind::Data(Data::new(Some(content), ctxt.runtime)),
    })
}

fn call_table(
    input: Option<ValueKind>,
    mut args: Vec<Option<ValueKind>>,
    _: NodeLoc,
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let data = input.unwrap().expect_data();

    // TODO should check the separator strings are a single character and error if not
    let row = args
        .pop()
        .unwrap()
        .map(|v| v.expect_string().chars().next().unwrap())
        .unwrap_or('\n');
    let col = args
        .pop()
        .unwrap()
        .unwrap()
        .expect_string()
        .chars()
        .next()
        .unwrap();

    data.force_tabular(row, (vec![col], 0), ctxt);
    Ok(Value {
        kind: ValueKind::Data(data),
    })
}

fn call_transpose(
    input: Option<ValueKind>,
    _args: Vec<Option<ValueKind>>,
    loc: NodeLoc,
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let data = input.unwrap().expect_data();
    let Some(result) = data.with_tabular(ctxt.runtime, |data| data.transpose()) else {
        return Err(vec![ctxt.make_err(
            format!("expected tabular data, found: {}", data.ty(ctxt.runtime)),
            loc,
        )]);
    };

    let data = Data::new(None, ctxt.runtime);
    data.with_tabular(ctxt.runtime, move |data| {
        *data = result;
    })
    .unwrap();

    Ok(Value {
        kind: ValueKind::Data(data),
    })
}

#[cfg(test)]
static TEST_FN_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
#[cfg(test)]
#[allow(clippy::type_complexity)]
static TEST_FN: std::sync::Mutex<
    Option<Box<fn(&crate::Data, &[Option<ValueKind>], NodeLoc, &mut Context)>>,
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
                            e => {
                                return Err(vec![ctxt.make_err(
                                    format!(
                                        "Re-applied command is not a function call (found {e:?})"
                                    ),
                                    self.location,
                                )]);
                            }
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
            Expr::Blob(b) => Ok(Value {
                kind: ValueKind::Data(Data::new(Some(b), ctxt.runtime)),
            }),
            Expr::Pipe(lhs, actions) => eval_pipe(lhs, actions, ctxt, self.location),
            Expr::Action(action) => match action {
                Action::Call(name, args) => {
                    ctxt.call(&name.inner, None, args, Vec::new(), self.location)
                }
                Action::Projection(lhs, s) => {
                    let result = lhs.unwrap().exec(ctxt)?;
                    eval_projection(result, s, ctxt, self.location)
                }
                Action::Selection(lhs, s) => {
                    let result = lhs.unwrap().exec(ctxt)?;
                    eval_selection(result, &s, ctxt, self.location)
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
            }
            Action::Projection(_, s) => eval_projection(result, s, ctxt, loc)?,
            Action::Selection(_, s) => eval_selection(result, &s, ctxt, loc)?,
            // TODO reapply in pipe
        }
    }

    Ok(result)
}

fn eval_selection(
    lhs: Value,
    selector: &[Node<RangeSelector>],
    ctxt: &mut Context,
    loc: NodeLoc,
) -> Result<Value, Vec<Error>> {
    let data = match lhs.kind {
        ValueKind::Data(data) => data,
        ValueKind::String(_) => {
            return Err(vec![ctxt.make_err("Cannot select over a string", loc)]);
        }
        ValueKind::Number(_) => {
            return Err(vec![ctxt.make_err("Cannot select over a number", loc)]);
        }
        ValueKind::Bool(_) => {
            return Err(vec![ctxt.make_err("Cannot select over a boolean", loc)]);
        }
        ValueKind::Error => return Ok(Value::new(ValueKind::Error)),
        ValueKind::None => return Ok(lhs),
    };

    match data.ty(ctxt.runtime) {
        data::DataType::Struct | data::DataType::Unknown => {
            data.resolve_structural(ctxt.runtime);
            // TODO implementation
            todo!()
        }
        data::DataType::Tabular => select_tabular(data, selector, ctxt, loc),
        data::DataType::Sequence => todo!(),
        data::DataType::Atom => Err(vec![ctxt.make_err("Cannot select over an atom", loc)]),
    }
}

fn select_tabular(
    data: Data,
    selector: &[Node<RangeSelector>],
    ctxt: &mut Context,
    _loc: NodeLoc,
) -> Result<Value, Vec<Error>> {
    let new_data = data
        .with_tabular(ctxt.runtime, |data| {
            validate_range_selector(selector, data.data.len(), ctxt)?;

            let mut new_data = TabularMetaData::with_capacity(
                selected_len(selector, data.data.len()),
                data.row_sep,
                data.col_sep.clone(),
            );

            for s in selector {
                match &s.inner {
                    RangeSelector::Single(s) => new_data
                        .data
                        .push(data.data[s.unwrap_int() as usize].clone()),
                    RangeSelector::Range(a, b) => {
                        let a = a.as_ref().map(|s| s.unwrap_int() as usize).unwrap_or(0);
                        let b = b
                            .as_ref()
                            .map(|s| s.unwrap_int() as usize)
                            .unwrap_or(data.data.len());
                        new_data.data.extend(data.data[a..b].iter().cloned());
                    }
                }
            }

            Ok::<_, Vec<Error>>(MetaData::Tabular(new_data))
        })
        .unwrap()?;

    let data = Data::new(None, ctxt.runtime);
    data.set_meta_data(new_data, ctxt.runtime);
    Ok(Value::new(ValueKind::Data(data)))
}

fn validate_range_selector(
    selector: &[Node<RangeSelector>],
    rows: usize,
    ctxt: &mut Context,
) -> Result<(), Vec<Error>> {
    fn expect_int(
        s: &SingleSelector,
        ctxt: &mut Context,
        loc: NodeLoc,
    ) -> Result<usize, Vec<Error>> {
        match s {
            SingleSelector::Int(i) if *i >= 0 => Ok(*i as usize),
            _ => Err(vec![ctxt.make_err("Expected numeric selector", loc)]),
        }
    }

    for s in selector {
        match &s.inner {
            RangeSelector::Single(a) => {
                let a = expect_int(a, ctxt, s.location)?;
                if a >= rows {
                    return Err(vec![ctxt.make_err("Out of bounds selector", s.location)]);
                }
            }
            RangeSelector::Range(a, b) => match (a, b) {
                (None, None) => {}
                (None, Some(b)) => {
                    let b = expect_int(b, ctxt, b.location)?;
                    if b > rows {
                        return Err(vec![ctxt.make_err("Out of bounds selector", s.location)]);
                    }
                }
                (Some(a), None) => {
                    let a = expect_int(a, ctxt, a.location)?;
                    if a > rows {
                        return Err(vec![ctxt.make_err("Out of bounds selector", s.location)]);
                    }
                }
                (Some(a), Some(b)) => {
                    let a = expect_int(a, ctxt, a.location)?;
                    let b = expect_int(b, ctxt, b.location)?;
                    if b > rows {
                        return Err(vec![ctxt.make_err("Out of bounds selector", s.location)]);
                    }
                    if b < a {
                        return Err(vec![ctxt.make_err(
                            "End of range must be larger than start of range",
                            s.location,
                        )]);
                    }
                }
            },
        }
    }

    Ok(())
}

/// Precondition: `validate_range_selector(data, rows).is_ok()`
fn selected_len(selector: &[Node<RangeSelector>], rows: usize) -> usize {
    let mut result = 0;

    for s in selector {
        match &s.inner {
            RangeSelector::Single(_) => result += 1,
            RangeSelector::Range(a, b) => {
                let a = a.as_ref().map(|s| s.unwrap_int() as usize).unwrap_or(0);
                let b = b.as_ref().map(|s| s.unwrap_int() as usize).unwrap_or(rows);
                result += b - a;
            }
        }
    }

    result
}

fn eval_projection(
    lhs: Value,
    selector: Node<Selector>,
    ctxt: &mut Context,
    loc: NodeLoc,
) -> Result<Value, Vec<Error>> {
    let data = match lhs.kind {
        ValueKind::Data(data) => data,
        ValueKind::String(_) => {
            return Err(vec![ctxt.make_err("Cannot project over a string", loc)]);
        }
        ValueKind::Number(_) => {
            return Err(vec![ctxt.make_err("Cannot project over a number", loc)]);
        }
        ValueKind::Bool(_) => {
            return Err(vec![ctxt.make_err("Cannot project over a boolean", loc)]);
        }
        ValueKind::Error => return Ok(Value::new(ValueKind::Error)),
        ValueKind::None => return Ok(lhs),
    };

    if selector.inner == Selector::All {
        return Ok(Value::new(ValueKind::Data(data)));
    }

    match data.ty(ctxt.runtime) {
        data::DataType::Struct | data::DataType::Unknown => {
            data.resolve_structural(ctxt.runtime);
            project_structural(data, selector, ctxt)
        }
        data::DataType::Tabular => project_tabular(data, selector, ctxt, loc),
        data::DataType::Atom => Err(vec![ctxt.make_err("Cannot project over an atom", loc)]),
        data::DataType::Sequence => Err(vec![ctxt.make_err("Cannot project over a sequence", loc)]),
    }
}

fn project_structural(
    data: Data,
    selector: Node<Selector>,
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    // TODO depth 2 or 3 or 4?
    let tokens = data::reparse::with_reparsed(&data, Some(4), ctxt.runtime, |reparsed, toks| {
        project_node(reparsed, &selector, toks, ctxt)
    })?;
    if tokens.is_empty() {
        return Ok(Value::new(ValueKind::None));
    }
    let eof = Token::following_eof(tokens.last().unwrap());
    let data = Data::new(None, ctxt.runtime);
    data.resolve_structural_from_tokens(tokens.into_iter().chain(Some(eof)), ctxt.runtime);
    Ok(Value::new(ValueKind::Data(data)))
}

fn project_node(
    node: &RNode,
    selector: &Node<Selector>,
    toks: &[Token],
    _ctxt: &Context,
) -> Result<Vec<Token>, Vec<Error>> {
    match node {
        RNode::List(l) => {
            if let Some(ns) = selector.numeric() {
                // select
                let tokens = ns
                    .into_iter()
                    .filter_map(|n| {
                        let i = if n < 0 {
                            l.children.len() - (-n as usize)
                        } else {
                            n as usize
                        };
                        l.children.get(i)
                    })
                    .flat_map(|n| n.tokens(toks));

                let tokens: Vec<Token> = l
                    .start_tok(toks)
                    .into_iter()
                    .chain(tokens)
                    .chain(l.end_tok(toks))
                    .cloned()
                    .collect();
                Ok(tokens)
            } else {
                // try to select, then fallback to map and recurse
                let mut nodes = l
                    .children
                    .iter()
                    .enumerate()
                    .filter(|(i, n)| selector.matches(n, *i, l.children.len(), toks))
                    .peekable();

                // TODO we should return empty here if tokens is empty, but could have succeeded (i.e., a genuine empty match)
                if nodes.peek().is_some() {
                    // preserve the list boilerplate
                    let tokens: Vec<Token> = l
                        .start_tok(toks)
                        .into_iter()
                        .chain(nodes.flat_map(|(i, _)| l.toks_for(i, toks)))
                        .chain(l.end_tok(toks))
                        .cloned()
                        .collect();
                    return Ok(tokens);
                }

                // map and recurse
                let mut tokens = Vec::new();
                let mut errs = Vec::new();
                for (i, n) in l.children.iter().enumerate() {
                    match project_node(n, selector, toks, _ctxt) {
                        Ok(ts) if ts.is_empty() => continue,
                        Ok(mut ts) => tokens.append(&mut ts),
                        Err(mut es) => errs.append(&mut es),
                    }

                    // Separator
                    if let Some(next) = l.upper_bound(i)
                        && let Some(e) = n.end_token()
                    {
                        tokens.extend(toks[e + 1..next].iter().cloned());
                    }
                }

                if !errs.is_empty() {
                    return Err(errs);
                }
                let tokens: Vec<Token> = l
                    .start_tok(toks)
                    .into_iter()
                    .cloned()
                    .chain(tokens)
                    .chain(l.end_tok(toks).into_iter().cloned())
                    .collect();
                Ok(tokens)
            }
        }
        // Skip over details to get to a list e.g., `foo { ... }`
        RNode::Group(nodes) => {
            // Try to find a list node to project, skipping up to 3 real nodes.
            let mut list_index = None;
            let mut skipped = 0;
            for (i, n) in nodes.iter().enumerate() {
                match n {
                    // Just ignore these nodes
                    RNode::Error(_) | RNode::None => continue,
                    RNode::List(_) => {
                        list_index = Some(i);
                        break;
                    }
                    RNode::Todo | RNode::Group(_) | RNode::Pair(..) | RNode::Atom(..) => {
                        skipped += 1
                    }
                }

                if skipped >= 3 {
                    break;
                }
            }

            let Some(list_index) = list_index else {
                return Ok(Vec::new());
            };

            let node_toks = project_node(&nodes[list_index], selector, toks, _ctxt)?;

            // toks for before and after nodes
            let start_toks = if list_index != 0
                && let Some(first_range) = nodes[0].token_range()
                && let Some(node_range) = nodes[list_index].token_range()
            {
                &toks[*first_range.start()..*node_range.start()]
            } else {
                &[]
            };
            let end_toks: &[Token] = if list_index < nodes.len() - 1
                && let Some(last_range) = nodes[nodes.len() - 1].token_range()
                && let Some(node_range) = nodes[list_index].token_range()
            {
                &toks[*node_range.end()..*last_range.end()]
            } else {
                &[]
            };

            Ok(start_toks
                .iter()
                .cloned()
                .chain(node_toks)
                .chain(end_toks.iter().cloned())
                .collect())
        }
        _ => Ok(Vec::new()),
    }
}

fn project_tabular(
    data: Data,
    selector: Node<Selector>,
    ctxt: &mut Context,
    loc: NodeLoc,
) -> Result<Value, Vec<Error>> {
    // TODO accept column names as well as numbers
    let Some(columns) = selector.numeric() else {
        return Err(vec![ctxt.make_err(
            "Tabular data can only be projected with column numbers",
            loc,
        )]);
    };

    let new_data = data
        .with_tabular(ctxt.runtime, |data| {
            let mut new_data =
                TabularMetaData::with_capacity(data.data.len(), data.row_sep, data.col_sep.clone());

            if data.data.is_empty() {
                return Ok(MetaData::Tabular(new_data));
            }

            for c in &columns {
                if *c < 0 || *c >= data.data[0].len() as i64 {
                    return Err(vec![ctxt.make_err(
                        format!(
                            "Projection index out of bounds. Found: {}, expected: 0..{}",
                            *c,
                            data.data[0].len()
                        ),
                        loc,
                    )]);
                }
            }

            for r in &data.data {
                let mut row = Vec::with_capacity(columns.len());
                for c in &columns {
                    row.push(r[*c as usize].clone());
                }
                new_data.data.push(row);
            }

            Ok(MetaData::Tabular(new_data))
        })
        .unwrap()?;

    let data = Data::new(None, ctxt.runtime);
    data.set_meta_data(new_data, ctxt.runtime);
    Ok(Value::new(ValueKind::Data(data)))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::lang::{
        lex::Lexer,
        parse::{CommandParser, SingleSelector},
    };

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

                assert_eq!(input.raw.as_deref().unwrap(), "foo");
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

                assert_eq!(input.raw.as_deref().unwrap(), "foo");
            }));
        }
        rt.exec_cmd("^(a = 'd', c = 'c')", 2);

        // TODO test overriding the input (reapply in pipe)
    }

    #[test]
    fn project_index() {
        // TODO test on other kinds of sequences
        let runtime = &crate::Runtime::new_test();
        let (mut ctxt, data) = init(
            r#"Command {
    source: "$foo = $bar",
    kind: Assign(
        Some(
            "foo",
        ),
        Var(
            "bar",
        ),
    ),
    line: 0,
}
Command {
    source: "$foo",
    kind: Echo(
        Var(
            "foo\n",
        ),
    ),
    line: 0,
}"#,
            runtime,
        );

        // Selector::All
        let result = eval_project(&data, Selector::All, &mut ctxt);
        assert_eq!(result.kind.expect_data(), data);

        // Out of bounds selector
        let result = eval_project(&data, Selector::int(2), &mut ctxt);
        std::assert_matches::assert_matches!(result.kind, ValueKind::None);

        // In bounds selector
        let result = eval_project(&data, Selector::int(1), &mut ctxt);
        assert_eq_reloc(
            result,
            r#"Command {
    source: "$foo",
    kind: Echo(
        Var(
            "foo\n",
        ),
    ),
    line: 0,
}"#,
            runtime,
        );

        // Multiple selector, just one
        let result = eval_project(
            &data,
            Selector::Seq(vec![Node::new(SingleSelector::Int(1), 0, 0)]),
            &mut ctxt,
        );
        assert_eq_reloc(
            result,
            r#"Command {
    source: "$foo",
    kind: Echo(
        Var(
            "foo\n",
        ),
    ),
    line: 0,
}"#,
            runtime,
        );

        // Multiple selector, both
        let result = eval_project(
            &data,
            Selector::Seq(vec![
                Node::new(SingleSelector::Int(0), 0, 0),
                Node::new(SingleSelector::Int(1), 0, 0),
            ]),
            &mut ctxt,
        );
        let result = result.kind.expect_data();
        runtime.with_meta_datas(&[result.meta, data.meta], |meta| {
            assert!(
                meta[0].eq_reloc(meta[1]),
                "Not equal:\n{}\n\n{}",
                &meta[0],
                &meta[1]
            );
        });
    }

    #[test]
    fn project_named_select() {
        let runtime = &crate::Runtime::new_test();
        let (mut ctxt, data) = init(
            r#"{
    source: "$foo = $bar",
    kind: Assign(
        Some(
            "foo",
        ),
        Var(
            "bar",
        ),
    ),
    line: 0,
}"#,
            runtime,
        );

        // Unknown selector
        let result = eval_project(&data, Selector::ident("foo".to_owned()), &mut ctxt);
        assert_eq_reloc(result, r#"{}"#, runtime);

        // Known selector
        let result = eval_project(&data, Selector::ident("kind".to_owned()), &mut ctxt);
        assert_eq_reloc(
            result,
            r#"{
    kind: Assign(
        Some(
            "foo",
        ),
        Var(
            "bar",
        ),
    ),
}"#,
            runtime,
        );

        // Multiple selectors
        let result = eval_project(
            &data,
            Selector::Seq(vec![
                Node::new(SingleSelector::Ident("source".to_owned()), 0, 0),
                Node::new(SingleSelector::Ident("line".to_owned()), 0, 0),
            ]),
            &mut ctxt,
        );
        assert_eq_reloc(
            result,
            r#"{
    source: "$foo = $bar",
    line: 0,
}"#,
            runtime,
        );

        // With a name before the struct
        let (mut ctxt, data) = init(
            r#"Command {
    source: "$foo = $bar",
    kind: Assign(
        Some(
            "foo",
        ),
        Var(
            "bar",
        ),
    ),
    line: 0,
}"#,
            runtime,
        );

        // Unknown selector
        let result = eval_project(&data, Selector::ident("foo".to_owned()), &mut ctxt);
        assert_eq_reloc(result, r#"Command {}"#, runtime);

        // Known selector
        let result = eval_project(&data, Selector::ident("kind".to_owned()), &mut ctxt);
        assert_eq_reloc(
            result,
            r#"Command {
    kind: Assign(
        Some(
            "foo",
        ),
        Var(
            "bar",
        ),
    ),
}"#,
            runtime,
        );

        // Multiple selectors
        let result = eval_project(
            &data,
            Selector::Seq(vec![
                Node::new(SingleSelector::Ident("source".to_owned()), 0, 0),
                Node::new(SingleSelector::Ident("line".to_owned()), 0, 0),
            ]),
            &mut ctxt,
        );
        assert_eq_reloc(
            result,
            r#"Command {
    source: "$foo = $bar",
    line: 0,
}"#,
            runtime,
        );
    }

    #[test]
    fn project_named_mapped() {
        let runtime = &crate::Runtime::new_test();
        let (mut ctxt, data) = init(
            r#"Command {
    source: "$foo = $bar",
    kind: Assign(
        Some(
            "foo",
        ),
        Var(
            "bar",
        ),
    ),
    line: 0,
}
Command {
    source: "$foo",
    kind: Echo(
        Var(
            "foo\n",
        ),
    ),
    line: 0,
}"#,
            runtime,
        );

        // One mapped selector
        let result = eval_project(&data, Selector::ident("kind".to_owned()), &mut ctxt);
        assert_eq_reloc(
            result,
            r#"Command {
    kind: Assign(
        Some(
            "foo",
        ),
        Var(
            "bar",
        ),
    ),
}
Command {
    kind: Echo(
        Var(
            "foo\n",
        ),
    ),
}"#,
            runtime,
        );

        // multiple mapped selectors
        let result = eval_project(
            &data,
            Selector::Seq(vec![
                Node::new(SingleSelector::Ident("source".to_owned()), 0, 0),
                Node::new(SingleSelector::Ident("line".to_owned()), 0, 0),
            ]),
            &mut ctxt,
        );
        assert_eq_reloc(
            result,
            r#"Command {
    source: "$foo = $bar",
    line: 0,
}
Command {
    source: "$foo",
    line: 0,
}"#,
            runtime,
        );

        let (mut ctxt, data) = init(
            r#"[Command {
    source: "$foo = $bar",
    kind: Assign(
        Some(
            "foo",
        ),
        Var(
            "bar",
        ),
    ),
    line: 0,
},
Command {
    source: "$foo",
    kind: Echo(
        Var(
            "foo\n",
        ),
    ),
    line: 0,
}]"#,
            runtime,
        );

        // One mapped selector
        let result = eval_project(&data, Selector::ident("kind".to_owned()), &mut ctxt);
        assert_eq_reloc(
            result,
            r#"[Command {
    kind: Assign(
        Some(
            "foo",
        ),
        Var(
            "bar",
        ),
    ),
},
Command {
    kind: Echo(
        Var(
            "foo\n",
        ),
    ),
}]"#,
            runtime,
        );

        // multiple mapped selectors
        let result = eval_project(
            &data,
            Selector::Seq(vec![
                Node::new(SingleSelector::Ident("source".to_owned()), 0, 0),
                Node::new(SingleSelector::Ident("line".to_owned()), 0, 0),
            ]),
            &mut ctxt,
        );
        assert_eq_reloc(
            result,
            r#"[Command {
    source: "$foo = $bar",
    line: 0,
},
Command {
    source: "$foo",
    line: 0,
}]"#,
            runtime,
        );
    }

    #[test]
    fn project_tabular_index() {
        let runtime = &crate::Runtime::new_test();
        let (mut ctxt, data) = init_tabular(
            r#"a | b | c | d
e | f | g | h
i | j | k | l"#,
            runtime,
        );

        // Selector::All
        let result = eval_project(&data, Selector::All, &mut ctxt);
        assert_eq!(result.kind.expect_data(), data);

        // Out of bounds selector
        let result = eval_projection(
            Value::new(ValueKind::Data(data.clone())),
            Node::new(Selector::int(4), 0, 0),
            &mut ctxt,
            NodeLoc { char: 0, len: 0 },
        );
        assert!(result.is_err());

        // In bounds selector
        let result = eval_project(&data, Selector::int(1), &mut ctxt);
        assert_eq_tabular(
            result, r#"b
f
j"#, runtime,
        );

        // Multiple selector, just one
        let result = eval_project(
            &data,
            Selector::Seq(vec![Node::new(SingleSelector::Int(1), 0, 0)]),
            &mut ctxt,
        );
        assert_eq_tabular(
            result, r#"b
f
j"#, runtime,
        );

        // Multiple selector
        let result = eval_project(
            &data,
            Selector::Seq(vec![
                Node::new(SingleSelector::Int(1), 0, 0),
                Node::new(SingleSelector::Int(3), 0, 0),
            ]),
            &mut ctxt,
        );
        assert_eq_tabular(
            result,
            r#"b | d
f | h
j | l"#,
            runtime,
        );

        // Multiple selector, with reordering
        let result = eval_project(
            &data,
            Selector::Seq(vec![
                Node::new(SingleSelector::Int(3), 0, 0),
                Node::new(SingleSelector::Int(2), 0, 0),
            ]),
            &mut ctxt,
        );
        assert_eq_tabular(
            result,
            r#"d | c
h | g
l | k"#,
            runtime,
        );

        // Multiple selector, all
        let result = eval_project(
            &data,
            Selector::Seq(vec![
                Node::new(SingleSelector::Int(0), 0, 0),
                Node::new(SingleSelector::Int(1), 0, 0),
                Node::new(SingleSelector::Int(2), 0, 0),
                Node::new(SingleSelector::Int(3), 0, 0),
            ]),
            &mut ctxt,
        );
        let result = result.kind.expect_data();
        runtime.with_meta_datas(&[result.meta, data.meta], |meta| {
            assert!(
                meta[0].eq_reloc(meta[1]),
                "Not equal:\n{}\n\n{}",
                &meta[0],
                &meta[1]
            );
        });
    }

    #[track_caller]
    fn init<'a>(code: &str, runtime: &'a crate::Runtime) -> (Context<'a>, Data) {
        let data = Data::new(Some(code.to_owned()), runtime);
        data.resolve_structural(runtime);

        let ctxt = Context {
            runtime,
            src_line: 0,
            history_position: 0,
        };

        (ctxt, data)
    }

    #[track_caller]
    fn init_tabular<'a>(code: &str, runtime: &'a crate::Runtime) -> (Context<'a>, Data) {
        let ctxt = Context {
            runtime,
            src_line: 0,
            history_position: 0,
        };

        let data = Data::new(Some(code.to_owned()), runtime);
        data.force_tabular('\n', (vec!['|'], 0), &ctxt);

        (ctxt, data)
    }

    #[track_caller]
    fn eval_project(data: &crate::Data, selector: Selector, ctxt: &mut Context) -> Value {
        eval_projection(
            Value::new(ValueKind::Data(data.clone())),
            Node::new(selector, 0, 0),
            ctxt,
            NodeLoc { char: 0, len: 0 },
        )
        .unwrap()
    }

    #[track_caller]
    fn assert_eq_reloc(result: Value, expected: &str, runtime: &crate::Runtime) {
        let data1 = crate::data::parse_structural(expected).unwrap().unwrap();

        let result = result.kind.expect_data();
        runtime.with_meta_data(result.meta, |meta| {
            assert!(
                meta.eq_reloc(&data::MetaData::Struct(data1.clone())),
                "Not equal:\n{}\n\n{}",
                meta,
                data::MetaData::Struct(data1)
            );
        });
    }

    #[track_caller]
    fn assert_eq_tabular(result: Value, expected: &str, runtime: &crate::Runtime) {
        let expected = crate::data::parse_tabular(expected, '\n', (vec!['|'], 0));

        let result = result.kind.expect_data();
        runtime.with_meta_data(result.meta, |meta| {
            assert!(
                meta.eq_reloc(&data::MetaData::Tabular(expected.clone())),
                "Not equal:\n{}\n\n{}",
                meta,
                data::MetaData::Tabular(expected)
            );
        });
    }

    #[test]
    fn select_tabular() {
        let runtime = &crate::Runtime::new_test();
        let (mut ctxt, data) = init_tabular(
            r#"a | b | c | d
e | f | g | h
i | j | k | l
m | n | o | p
q | r | s | t"#,
            runtime,
        );

        // Single row selection
        let result = eval_select(&data, "0", &mut ctxt);
        assert_eq_tabular(result, r#"a | b | c | d"#, runtime);

        let result = eval_select(&data, "2", &mut ctxt);
        assert_eq_tabular(result, r#"i | j | k | l"#, runtime);

        // Range selection - both bounds
        let result = eval_select(&data, "0..2", &mut ctxt);
        assert_eq_tabular(
            result,
            r#"a | b | c | d
e | f | g | h"#,
            runtime,
        );

        let result = eval_select(&data, "1..4", &mut ctxt);
        assert_eq_tabular(
            result,
            r#"e | f | g | h
i | j | k | l
m | n | o | p"#,
            runtime,
        );

        // Range selection - only start
        let result = eval_select(&data, "3..", &mut ctxt);
        assert_eq_tabular(
            result,
            r#"m | n | o | p
q | r | s | t"#,
            runtime,
        );

        // Range selection - only end
        let result = eval_select(&data, "..3", &mut ctxt);
        assert_eq_tabular(
            result,
            r#"a | b | c | d
e | f | g | h
i | j | k | l"#,
            runtime,
        );

        // Range selection - all rows
        let result = eval_select(&data, "..", &mut ctxt);
        let result_data = result.kind.expect_data();
        runtime.with_meta_datas(&[result_data.meta, data.meta], |meta| {
            assert!(
                meta[0].eq_reloc(meta[1]),
                "Not equal:\n{}\n\n{}",
                &meta[0],
                &meta[1]
            );
        });

        // Multiple single selectors
        let result = eval_select(&data, "0, 2, 4", &mut ctxt);
        assert_eq_tabular(
            result,
            r#"a | b | c | d
i | j | k | l
q | r | s | t"#,
            runtime,
        );

        // Mixed selectors - single and range
        let result = eval_select(&data, "0, 2..4", &mut ctxt);
        assert_eq_tabular(
            result,
            r#"a | b | c | d
i | j | k | l
m | n | o | p"#,
            runtime,
        );

        // Multiple ranges
        let result = eval_select(&data, "0..2, 3..5", &mut ctxt);
        assert_eq_tabular(
            result,
            r#"a | b | c | d
e | f | g | h
m | n | o | p
q | r | s | t"#,
            runtime,
        );

        // Out of order selection
        let result = eval_select(&data, "4, 2, 0", &mut ctxt);
        assert_eq_tabular(
            result,
            r#"q | r | s | t
i | j | k | l
a | b | c | d"#,
            runtime,
        );

        // Duplicate selections
        let result = eval_select(&data, "1, 1", &mut ctxt);
        assert_eq_tabular(
            result,
            r#"e | f | g | h
e | f | g | h"#,
            runtime,
        );

        // Empty range (start == end)
        let result = eval_select(&data, "2..2", &mut ctxt);
        let result = result.kind.expect_data();
        runtime.with_meta_data(result.meta, |meta| {
            assert!(meta.eq_reloc(&data::MetaData::Tabular(TabularMetaData::new(
                '\n',
                (vec!['|'], 0)
            ))),);
        });
    }

    #[track_caller]
    fn eval_select(data: &crate::Data, selector: &str, ctxt: &mut Context) -> Value {
        let selector = parse_ranges(selector);
        eval_selection(
            Value::new(ValueKind::Data(data.clone())),
            &selector,
            ctxt,
            NodeLoc { char: 0, len: 0 },
        )
        .unwrap()
    }

    fn parse_ranges(r: &str) -> Vec<Node<RangeSelector>> {
        let src = format!("[{r}]");
        let lexer = Lexer::new(src.chars());
        let mut parser = CommandParser::new(lexer);
        match parser.selection(None).unwrap().inner {
            Action::Selection(_, ranges) => ranges,
            _ => unreachable!(),
        }
    }

    #[test]
    fn range_selector_len() {
        let selector = parse_ranges("..");
        assert_eq!(selected_len(&selector, 0), 0);
        assert_eq!(selected_len(&selector, 3), 3);

        let selector = parse_ranges("0..");
        assert_eq!(selected_len(&selector, 0), 0);
        assert_eq!(selected_len(&selector, 3), 3);
        let selector = parse_ranges("2..");
        assert_eq!(selected_len(&selector, 2), 0);
        assert_eq!(selected_len(&selector, 3), 1);
        let selector = parse_ranges("..2");
        assert_eq!(selected_len(&selector, 2), 2);
        assert_eq!(selected_len(&selector, 3), 2);
        let selector = parse_ranges("..0");
        assert_eq!(selected_len(&selector, 0), 0);
        let selector = parse_ranges("0..0");
        assert_eq!(selected_len(&selector, 0), 0);
        let selector = parse_ranges("0..3");
        assert_eq!(selected_len(&selector, 3), 3);
        assert_eq!(selected_len(&selector, 5), 3);
        let selector = parse_ranges("2..5");
        assert_eq!(selected_len(&selector, 5), 3);
        let selector = parse_ranges("2..2");
        assert_eq!(selected_len(&selector, 5), 0);

        let selector = parse_ranges(".., .., 0..0");
        assert_eq!(selected_len(&selector, 0), 0);
        assert_eq!(selected_len(&selector, 3), 6);
        let selector = parse_ranges("1..3, 2..5");
        assert_eq!(selected_len(&selector, 5), 5);
    }

    #[test]
    fn test_validate_range_selector() {
        let mut ctxt = Context {
            runtime: &crate::Runtime::new_test(),
            src_line: 0,
            history_position: 0,
        };

        let selector = parse_ranges("..");
        validate_range_selector(&selector, 0, &mut ctxt).unwrap();
        validate_range_selector(&selector, 42, &mut ctxt).unwrap();

        // Single ranges - valid
        let selector = parse_ranges("0");
        validate_range_selector(&selector, 5, &mut ctxt).unwrap();
        let selector = parse_ranges("3");
        validate_range_selector(&selector, 5, &mut ctxt).unwrap();
        let selector = parse_ranges("4");
        validate_range_selector(&selector, 5, &mut ctxt).unwrap();

        // Multiple ranges - valid
        let selector = parse_ranges("0, 2, 4");
        validate_range_selector(&selector, 5, &mut ctxt).unwrap();
        let selector = parse_ranges("0..2, 3");
        validate_range_selector(&selector, 5, &mut ctxt).unwrap();
        let selector = parse_ranges("1, 2..4");
        validate_range_selector(&selector, 5, &mut ctxt).unwrap();
        let selector = parse_ranges("0..2, 3..5");
        validate_range_selector(&selector, 5, &mut ctxt).unwrap();

        // Multiple ranges, out of order - valid (order doesn't matter for validation)
        let selector = parse_ranges("4, 2, 0");
        validate_range_selector(&selector, 5, &mut ctxt).unwrap();
        let selector = parse_ranges("3..5, 0..2");
        validate_range_selector(&selector, 5, &mut ctxt).unwrap();

        // Error: out of bounds single/multiple selector
        let selector = parse_ranges("5");
        assert!(validate_range_selector(&selector, 5, &mut ctxt).is_err());
        let selector = parse_ranges("10");
        assert!(validate_range_selector(&selector, 5, &mut ctxt).is_err());
        let selector = parse_ranges("0, 5");
        assert!(validate_range_selector(&selector, 5, &mut ctxt).is_err());

        // Error: out of bounds range selector (end)
        let selector = parse_ranges("0..6");
        assert!(validate_range_selector(&selector, 5, &mut ctxt).is_err());
        let selector = parse_ranges("..6");
        assert!(validate_range_selector(&selector, 5, &mut ctxt).is_err());

        // Error: out of bounds range selector (start)
        let selector = parse_ranges("6..");
        assert!(validate_range_selector(&selector, 5, &mut ctxt).is_err());
        let selector = parse_ranges("6..10");
        assert!(validate_range_selector(&selector, 5, &mut ctxt).is_err());

        // Error: range where end < start
        let selector = parse_ranges("3..1");
        assert!(validate_range_selector(&selector, 5, &mut ctxt).is_err());
        let selector = parse_ranges("4..2");
        assert!(validate_range_selector(&selector, 5, &mut ctxt).is_err());
    }
}
