use std::{collections::HashMap, fs::File, io::read_to_string, sync::LazyLock};

use crate::{
    Error, NumberKind, Value, ValueKind, ValueType,
    data::{self, Data, Token, reparse::Node as RNode},
    lang::parse::{Action, CmdKind, Expr, Node, NodeLoc, Selector},
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
            vec![("depth", ValueType::Number(NumberKind::UInt), true), ("width", ValueType::Number(NumberKind::UInt), true)],
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
        Function::new(
            "table",
            Some(ValueType::Data),
            vec![("col", ValueType::String, false), ("row", ValueType::String, true)],
            "data > table(col: string, row?: string) > data",
            "parse data into tabular data\nTakes a column separator and an optional row separator (defaults to newlines).",
            &call_table,
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
    let width = args.pop().unwrap();
    let depth = args.pop().unwrap();

    let mut opts = data::FmtOptions::default();
    if let Some(depth) = depth {
        opts.depth = Some(depth.expect_uint() as usize);
    }
    // TODO support non-0 widths (0 means don't truncate).
    if let Some(width) = width
        && width.expect_uint() == 0
    {
        opts.truncate = false;
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

#[cfg(test)]
static TEST_FN_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
#[cfg(test)]
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
            // TODO reapply in pipe
        }
    }

    Ok(result)
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
        ValueKind::Error => return Ok(Value::new(ValueKind::Error)),
        ValueKind::None => return Ok(lhs),
    };
    data.resolve_structural(ctxt.runtime);

    if selector.inner == Selector::All {
        return Ok(Value::new(ValueKind::Data(data)));
    }

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
        let result = eval_project(&data, Selector::Int(2), &mut ctxt);
        std::assert_matches::assert_matches!(result.kind, ValueKind::None);

        // In bounds selector
        let result = eval_project(&data, Selector::Int(1), &mut ctxt);
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
            Selector::Seq(vec![Node::new(Selector::Int(1), 0, 0)]),
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
                Node::new(Selector::Int(0), 0, 0),
                Node::new(Selector::Int(1), 0, 0),
            ]),
            &mut ctxt,
        );
        let result = result.kind.expect_data();
        runtime.with_meta_datas(&[result.meta, data.meta], |meta| {
            assert!(
                meta[0].eq_reloc(&meta[1]),
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
        let result = eval_project(&data, Selector::Ident("foo".to_owned()), &mut ctxt);
        assert_eq_reloc(result, r#"{}"#, runtime);

        // Known selector
        let result = eval_project(&data, Selector::Ident("kind".to_owned()), &mut ctxt);
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
                Node::new(Selector::Ident("source".to_owned()), 0, 0),
                Node::new(Selector::Ident("line".to_owned()), 0, 0),
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
        let result = eval_project(&data, Selector::Ident("foo".to_owned()), &mut ctxt);
        assert_eq_reloc(result, r#"Command {}"#, runtime);

        // Known selector
        let result = eval_project(&data, Selector::Ident("kind".to_owned()), &mut ctxt);
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
                Node::new(Selector::Ident("source".to_owned()), 0, 0),
                Node::new(Selector::Ident("line".to_owned()), 0, 0),
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
        let result = eval_project(&data, Selector::Ident("kind".to_owned()), &mut ctxt);
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
                Node::new(Selector::Ident("source".to_owned()), 0, 0),
                Node::new(Selector::Ident("line".to_owned()), 0, 0),
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
        let result = eval_project(&data, Selector::Ident("kind".to_owned()), &mut ctxt);
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
                Node::new(Selector::Ident("source".to_owned()), 0, 0),
                Node::new(Selector::Ident("line".to_owned()), 0, 0),
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
}
