use std::{collections::HashMap, fs::File, io::read_to_string, sync::LazyLock};

use crate::{
    Data, Error, NumberKind, Value, ValueKind, ValueType, data,
    lang::parse::{Action, Expr, Node, NodeLoc},
};

pub fn help_message_for(cmd: &str) -> String {
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

pub struct Context<'a> {
    pub runtime: &'a crate::Runtime,
    pub src_line: usize,
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
        args: Vec<(Node<String>, Node<Expr>)>,
        loc: NodeLoc,
    ) -> Result<Value, Vec<Error>> {
        // Function lookup.
        let Some(f) = FUNCTIONS.get(fn_name) else {
            return Err(vec![
                self.make_err(&format!("Unknown function name: `{fn_name}`"), loc),
            ]);
        };

        // Check input and args.
        let input = f.type_check_input(lhs, loc, self)?;
        let args = f.type_check_args(args, loc, self)?;

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
                    &format!("`{}` expected {ty} as input, found: `{k}`", self.name),
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
        args: Vec<(Node<String>, Node<Expr>)>,
        loc: NodeLoc,
        ctxt: &mut Context,
    ) -> Result<Vec<Option<ValueKind>>, Vec<Error>> {
        let mut args: Vec<_> = args.into_iter().map(|(n, e)| (n, Some(e))).collect();
        let results: Vec<Result<Option<Value>, Vec<Error>>> = self.args.iter().map(|(n, ty, opt)| {
            let Some(arg) = args.iter_mut().find(|(an, _)| &an.inner == n) else {
                if *opt {
                    return Ok(None);
                } else {
                    return Err(vec![ctxt.make_err(format!("`{}` requires a `{n}` argument but none found", self.name), loc)]);
                }
            };


            let value = arg.1.take().unwrap().exec(ctxt)?;
            value.coerce_to(ty).map_err(|orig| vec![ctxt.make_err(format!("`{}` expects an argument `{n}` with type `{ty}`, but found type `{}`", self.name, orig.ty()), loc)]).map(Some)
        }).collect();

        let (results, errors): (Vec<_>, Vec<_>) = results.into_iter().partition(|r| r.is_ok());
        let mut errors: Vec<_> = errors.into_iter().flat_map(Result::unwrap_err).collect();

        // Check for extra args
        for (l, e) in args {
            if e.is_some() {
                errors.push(ctxt.make_err(
                    &format!("unexpected argument to `{}`: `{}`", self.name, l.inner),
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

    crate::data::reparse::require_reparsed(&data, Some(1), &ctxt.runtime);
    match data {
        Data::Struct(_, r) => {
            let reparsed = &ctxt.runtime.metadata.borrow()[&r].reparsed;
            Ok(Value {
                kind: ValueKind::Number(reparsed.count() as i64),
            })
        }
        Data::Unknown => {
            return Err(vec![ctxt.make_err("unknown data input", loc)]);
        }
        _ => unimplemented!(),
    }
}

fn call_read(
    _: Option<ValueKind>,
    mut args: Vec<Option<ValueKind>>,
    loc: NodeLoc,
    ctxt: &mut Context,
) -> Result<Value, Vec<Error>> {
    let path = args.pop().unwrap().unwrap().expect_str();

    let Ok(file) = File::open(&path) else {
        return Err(vec![
            ctxt.make_err(&format!("could not open file: {path}"), loc),
        ]);
    };

    let Ok(content) = read_to_string(file) else {
        return Err(vec![
            ctxt.make_err(&format!("could not read file: {path}"), loc),
        ]);
    };

    let data = data::parse(&content, ctxt.src_line, &ctxt.runtime)?;
    Ok(Value {
        kind: ValueKind::Data(data),
    })
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
                let data = data::parse(&b, ctxt.src_line, &ctxt.runtime)?;
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
