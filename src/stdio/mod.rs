use std::{
    io::{self, Read, Write},
    sync::mpsc::{self, Receiver, TryRecvError},
    thread,
    time::Duration,
};

use io_streams::StreamReader;

const PROMPT: &str = "> ";

pub fn start() {
    println!();
    println!();
    println!("plob");
    println!("Use `h` for help, `q` to quit.");

    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        // TODO go back to just using stdin
        let mut stdin = StreamReader::stdin().unwrap();
        let mut buffer = [0; 1024];
        loop {
            let n = stdin.read(&mut buffer).unwrap();
            let s = std::str::from_utf8(&buffer[..n]).unwrap();
            tx.send(s.to_owned()).unwrap();
        }
    });

    let mut handler = StdioHandler::new(rx);
    handler.main_loop();
}

#[derive(Debug)]
struct StdioHandler {
    recv: Receiver<String>,
    source: Vec<String>,
    runtime: crate::Runtime,
}

#[derive(Debug)]
struct StdoutReporter {}

impl crate::Report for StdoutReporter {
    fn echo(&self, s: &str) {
        println!("{s}");
    }

    fn report_err(&self, err: &crate::Error) {
        println!("Error: {}", err.msg);
    }
}

impl StdioHandler {
    fn new(recv: Receiver<String>) -> Self {
        StdioHandler {
            recv,
            runtime: crate::Runtime::new(Box::new(StdoutReporter {})),
            source: Vec::new(),
        }
    }

    fn main_loop(&mut self) {
        loop {
            print!("{PROMPT}");
            io::stdout().flush().unwrap();

            let mut buf = String::new();
            let mut state = 0;
            loop {
                match self.recv.try_recv() {
                    Ok(line) => {
                        buf.push_str(&line);
                        if state == 1 {
                            state = 2;
                        }
                    }
                    Err(TryRecvError::Empty) => {
                        if !buf.is_empty() {
                            if state == 2 || !buf[..buf.len() - 1].contains('\n') {
                                break;
                            }
                            state = 1;
                        }
                        thread::sleep(Duration::from_millis(100));
                    }
                    Err(TryRecvError::Disconnected) => return,
                }
            }

            match self.handle_line(buf.trim()) {
                Action::None => {}
                Action::Quit => return,
            }
            buf.clear();
        }
    }

    fn handle_line(&mut self, line: &str) -> Action {
        match line.chars().next() {
            None => return Action::None,
            Some('q') => return Action::Quit,
            Some('h') => {
                print_help();
                return Action::None;
            }
            _ => {}
        }

        self.source.push(line.to_owned());

        self.runtime.exec_cmd(line, self.source.len() - 1);
        Action::None
    }
}

enum Action {
    None,
    Quit,
}

fn print_help() {
    println!(
        r#"
plob

# Commands

q           quit
h           display this help message
"#
    );
}
