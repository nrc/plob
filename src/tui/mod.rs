// TODO use Cargo features to enable tui

use std::{cell::RefCell, error::Error, io::stdout, rc::Rc, time::Duration};

use crossterm::event::{
    self, EnableBracketedPaste, Event, KeyCode, KeyEvent, KeyEventKind, KeyModifiers,
    KeyboardEnhancementFlags, PopKeyboardEnhancementFlags, PushKeyboardEnhancementFlags,
};
use ratatui::{
    style::{Color, Style},
    text::{Span, Text},
    widgets::{Paragraph, Wrap},
};

use crate::Report;

pub fn start() {
    Tui::new().run();
    ratatui::restore();
}

#[derive(Debug)]
struct Tui {
    running: bool,
    buffer: String,
    cursor_position: usize,
    cur_line: String,

    source_lines: Vec<String>,
    pending_output: Rc<RefCell<String>>,
    runtime: crate::Runtime,
}

impl Tui {
    fn new() -> Self {
        let pending_output = Rc::new(RefCell::new(String::new()));

        Tui {
            running: false,
            buffer: String::new(),
            cursor_position: 0,
            cur_line: String::new(),
            source_lines: Vec::new(),
            runtime: crate::Runtime::new(Box::new(pending_output.clone())),
            pending_output,
        }
    }

    fn run(mut self) {
        let mut terminal = ratatui::init();

        crossterm::execute!(
            stdout(),
            PushKeyboardEnhancementFlags(
                KeyboardEnhancementFlags::DISAMBIGUATE_ESCAPE_CODES
                    .union(KeyboardEnhancementFlags::REPORT_ALL_KEYS_AS_ESCAPE_CODES)
            )
        )
        .unwrap();
        crossterm::execute!(stdout(), EnableBracketedPaste,).unwrap();

        struct TidyUp;
        impl Drop for TidyUp {
            fn drop(&mut self) {
                crossterm::execute!(stdout(), PopKeyboardEnhancementFlags).unwrap();
            }
        }
        let _tidy = TidyUp;

        self.running = true;
        self.buffer
            .push_str("plob\n\nUse `h` for help, `q` to quit.\n");
        self.print_prompt();

        while self.running {
            if let Err(e) = terminal.draw(|frame| self.render(frame)) {
                eprintln!("Error drawing terminal: {}", e);
                break;
            }
            if let Err(e) = self.handle_crossterm_events() {
                eprintln!("Error handling events: {}", e);
                break;
            }
        }
    }

    fn print_prompt(&mut self) {
        self.buffer.push_str("\n> ");
    }

    fn print(&mut self, s: &str) {
        self.buffer.push('\n');
        self.buffer.push_str(s);
    }

    fn render(&self, frame: &mut ratatui::Frame) {
        let area = frame.area();
        let mut text = Text::from(&*self.buffer);

        let mut chars = 0;
        let mut rendered_cursor = false;
        let mut first = true;

        for line in self.cur_line.lines() {
            if !first {
                chars += 1;
                text.push_line("");
            } else {
                first = false;
            }

            if self.cursor_position < chars || self.cursor_position - chars > line.len() {
                text.push_span(line);
            } else if self.cursor_position == line.len() + chars {
                text.push_span(line);
                text.push_span(Span::from(" ").style(Style::new().bg(Color::Gray)));
                rendered_cursor = true;
            } else {
                let cpos = self.cursor_position - chars;
                text.push_span(&line[..cpos]);
                text.push_span(Span::from(&line[cpos..=cpos]).style(Style::new().bg(Color::Gray)));
                text.push_span(&line[cpos + 1..]);
                rendered_cursor = true;
            }
            chars += line.len();
        }
        if self.cur_line.ends_with('\n') {
            text.push_line("");
        }
        if !rendered_cursor {
            // The dot should be invisible since it's the same colour as the background,
            // but we need to use a dot rather than a space since there seems to be a bug
            // where starting a newline with a space (or maybe only if the whole line is a
            // space) produces a double newline rather than just one.
            text.push_span(Span::from(".").style(Style::new().bg(Color::Gray)));
        }

        let para = Paragraph::new(text).wrap(Wrap { trim: false });
        frame.render_widget(para, area);
    }

    fn handle_crossterm_events(&mut self) -> Result<(), Box<dyn Error>> {
        if !event::poll(Duration::from_millis(16))? {
            return Ok(());
        }
        match event::read()? {
            Event::Key(key) if key.kind == KeyEventKind::Press => self.on_key_event(key),
            Event::Paste(s) => {
                self.cur_line.insert_str(self.cursor_position, &s);
                self.cursor_position += s.len();
            }
            Event::Mouse(_) => {}
            Event::Resize(_, _) => {}
            _ => {}
        }
        Ok(())
    }

    fn on_key_event(&mut self, key: KeyEvent) {
        match (key.modifiers, key.code) {
            // Escape or Ctrl+C to clear the line and start again
            (_, KeyCode::Esc)
            | (KeyModifiers::CONTROL, KeyCode::Char('c') | KeyCode::Char('C')) => {
                self.cur_line.clear();
                self.cursor_position = 0;
            }
            (KeyModifiers::SHIFT, KeyCode::Enter) => {
                self.cur_line.insert(self.cursor_position, '\n');
                self.cursor_position += 1;
            }
            (_, KeyCode::Enter) => self.on_enter(),
            (_, KeyCode::Backspace) => {
                if self.cursor_position > 0 {
                    if self.cursor_position >= self.cur_line.len() {
                        self.cur_line.pop();
                    } else {
                        self.cur_line
                            .replace_range(self.cursor_position - 1..self.cursor_position, "");
                    }
                    self.cursor_position -= 1;
                }
            }
            (_, KeyCode::Delete) => {
                if self.cursor_position < self.cur_line.len() {
                    self.cur_line
                        .replace_range(self.cursor_position..=self.cursor_position, "");
                }
            }
            // Cursor keys
            (_, KeyCode::Left) if self.cursor_position > 0 => self.cursor_position -= 1,
            (_, KeyCode::Right) if self.cursor_position < self.cur_line.len() => {
                self.cursor_position += 1
            }
            // TODO up and down arrows
            // TODO? undo, redo

            // Typing characters
            (_, KeyCode::Char(c)) => {
                self.cur_line.insert(self.cursor_position, c);
                self.cursor_position += 1;
            }
            _ => {}
        }
    }

    fn on_enter(&mut self) {
        if self.cur_line.is_empty() {
            self.print_prompt();
            return;
        }
        self.buffer.push_str(&self.cur_line);
        self.handle_line();

        let output = self.pending_output.take();
        if !output.is_empty() {
            self.print(&output);
        }

        self.print_prompt();
    }

    fn handle_line(&mut self) {
        match self.cur_line.chars().next() {
            None => return,
            Some('q') => {
                self.running = false;
                return;
            }
            Some('h') => {
                self.print(
                    &self
                        .runtime
                        .help_message(self.cur_line[1..].split_whitespace()),
                );
                self.cur_line.clear();
                self.cursor_position = 0;
                return;
            }
            _ => {}
        }

        self.source_lines.push(std::mem::take(&mut self.cur_line));
        self.cursor_position = 0;

        self.runtime.exec_cmd(
            self.source_lines.last().unwrap(),
            self.source_lines.len() - 1,
        );
    }
}

impl Report for Rc<RefCell<String>> {
    fn echo(&self, s: &str) {
        let mut this = self.borrow_mut();
        this.push('\n');
        this.push_str(s);
    }

    fn report_err(&self, err: &crate::Error, src_line: &str) {
        let mut this = self.borrow_mut();
        this.push_str("\nError: ");
        this.push_str(&err.render(src_line));
    }
}
