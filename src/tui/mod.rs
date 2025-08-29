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
}

#[derive(Debug)]
struct Tui {
    running: bool,
    buffer: String,
    cursor_position: usize,
    cur_line: String,
    history_index: usize,
    scroll_lines: u16,
    viewport_size: u16,
    doc_size: u16,
    update_scroll_position: bool,

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
            history_index: 0,
            scroll_lines: 0,
            viewport_size: 0,
            doc_size: 0,
            update_scroll_position: false,

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
                ratatui::restore();
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

    fn render_cur_line(text: &mut Text, cur_line: &str, cursor_position: usize) {
        let mut chars = 0;
        let mut rendered_cursor = false;
        let mut first = true;

        for line in cur_line.lines() {
            if !first {
                chars += 1;
                text.push_line("");
            } else {
                first = false;
            }

            if cursor_position < chars || cursor_position - chars > line.len() {
                text.push_span(line.to_owned());
            } else if cursor_position == line.len() + chars {
                text.push_span(line.to_owned());
                text.push_span(Span::from(" ").style(Style::new().bg(Color::Gray)));
                rendered_cursor = true;
            } else {
                let cpos = cursor_position - chars;
                text.push_span(line[..cpos].to_owned());
                text.push_span(
                    Span::from(line[cpos..=cpos].to_owned()).style(Style::new().bg(Color::Gray)),
                );
                text.push_span(line[cpos + 1..].to_owned());
                rendered_cursor = true;
            }
            chars += line.len();
        }
        if cur_line.ends_with('\n') {
            text.push_line("");
        }
        if !rendered_cursor {
            // The dot should be invisible since it's the same colour as the background,
            // but we need to use a dot rather than a space since there seems to be a bug
            // where starting a newline with a space (or maybe only if the whole line is a
            // space) produces a double newline rather than just one.
            text.push_span(Span::from(".").style(Style::new().bg(Color::Gray)));
        }
    }

    fn render(&mut self, frame: &mut ratatui::Frame) {
        let area = frame.area();
        let mut text = Text::from(&*self.buffer);

        Self::render_cur_line(&mut text, self.current_line(), self.cursor_position);

        let para = Paragraph::new(text).wrap(Wrap { trim: false });

        self.doc_size = para.line_count(area.width) as u16;
        self.viewport_size = area.bottom();
        if self.update_scroll_position {
            self.update_scroll_position = false;
            if self.doc_size >= self.scroll_lines + self.viewport_size {
                self.scroll_lines = if self.viewport_size > self.doc_size {
                    0
                } else {
                    self.doc_size - self.viewport_size
                };
            }
        }

        let para = para.scroll((self.scroll_lines, 0));

        frame.render_widget(para, area);
    }

    fn current_line(&self) -> &str {
        if self.history_index == 0 {
            &self.cur_line
        } else {
            &self.source_lines[self.source_lines.len() - self.history_index]
        }
    }

    // Enter edit mode if we're in history-scrolling mode.
    fn edit_current_line(&mut self) {
        if self.history_index == 0 {
            return;
        }

        self.cur_line = self.source_lines[self.source_lines.len() - self.history_index].clone();
        self.history_index = 0;
    }

    fn total_line_count(&self) -> u16 {
        let cur_line = self.current_line();
        let fudge = if cur_line.is_empty() { 1 } else { 2 };
        (self.buffer.lines().count() + cur_line.lines().count() - fudge) as u16
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
                self.history_index = 0;
                self.cur_line.clear();
                self.cursor_position = 0;
                self.scroll_lines = self.doc_size - 1;
                self.update_scroll_position = true;
            }
            (KeyModifiers::SHIFT, KeyCode::Enter) => {
                self.edit_current_line();
                self.cur_line.insert(self.cursor_position, '\n');
                self.cursor_position += 1;
                self.update_scroll_position = true;
            }
            (_, KeyCode::Enter) => {
                self.edit_current_line();
                self.on_enter();
                self.update_scroll_position = true;
            }
            (_, KeyCode::Backspace) => {
                self.edit_current_line();
                if self.cursor_position > 0 {
                    if self.cursor_position >= self.cur_line.len() {
                        self.cur_line.pop();
                    } else {
                        self.cur_line
                            .replace_range(self.cursor_position - 1..self.cursor_position, "");
                    }
                    self.cursor_position -= 1;
                }
                self.update_scroll_position = true;
            }
            (_, KeyCode::Delete) => {
                self.edit_current_line();
                if self.cursor_position < self.cur_line.len() {
                    self.cur_line
                        .replace_range(self.cursor_position..=self.cursor_position, "");
                }
                self.update_scroll_position = true;
            }
            // Cursor keys
            (_, KeyCode::Left) if self.cursor_position > 0 => self.cursor_position -= 1,
            (_, KeyCode::Right) if self.cursor_position < self.cur_line.len() => {
                self.cursor_position += 1
            }
            (KeyModifiers::SHIFT, KeyCode::Down) => {
                if self.scroll_lines < self.doc_size - 1 {
                    self.scroll_lines += 1;
                }
            }
            (KeyModifiers::SHIFT, KeyCode::Up) => {
                if self.scroll_lines > 0 {
                    self.scroll_lines -= 1;
                }
            }
            (_, KeyCode::Up) if self.history_index < self.source_lines.len() => {
                self.history_index += 1;
                self.cursor_position = self.current_line().len();
                if self.scroll_lines > self.total_line_count() {
                    self.scroll_lines = self.total_line_count();
                }
                self.update_scroll_position = true;
            }
            (_, KeyCode::Down) if self.history_index > 0 => {
                self.history_index -= 1;
                self.cursor_position = self.current_line().len();
                if self.scroll_lines > self.total_line_count() {
                    self.scroll_lines = self.total_line_count();
                }
                self.update_scroll_position = true;
            }
            // TODO? undo, redo

            // Typing characters
            (_, KeyCode::Char(c)) => {
                self.edit_current_line();
                self.cur_line.insert(self.cursor_position, c);
                self.cursor_position += 1;
                self.update_scroll_position = true;
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
