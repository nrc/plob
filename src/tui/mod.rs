// TODO use Cargo features to enable tui

use std::{cell::RefCell, error::Error, io::stdout, rc::Rc, time::Duration};

use crossterm::event::{
    self, EnableBracketedPaste, Event, KeyCode, KeyEvent, KeyEventKind, KeyModifiers,
    KeyboardEnhancementFlags, PopKeyboardEnhancementFlags, PushKeyboardEnhancementFlags,
};
use ratatui::{
    style::{Color, Style},
    text::{Line, Span, Text},
    widgets::Paragraph,
};

use crate::Report;

const PROMPT: &str = "> ";

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
        self.buffer.push('\n');
        self.buffer.push_str(PROMPT);
    }

    fn print(&mut self, s: &str) {
        self.buffer.push('\n');
        self.buffer.push_str(s);
    }

    fn render(&mut self, frame: &mut ratatui::Frame) {
        let area = frame.area();
        let mut renderer = TextRenderer::new(area.width);

        for line in self.buffer.lines() {
            renderer.push_line_to_text(line, None);
            renderer.finish_line();
        }
        if self.buffer.ends_with('\n') {
            renderer.finish_line();
        }

        renderer.render_cur_line(self.current_line(), self.cursor_position);

        // TODO scrolling - what if doc_size has changed?
        let doc_size = renderer.line_count;
        let viewport_size = area.bottom();
        let mut scroll_lines = self.scroll_lines;

        if (self.update_scroll_position || doc_size != self.doc_size)
            && doc_size >= self.scroll_lines + viewport_size
        {
            scroll_lines = doc_size.saturating_sub(viewport_size);
        }

        let para = Paragraph::new(renderer.text).scroll((scroll_lines, 0));
        frame.render_widget(para, area);

        self.doc_size = doc_size;
        self.scroll_lines = scroll_lines;
        self.update_scroll_position = false;
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
                // TODO handle windows line endings
                self.cur_line
                    .insert_str(self.cursor_position, &s.replace('\r', "\n"));
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
            (_, KeyCode::Right) if self.cursor_position < self.current_line().len() => {
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
            (modifier, KeyCode::Char(c)) => {
                let c = apply_shift(c, modifier.intersects(KeyModifiers::SHIFT));
                self.edit_current_line();
                self.cur_line.insert(self.cursor_position, c);
                self.cursor_position += 1;
                self.update_scroll_position = true;
            }
            _ => {}
        }
    }

    fn on_enter(&mut self) {
        self.print_prompt();

        if self.cur_line.is_empty() {
            return;
        }

        self.buffer.push_str(&self.cur_line);
        self.handle_line();

        let output = self.pending_output.take();
        if !output.is_empty() {
            self.print(&output);
        }
    }

    fn handle_line(&mut self) {
        if self.cur_line.is_empty() {
            return;
        }

        self.source_lines.push(std::mem::take(&mut self.cur_line));
        self.cursor_position = 0;

        let line = self.source_lines.last().unwrap();

        if line == "q" || line.starts_with("q ") {
            self.running = false;
            return;
        }

        if line == "h" || line.starts_with("h ") {
            self.print(&self.runtime.help_message(line[1..].split_whitespace()));
            return;
        }

        self.runtime.exec_cmd(line, self.source_lines.len() - 1);
    }
}

struct TextRenderer<'a> {
    text: Text<'a>,
    line: Line<'a>,
    width: u16,
    line_count: u16,
}

impl<'a> TextRenderer<'a> {
    fn new(width: u16) -> Self {
        Self {
            text: Text::default(),
            line: Line::default(),
            width,
            line_count: 0,
        }
    }

    fn render_cur_line<'b: 'a>(&mut self, cur_line: &'b str, cursor_position: usize) {
        let mut chars = 0;
        let mut rendered_cursor = false;
        let mut first = true;

        self.line.push_span(PROMPT);
        for line in cur_line.lines() {
            // Account for the newline character.
            if first {
                first = false;
            } else {
                self.finish_line();
                chars += 1;
            }

            if cursor_position < chars || cursor_position - chars > line.len() {
                self.push_line_to_text(line, None);
            } else {
                let cpos = cursor_position - chars;
                self.push_line_to_text(line, Some(cpos));
                rendered_cursor = true;
            }

            chars += line.len();
        }
        if cur_line.ends_with('\n') {
            self.finish_line();
        }
        if !rendered_cursor {
            // The dot should be invisible since it's the same colour as the background,
            // but we need to use a dot rather than a space since there seems to be a bug
            // where starting a newline with a space (or maybe only if the whole line is a
            // space) produces a double newline rather than just one.
            self.line
                .push_span(Span::from(".").style(Style::new().bg(Color::Gray)));
        }
        self.finish_line();
    }

    fn push_line_to_text<'b: 'a>(&mut self, line: &'b str, cursor: Option<usize>) {
        match cursor {
            Some(cpos) => {
                self.push_line_to_line(&line[..cpos]);
                if cpos < line.len() {
                    self.line.push_span(
                        Span::from(&line[cpos..=cpos]).style(Style::new().bg(Color::Gray)),
                    );
                    self.push_line_to_line(&line[cpos + 1..]);
                } else {
                    self.line
                        .push_span(Span::from(".").style(Style::new().bg(Color::Gray)));
                }
            }
            None => {
                self.push_line_to_line(line);
            }
        }
    }

    fn finish_line(&mut self) {
        self.text.push_line(std::mem::take(&mut self.line));
        self.line_count += 1;
    }

    fn push_line_to_line<'b: 'a>(&mut self, mut line: &'b str) {
        // line wrapping
        loop {
            let chunk_len = self.width as usize - self.line.width();
            if line.len() <= chunk_len {
                break;
            }
            self.line.push_span(&line[..chunk_len]);
            self.finish_line();
            line = &line[chunk_len..];
        }

        self.line.push_span(line);
    }
}

// This is pretty sub-optimal (it is only correct for US keyboard layout and probably misses keys
// from other keyboards, etc.). There must be a better way, but I couldn't find one.
fn apply_shift(c: char, shift: bool) -> char {
    if !shift {
        return c;
    }

    if c.is_alphabetic() {
        return c.to_ascii_uppercase();
    }

    match c {
        '`' => '~',
        '1' => '!',
        '2' => '@',
        '3' => '#',
        '4' => '$',
        '5' => '%',
        '6' => '^',
        '7' => '&',
        '8' => '*',
        '9' => '(',
        '0' => ')',
        '-' => '_',
        '=' => '+',
        ',' => '<',
        '.' => '>',
        '/' => '?',
        ';' => ':',
        '\'' => '"',
        '[' => '{',
        ']' => '}',
        '\\' => '|',
        _ => todo!(),
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
