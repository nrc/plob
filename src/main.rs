use plob::{stdio, tui};

fn main() {
    let mut args = std::env::args();
    let _pname = args.next().unwrap();
    if let Some(arg) = args.next()
        && arg == "--stdio"
    {
        stdio::start();
        return;
    }
    tui::start();
}
