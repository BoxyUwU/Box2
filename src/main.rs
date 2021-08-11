use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    files::SimpleFiles,
    term::{
        self,
        termcolor::{ColorChoice, StandardStream},
    },
};

macro_rules! unwrap_matches {
    ($e:expr, $p:pat) => {
        match $e {
            $p => (),
            _ => panic!(""),
        }
    };
    ($e:expr, $p:pat => $body:expr) => {
        match $e {
            $p => $body,
            _ => panic!(""),
        }
    };
}

mod ast;
mod parser;
mod resolve;
mod tokenize;

fn main() {
    let mut files = SimpleFiles::new();
    let file = r"
    fn foo(,,) { let awd = 10; }
        ";
    let file_id = files.add("main.box", file);
    let diagnostic =
        parser::parse_fn(&mut tokenize::Tokenizer::new(file), &mut ast::Nodes(vec![])).unwrap_err();

    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = term::Config::default();
    term::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
}
