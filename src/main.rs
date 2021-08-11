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
    let invalid_code = [
        "pub pub Foo {}",
        "mod {}",
        "mod Foo {
            pub pub fn foo() { let _ = 10; }
        }",
        "mod Foo {
            fn foo(,) { let _ = 10; }
        }",
        "mod Foo {
            type {}
        }",
    ];
    for code in invalid_code {
        let mut nodes = ast::Nodes(vec![]);
        let mut files = SimpleFiles::new();
        files.add("main.box", code);
        let diagnostic =
            parser::parse_mod(&mut tokenize::Tokenizer::new(code), &mut nodes).unwrap_err();
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = term::Config::default();
        term::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
    }
}
