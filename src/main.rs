#![feature(type_alias_impl_trait)]

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
    use ast::Nodes;
    use tokenize::Tokenizer;

    let path = std::env::args().nth(1).expect("give me a path >:(");
    let nodes = Nodes::new();
    let code = std::fs::read_to_string(path).expect("give me a PATH >:(");

    let mut files = codespan_reporting::files::SimpleFiles::new();
    files.add("main.box", &code);
    let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
        codespan_reporting::term::termcolor::ColorChoice::Always,
    );
    let config = codespan_reporting::term::Config::default();

    let root_mod = match parser::parse_crate(&mut Tokenizer::new(&code), &nodes) {
        Ok(a) => a,
        Err(diag) => {
            codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            return;
        }
    };

    let mut resolver = resolve::Resolver::new(&nodes);
    resolver.resolve_mod(root_mod);
    for diag in &resolver.errors {
        codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
    }
}
