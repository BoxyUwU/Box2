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
    let valid_code = [
        "mod Foo {
            type Bar {
                field: type {},
                _field: type {},
                _field___bar_OWOFoo: type {},
            }
        }",
        "mod Foo {}",
    ];
    for code in valid_code {
        use codespan_reporting::files::SimpleFiles;
        let mut nodes = ast::Nodes(vec![]);
        let mut files = SimpleFiles::new();
        files.add("main.box", code);
        parser::parse_mod(&mut tokenize::Tokenizer::new(code), &mut nodes).unwrap();
    }
}
