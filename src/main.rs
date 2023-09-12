#![feature(type_alias_impl_trait)]
#![feature(map_try_insert)]

use std::collections::HashMap;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::ast::visit;
// use crate::{ast::visit, typeck::TypeckError};

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
mod tir;
mod tokenize;
// mod typeck;

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

    let tir_ctx = tir::TirCtx::new();
    let tir = tir::building::build(&nodes, root_mod.id, &resolver.resolutions, &tir_ctx);

    // let mut checker = typeck::FnChecker {
    //     ast: &nodes,
    //     resolutions: &resolver.resolutions,
    //     typeck_results: HashMap::new(),
    // };
    // visit::super_visit_mod(&mut checker, root_mod);

    // for e in checker.typeck_results.into_iter().flat_map(|(_, r)| r.errs) {
    //     match e {
    //         TypeckError::ExpectedFound(typeck::ExpectedFound(a, b, span)) => {
    //             let diag = Diagnostic::error()
    //                 .with_message(format!(
    //                     "mismatched types: a:{} b:{}",
    //                     a.pretty(&nodes),
    //                     b.pretty(&nodes),
    //                 ))
    //                 .with_labels(vec![Label::primary(0, span)]);
    //             codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
    //         }
    //         TypeckError::UnconstrainedInfer(_, _, span) => {
    //             let diag = Diagnostic::error()
    //                 .with_message(format!("could not infer type"))
    //                 .with_labels(vec![Label::primary(0, span)]);
    //             codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
    //         }
    //     }
    // }
}
