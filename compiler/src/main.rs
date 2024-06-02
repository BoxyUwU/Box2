#![feature(type_alias_impl_trait)]
#![feature(map_try_insert)]

use std::collections::HashMap;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use crate::typeck::TypeckError;

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
mod scopegraph;
mod solve;
mod tir;
mod tokenize;
mod typeck;

fn main() {
    use ast::Nodes;
    use tokenize::Tokenizer;

    let path = std::env::args().nth(1).expect("give me a path >:(");
    let code = std::fs::read_to_string(path).expect("give me a PATH >:(");

    let mut files = codespan_reporting::files::SimpleFiles::new();
    files.add("main.box", &code);
    let writer = codespan_reporting::term::termcolor::StandardStream::stderr(
        codespan_reporting::term::termcolor::ColorChoice::Auto,
    );
    let config = codespan_reporting::term::Config::default();

    let nodes = Nodes::new();
    let root_mod = match parser::parse_crate(&mut Tokenizer::new(&code), &nodes) {
        Ok(a) => a,
        Err(diag) => {
            codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            return;
        }
    };

    let crate_scopegraph = resolve::build_graph_for_crate(root_mod);
    let mut resolver = resolve::Resolver::new(&crate_scopegraph);
    resolver.resolve_mod(root_mod);
    let (resolution_errors, resolutions) = resolver.into_outputs();

    for error in resolution_errors {
        match error {
            resolve::ResolutionError::UnresolvedLexicalIdentifier {
                ident,
                in_scope: _,
                cause_expr,
            } => {
                let span = nodes.get(cause_expr).unwrap_path_seg().span;

                let diag = Diagnostic::error()
                    .with_message(format!("failed to resolve `{ident}`"))
                    .with_labels(vec![Label::primary(0, span)]);
                codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            }
            resolve::ResolutionError::UnresolvedAssociatedIdentifier {
                ident,
                in_scope: _,
                cause_expr,
            } => {
                let span = nodes.get(cause_expr).unwrap_path_seg().span;

                let diag = Diagnostic::error()
                    .with_message(format!("failed to resolve `{ident}`"))
                    .with_labels(vec![Label::primary(0, span)]);
                codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            }
            resolve::ResolutionError::UnresolvedField {
                ident,
                on_res: _,
                cause_expr,
            } => {
                let span = nodes.get(cause_expr).unwrap_expr().span();

                let diag = Diagnostic::error()
                    .with_message(format!("failed to resolve `{ident}`"))
                    .with_labels(vec![Label::primary(0, span)]);
                codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            }
        }
    }

    let tir_ctx = tir::TirCtx::new();
    let (tir, ref body_sources, tir_ctx, lowered_ids) =
        tir::building::build(&nodes, root_mod.id, &resolutions, &tir_ctx);

    let mut checker = typeck::FnChecker {
        ast: &nodes,
        resolutions: &resolutions,
        typeck_results: HashMap::new(),
        body_sources,

        lowered_ids,
        tir_ctx,
    };
    tir::visit::super_visit_mod(&mut checker, tir);

    let mut results = checker.typeck_results.into_iter().collect::<Vec<_>>();
    results.sort_by(|a, b| Ord::cmp(&a.0, &b.0));
    for e in results.into_iter().flat_map(|(_, r)| r.errs) {
        match e {
            TypeckError::ExpectedFound(typeck::ExpectedFound(a, b, span)) => {
                let diag = Diagnostic::error()
                    .with_message(format!(
                        "mismatched types: a:{} b:{}",
                        a.pretty(&tir_ctx),
                        b.pretty(&tir_ctx),
                    ))
                    .with_labels(vec![Label::primary(0, span)]);
                codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            }
            TypeckError::UnconstrainedInfer(_, _, span) => {
                let diag = Diagnostic::error()
                    .with_message(format!("could not infer type"))
                    .with_labels(vec![Label::primary(0, span)]);
                codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            }
            TypeckError::NonPlaceExprInMutateOp(_, span) => {
                let diag = Diagnostic::error()
                    .with_message(format!("invalid place expression",))
                    .with_labels(vec![Label::primary(0, span)]);
                codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            }
            TypeckError::NonIdentRhsOfDotOp(_, span) => {
                let diag = Diagnostic::error()
                    .with_message(format!("not an identifier",))
                    .with_labels(vec![Label::primary(0, span)]);
                codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            }
            TypeckError::NonStructTyForDotOp(ty, span) => {
                let diag = Diagnostic::error()
                    .with_message(format!(
                        "expected expression to have the type of a struct not `{}`",
                        ty.pretty(&tir_ctx)
                    ))
                    .with_labels(vec![Label::primary(0, span)]);
                codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            }
            TypeckError::FieldOrMethodNotFoundOnTy(ty, ident, span) => {
                let diag = Diagnostic::error()
                    .with_message(format!(
                        "field or method with name `{}` not present on ty `{}`",
                        ident,
                        ty.pretty(&tir_ctx)
                    ))
                    .with_labels(vec![Label::primary(0, span)]);
                codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &diag).unwrap();
            }
        }
    }

    for e in tir_ctx.take_errs() {
        codespan_reporting::term::emit(&mut writer.lock(), &config, &files, &e).unwrap();
    }
}
