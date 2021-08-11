use codespan_reporting::diagnostic::{Diagnostic, Label};
use logos::Span;

use crate::tokenize::{Kw, Token, Tokenizer};

use crate::ast::*;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Operator {
    Ambig(BinOp, UnOp),
    BinOp(BinOp),
    UnOp(UnOp),
}

impl Operator {
    fn bp(self) -> (Option<u8>, u8) {
        match self {
            Self::BinOp(op) => op.bp(),
            Self::UnOp(op) => op.bp(),
            _ => panic!(""),
        }
    }

    fn disambig_bin(self) -> Self {
        match self {
            Self::Ambig(bin, _) => Self::BinOp(bin),
            _ => self,
        }
    }

    fn disambig_un(self) -> Self {
        match self {
            Self::Ambig(_, un) => Self::UnOp(un),
            _ => self,
        }
    }

    fn binop(self) -> Option<BinOp> {
        match self {
            Self::BinOp(op) => Some(op),
            Self::Ambig(..) => panic!(""),
            _ => None,
        }
    }

    fn unop(self) -> Option<UnOp> {
        match self {
            Self::UnOp(op) => Some(op),
            Self::Ambig(..) => panic!(""),
            _ => None,
        }
    }
}

impl BinOp {
    /// Option is always `Some`
    fn bp(&self) -> (Option<u8>, u8) {
        match self {
            BinOp::Add | BinOp::Sub => (Some(1), 2),
            BinOp::Mul | BinOp::Div => (Some(3), 4),
        }
    }
}

impl UnOp {
    /// Option is always `None`
    fn bp(&self) -> (Option<u8>, u8) {
        match self {
            UnOp::Neg => (None, 5),
        }
    }
}

impl<'a> Token<'a> {
    fn to_operator(&self) -> Option<Operator> {
        use Token::*;
        Some(match *self {
            Plus => Operator::BinOp(BinOp::Add),
            Hyphen => Operator::Ambig(BinOp::Sub, UnOp::Neg),
            FwdSlash => Operator::BinOp(BinOp::Div),
            Star => Operator::BinOp(BinOp::Mul),
            _ => return None,
        })
    }
}

impl<'a> Tokenizer<'a> {
    fn next_if_disambig_un_op(&mut self) -> Option<UnOp> {
        match self
            .peek()
            .map(|(tok, _)| tok)
            .and_then(Token::to_operator)
            .map(Operator::disambig_un)
            .and_then(Operator::unop)
        {
            Some(op) => {
                self.next().unwrap();
                Some(op)
            }
            None => None,
        }
    }
}

impl Kw {
    fn format_found(&self) -> String {
        match self {
            Kw::Mod => "mod".into(),
            Kw::Let => "let".into(),
            Kw::Fn => "fn".into(),
            Kw::Pub => "pub".into(),
            Kw::Type => "type".into(),
        }
    }
}

impl<'a> Token<'a> {
    fn format_found(&self) -> String {
        use crate::tokenize::Literal;
        match self {
            Token::Ident(i) => i.to_string(),
            Token::Literal(Literal::Int(i)) => i.to_string(),
            Token::Literal(Literal::Float(f)) => f.to_string(),
            Token::Kw(kw) => kw.format_found(),
            t => match t {
                Token::Plus => "+",
                Token::Hyphen => "-",
                Token::Star => "*",
                Token::FwdSlash => "/",
                Token::UpLine => "|",
                Token::Arrow => "->",
                Token::Colon => ":",
                Token::SemiColon => ";",
                Token::Comma => ",",
                Token::Eq => "=",
                Token::LParen => "(",
                Token::RParen => ")",
                Token::LBrace => "{",
                Token::RBrace => "}",
                Token::Error => "ERROR",

                Token::Ident(_) | Token::Kw(_) | Token::Literal(_) => unreachable!(),
            }
            .into(),
        }
    }
}

fn diag_expected_bound<'a>(expected: &str, found: Token<'a>, span: Span) -> Diagnostic<usize> {
    Diagnostic::error()
        .with_message(&format!("expected {}", expected))
        .with_labels(vec![
            Label::primary(0, span).with_message(&format!("found {}", found.format_found()))
        ])
}

fn parse_expr<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &mut Nodes,
    min_bp: u8,
) -> Result<NodeId, Diagnostic<usize>> {
    let mut lhs = if let Some(unop) = tok.next_if_disambig_un_op() {
        let (_, r_bp) = unop.bp();
        let rhs = parse_expr(tok, nodes, r_bp)?;
        nodes.push_expr(ExprKind::UnOp(unop, rhs))
    } else if let Ok(_) = tok.next_if(Token::LParen) {
        let inner = parse_expr(tok, nodes, 0)?;
        tok.next_if(Token::RParen)
            .map_err(|(found, span)| diag_expected_bound("}", found, span))?;
        inner
    } else if let Ok((ident, _)) = tok.next_if_ident() {
        nodes.push_expr(ExprKind::Ident(ident.to_owned()))
    } else if let Ok((lit, _)) = tok.next_if_lit() {
        nodes.push_expr(ExprKind::Lit(lit))
    } else if let Ok(_) = tok.peek_if(Token::LBrace) {
        parse_block_expr(tok, nodes)?
    } else if let Ok(_) = tok.peek_if(Token::Kw(Kw::Let)) {
        parse_let_expr(tok, nodes)?
    } else {
        return Err(Diagnostic::error());
    };

    loop {
        let op = match tok.peek().map(|(tok, _)| tok).and_then(Token::to_operator) {
            Some(op) => op.disambig_bin(),
            None => return Ok(lhs),
        };
        let (l_bp, r_bp) = op.bp();
        let l_bp = l_bp.unwrap();

        if l_bp < min_bp {
            return Ok(lhs);
        }
        tok.next().unwrap();

        let rhs = parse_expr(tok, nodes, r_bp)?;
        lhs = nodes.push_expr(ExprKind::BinOp(op.binop().unwrap(), lhs, rhs));
    }
}

fn parse_let_expr<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &mut Nodes,
) -> Result<NodeId, Diagnostic<usize>> {
    tok.next_if(Token::Kw(Kw::Let))
        .map_err(|(found, span)| diag_expected_bound("let", found, span))?;
    let (name, _) = tok
        .next_if_ident()
        .map_err(|(found, span)| diag_expected_bound("IDENTIFIER", found, span))?;
    tok.next_if(Token::Eq)
        .map_err(|(found, span)| diag_expected_bound("=", found, span))?;
    let expr = parse_expr(tok, nodes, 0)?;
    Ok(nodes.push_expr(ExprKind::Let(name.to_owned(), expr)))
}

pub fn parse_block_expr<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &mut Nodes,
) -> Result<NodeId, Diagnostic<usize>> {
    tok.next_if(Token::LBrace)
        .map_err(|(found, span)| diag_expected_bound("{", found, span))?;
    let mut stmts = vec![];
    while let Err(_) = tok.next_if(Token::RBrace) {
        let expr = parse_expr(tok, nodes, 0)?;
        let terminator = tok.next_if(Token::SemiColon).is_ok();
        stmts.push((expr, terminator));
    }
    Ok(nodes.push_expr(ExprKind::Block(stmts)))
}

pub fn parse_fn<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &mut Nodes,
) -> Result<NodeId, Diagnostic<usize>> {
    // (pub)? fn ( (ident: ty),* ) (-> ty)? { expr }

    let visibility = tok
        .next_if(Token::Kw(Kw::Pub))
        .ok()
        .map(|_| Visibility::Pub);
    tok.next_if(Token::Kw(Kw::Fn))
        .map_err(|(found, span)| diag_expected_bound("fn", found, span))?;
    let name = tok
        .next_if_ident()
        .map_err(|(found, span)| diag_expected_bound("IDENTIFER", found, span))?
        .0
        .to_owned();

    tok.next_if(Token::LParen)
        .map_err(|(found, span)| diag_expected_bound("(", found, span))?;
    let mut params = Vec::new();
    while let Ok((ident, _)) = tok.next_if_ident() {
        tok.next_if(Token::Colon)
            .map_err(|(found, span)| diag_expected_bound(":", found, span))?;
        let (ty, _) = tok
            .next_if_ident()
            .map_err(|(found, span)| diag_expected_bound("IDENTIFIER", found, span))?;
        params.push((ident.to_owned(), ty.to_owned()));

        match tok.next_if(Token::Comma) {
            Ok(_) => continue,
            Err(_) => break,
        }
    }
    tok.next_if(Token::RParen)
        .map_err(|(found, span)| diag_expected_bound(")", found, span))?;

    let mut ret_ty = None;
    if let Ok(_) = tok.next_if(Token::Arrow) {
        ret_ty = Some(
            tok.next_if_ident()
                .map_err(|(found, span)| diag_expected_bound("IDENTIFER", found, span))?
                .0
                .to_owned(),
        );
    }

    let body = parse_block_expr(tok, nodes)?;

    Ok(nodes.push_fn(Fn {
        visibility,
        name,
        params,
        ret_ty,
        body,
    }))
}

pub fn parse_type_def<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &mut Nodes,
    parent_field: Option<String>,
) -> Result<NodeId, Diagnostic<usize>> {
    let visibility = tok
        .next_if(Token::Kw(Kw::Pub))
        .ok()
        .map(|_| Visibility::Pub);
    let (_, type_span) = tok
        .next_if(Token::Kw(Kw::Type))
        .map_err(|(found, span)| diag_expected_bound("type", found, span))?;

    let mut name = tok.next_if_ident().ok().map(|(s, _)| s.to_string());
    // type def is only permitted to not have a name if it is
    // the rhs of a field i.e. `field: type { ... }`
    if let None = name {
        name = Some(parent_field.ok_or_else(|| {
            Diagnostic::error()
                .with_message("expected a name")
                .with_labels(vec![Label::primary(0, type_span)])
        })?);
        // FIXME change casing of `parent_field` to be type cased
    }

    tok.next_if(Token::LBrace)
        .map_err(|(found, span)| diag_expected_bound("{", found, span))?;

    let mut variants = Vec::new();
    if let Ok(_) = tok.peek_if(Token::UpLine) {
        // type { | Foo, | Bar, }
        while let Err(_) = tok.peek_if(Token::RBrace) {
            tok.next_if(Token::UpLine)
                .map_err(|(found, span)| diag_expected_bound("|", found, span))?;
            let visibility = tok
                .next_if(Token::Kw(Kw::Pub))
                .ok()
                .map(|_| Visibility::Pub);
            let name = tok
                .next_if_ident()
                .map_err(|(found, span)| diag_expected_bound("IDENTIFER", found, span))?
                .0
                .to_owned();
            tok.next_if(Token::LBrace)
                .map_err(|(found, span)| diag_expected_bound("{", found, span))?;
            let Fields {
                type_defs,
                field_defs,
            } = parse_fields(tok, nodes)?;
            tok.next_if(Token::RBrace)
                .map_err(|(found, span)| diag_expected_bound("}", found, span))?;

            let variant_id = nodes.push_variant_def(VariantDef {
                visibility,
                name: Some(name),
                type_defs,
                field_defs,
            });
            variants.push(variant_id);

            match tok.next_if(Token::Comma) {
                Ok(_) => continue,
                Err(_) => break,
            }
        }
    } else {
        // type { field: Ty, bar: Foo, }
        let Fields {
            type_defs,
            field_defs,
        } = parse_fields(tok, nodes)?;
        let variant_id = nodes.push_variant_def(VariantDef {
            visibility,
            name: None,
            type_defs,
            field_defs,
        });
        variants.push(variant_id);
    }

    tok.next_if(Token::RBrace)
        .map_err(|(found, span)| diag_expected_bound("}", found, span))?;

    let id = nodes.push_type_def(TypeDef {
        visibility,
        name,
        variants,
    });
    Ok(id)
}

struct Fields {
    type_defs: Vec<NodeId>,
    field_defs: Vec<NodeId>,
}

fn parse_fields<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &mut Nodes,
) -> Result<Fields, Diagnostic<usize>> {
    let mut type_defs = Vec::new();
    let mut field_defs = Vec::new();

    while let Err(_) = tok.peek_if(Token::RBrace) {
        let visibility = tok
            .next_if(Token::Kw(Kw::Pub))
            .ok()
            .map(|_| Visibility::Pub);
        let name = tok
            .next_if_ident()
            .map_err(|(found, span)| diag_expected_bound("IDENTIFER", found, span))?
            .0
            .to_string();
        tok.next_if(Token::Colon)
            .map_err(|(found, span)| diag_expected_bound(":", found, span))?;

        let ty = match tok.peek() {
            Some((Token::Kw(Kw::Type | Kw::Pub), _)) => {
                let ty_def_id = parse_type_def(tok, nodes, Some(name.clone()))?;
                type_defs.push(ty_def_id);
                ty_def_id
            }
            Some((Token::Ident(_), _)) => {
                let ty = unwrap_matches!(tok.next(), Some((Token::Ident(ty), _)) => ty);
                nodes.push_expr(ExprKind::Ident(ty.to_string()))
            }
            Some((tok, span)) => {
                return Err(diag_expected_bound("type", *tok, span.clone()));
            }
            _ => return Err(Diagnostic::error()),
        };

        field_defs.push(nodes.push_field_def(FieldDef {
            visibility,
            name,
            ty,
        }));

        match tok.next_if(Token::Comma) {
            Ok(_) => continue,
            Err(_) => break,
        }
    }

    Ok(Fields {
        type_defs,
        field_defs,
    })
}

pub fn parse_mod<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &mut Nodes,
) -> Result<NodeId, Diagnostic<usize>> {
    // $(pub)? mod IDENT { $(i:item_def)* }
    let visibility = tok
        .next_if(Token::Kw(Kw::Pub))
        .ok()
        .map(|_| Visibility::Pub);
    tok.next_if(Token::Kw(Kw::Mod))
        .map_err(|(tok, sp)| diag_expected_bound("mod", tok, sp))?;
    let name = tok
        .next_if_ident()
        .map_err(|(tok, sp)| diag_expected_bound("IDENTIFER", tok, sp))?;

    tok.next_if(Token::LBrace)
        .map_err(|(tok, sp)| diag_expected_bound("{", tok, sp))?;

    let mut items = Vec::new();
    while let Err(_) = tok.next_if(Token::RBrace) {
        let peeked = match tok.peek_if(Token::Kw(Kw::Pub)) {
            Ok(_) => tok.peek_second(),
            Err(_) => tok.peek(),
        }
        .ok_or_else(|| Diagnostic::error().with_message("unexpected end of file"))?;

        let item_node_id = match &peeked.0 {
            Token::Kw(Kw::Mod) => parse_mod(tok, nodes)?,
            Token::Kw(Kw::Type) => parse_type_def(tok, nodes, None)?,
            Token::Kw(Kw::Fn) => parse_fn(tok, nodes)?,
            _ => {
                return Err(Diagnostic::error()
                    .with_message("non-item in module")
                    .with_labels(vec![Label::primary(0, peeked.1.clone())]))
            }
        };
        items.push(item_node_id);
    }

    Ok(nodes.push_mod_def(Module {
        visibility,
        name: name.0.into(),
        items,
    }))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn mod_defs_valid() {
        let mut nodes = Nodes(vec![]);
        let valid_code = [
            "mod Foo {}",
            "pub mod Foo {}",
            "mod Foo { 
                fn bar() { let _ = 10; } 
            }",
            "mod Foo { 
                fn bar() { let _ = 10; } 
                pub fn baz() { let _ = 10; }
            }",
            "mod Foo {
                type Bar {
                    field: Blah,
                }
                fn bar() { let _ = 10; } 
                pub fn baz() { let _ = 10; }
            }",
            "mod Foo {
                mod Bar {
                    type Foo {}
                }
            }",
        ];
        for code in valid_code {
            parse_mod(&mut Tokenizer::new(code), &mut nodes).unwrap();
        }
    }

    #[test]
    fn mod_defs_invalid() {
        let mut nodes = Nodes(vec![]);
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
            parse_mod(&mut Tokenizer::new(code), &mut nodes).unwrap_err();
        }
    }

    #[test]
    fn type_defs_valid() {
        let mut nodes = Nodes(vec![]);
        let valid_code = [
            "type Foo { field: Bar }",
            "type Foo {
                | Bar{},
                | Baz{},
            }",
            "type Foo {}",
            "type Foo {
                field: type {
                    inner_field: Bar,
                },
                other_field: type Blah {}
            }",
            "pub type Foo {}",
            "pub type Foo {
                pub field: pub type {
                    pub inner_field: Bar,
                },
                pub other_field: pub type Blah {}
            }",
            "type Foo {
                field: pub type Bar {
                }
            }",
            "type Foo {
                | Bar { 
                    field: type Baz {},
                },
                | Blah {},
            }",
            "pub type Foo {
                | pub Bar {},
                | pub baz {
                    pub field: type Blah {
                        | pub None {},
                        | pub Some { field: UwU },
                    }
                }
            }",
        ];
        for code in valid_code {
            parse_type_def(&mut Tokenizer::new(code), &mut nodes, None).unwrap();
        }
    }

    #[test]
    fn type_defs_invalid() {
        let mut nodes = Nodes(vec![]);
        let invalid_code = [
            "type Foo {
                | type Bar {}
            }",
            "type Foo {
                field: Bar
                field2: Baz
            }",
            "type Foo {
                field:
                    | Bar {},
                    | Baz {},
            }",
        ];
        for code in invalid_code {
            parse_type_def(&mut Tokenizer::new(code), &mut nodes, None)
                .map(|_| panic!(""))
                .unwrap_err();
        }
    }

    #[test]
    fn let_expr() {
        let mut nodes = Nodes(vec![]);
        parse_let_expr(&mut Tokenizer::new("let foo = 10 + 12"), &mut nodes).unwrap();
        assert_eq!(&nodes.to_string(), "let foo = (+ 10 12)");
        parse_let_expr(
            &mut Tokenizer::new("let foo = { 10 + 12; bar }"),
            &mut nodes,
        )
        .unwrap();
        assert_eq!(
            &nodes.to_string(),
            r"let foo = {
    (+ 10 12);
    bar
}"
        )
    }

    #[test]
    fn block_expr() {
        let mut nodes = Nodes(vec![]);
        parse_block_expr(&mut Tokenizer::new("{ 10 + 14 - 2; -1; {10} }"), &mut nodes).unwrap();
        assert_eq!(
            &nodes.to_string(),
            r"{
    (- (+ 10 14) 2);
    (- 1);
    {
    10
}
}"
        );
    }

    #[test]
    fn fn_header() {
        let mut nodes = Nodes(vec![]);

        // succeeds
        parse_fn(&mut Tokenizer::new("fn foo() { 1 }"), &mut nodes).unwrap();
        assert_eq!(
            &nodes.to_string(),
            r"fn foo() {
    1
}"
        );
        parse_fn(&mut Tokenizer::new("fn foo(foo: Bar) { 1 }"), &mut nodes).unwrap();
        assert_eq!(
            &nodes.to_string(),
            r"fn foo(foo: Bar,) {
    1
}"
        );
        parse_fn(&mut Tokenizer::new("fn foo() -> RetTy { 1 }"), &mut nodes).unwrap();
        assert_eq!(
            &nodes.to_string(),
            r"fn foo() -> RetTy {
    1
}"
        );
        parse_fn(
            &mut Tokenizer::new("fn foo(foo: Bar) -> RetTy { 1 }"),
            &mut nodes,
        )
        .unwrap();
        assert_eq!(
            &nodes.to_string(),
            r"fn foo(foo: Bar,) -> RetTy {
    1
}"
        );
        parse_fn(&mut Tokenizer::new("fn foo() -> RetTy { 1 }"), &mut nodes).unwrap();
        assert_eq!(
            &nodes.to_string(),
            r"fn foo() -> RetTy {
    1
}"
        );
        parse_fn(
            &mut Tokenizer::new("fn foo(foo: Bar,baz: Bar,) { 1 }"),
            &mut nodes,
        )
        .unwrap();
        assert_eq!(
            &nodes.to_string(),
            r"fn foo(foo: Bar,baz: Bar,) {
    1
}"
        );

        // fails
        parse_fn(&mut Tokenizer::new("pub pub fn foo() { 1 }"), &mut nodes).unwrap_err();
        parse_fn(&mut Tokenizer::new("foo() { 1 }"), &mut nodes).unwrap_err();
        parse_fn(&mut Tokenizer::new("fn foo(foo:: Bar) { 1 }"), &mut nodes).unwrap_err();
        parse_fn(&mut Tokenizer::new("fn foo() -> Ty Ty { 1 }"), &mut nodes).unwrap_err();
        parse_fn(&mut Tokenizer::new("fn foo() -> { 1 }"), &mut nodes).unwrap_err();
        parse_fn(
            &mut Tokenizer::new("fn foo(Foo: Bar,,) -> { 1 }"),
            &mut nodes,
        )
        .unwrap_err();
    }

    #[test]
    fn braces() {
        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 * (2 + 3)"), &mut nodes, 0).unwrap();
        assert_eq!(&nodes.to_string(), "(* 1 (+ 2 3))");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("(1 + 2) * 3"), &mut nodes, 0).unwrap();
        assert_eq!(&nodes.to_string(), "(* (+ 1 2) 3)");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("((((((3))))))"), &mut nodes, 0).unwrap();
        assert_eq!(&nodes.to_string(), "3");
    }

    #[test]
    fn exprs() {
        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 + 2 / 3"), &mut nodes, 0).unwrap();
        assert_eq!(&nodes.to_string(), "(+ 1 (/ 2 3))");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 / 2 + 3"), &mut nodes, 0).unwrap();
        assert_eq!(&nodes.to_string(), "(+ (/ 1 2) 3)");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 + 2 - 3 + 4"), &mut nodes, 0).unwrap();
        assert_eq!(&nodes.to_string(), "(+ (- (+ 1 2) 3) 4)");
    }

    #[test]
    fn disambig_op() {
        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 - 2"), &mut nodes, 0).unwrap();
        assert_eq!(&nodes.to_string(), "(- 1 2)");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 - -2"), &mut nodes, 0).unwrap();
        assert_eq!(&nodes.to_string(), "(- 1 (- 2))");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("-1 - -2"), &mut nodes, 0).unwrap();
        assert_eq!(&nodes.to_string(), "(- (- 1) (- 2))");
    }
}
