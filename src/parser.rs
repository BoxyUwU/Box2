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
    fn bp(self) -> (Option<u8>, Option<u8>) {
        match self {
            Self::BinOp(op) => (Some(op.bp().0), Some(op.bp().1)),
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
    fn bp(&self) -> (u8, u8) {
        match self {
            BinOp::Dot => (13, 14),
            BinOp::Mul | BinOp::Div => (3, 4),
            BinOp::Add | BinOp::Sub => (1, 2),
        }
    }
}

impl UnOp {
    /// Option is always `None`
    fn bp(&self) -> (Option<u8>, Option<u8>) {
        match self {
            UnOp::Call => (Some(11), None),
            UnOp::Neg => (None, Some(5)),
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
            Dot => Operator::BinOp(BinOp::Dot),
            LParen => Operator::UnOp(UnOp::Call),
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
                Token::Dot => ".",
                Token::PathSep => "::",
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
    nodes: &'a Nodes<'a>,
    min_bp: u8,
) -> Result<&'a Node<'a>, Diagnostic<usize>> {
    let mut lhs = if let Ok(_) = tok.next_if(Token::LParen) {
        let inner = parse_expr(tok, nodes, 0)?;
        tok.next_if(Token::RParen)
            .map_err(|(found, span)| diag_expected_bound(")", found, span))?;
        inner
    } else if let Some(unop) = tok.next_if_disambig_un_op() {
        let (_, r_bp) = unop.bp();
        let rhs = parse_expr(tok, nodes, r_bp.unwrap())?;
        nodes.push_expr(ExprKind::UnOp(unop, rhs))
    } else if let Ok(_) = tok.peek_if_ident() {
        let path = nodes.push_expr(ExprKind::Path(parse_path(tok)?));

        // handle type construction i.e.
        // `Foo { field: 10 + 1 }`
        match tok.next_if(Token::LBrace) {
            Err(_) => path,
            Ok(_) => {
                let mut fields = Vec::new();
                while let Ok((ident, span)) = tok.next_if_ident() {
                    tok.next_if(Token::Colon)
                        .map_err(|(found, span)| diag_expected_bound(":", found, span))?;
                    let rhs = parse_expr(tok, nodes, 0)?;

                    let field = nodes
                        .push_expr_with(|id| {
                            ExprKind::FieldInit(FieldInit {
                                id,
                                ident: ident.to_owned(),
                                span: span.clone(),
                                expr: rhs,
                            })
                        })
                        .kind
                        .unwrap_expr();
                    fields.push(unwrap_matches!(&field.kind, ExprKind::FieldInit(init) => init));

                    match tok.next_if(Token::Comma) {
                        Err(_) => break,
                        Ok(_) => continue,
                    }
                }

                tok.next_if(Token::RBrace)
                    .map_err(|(found, span)| diag_expected_bound("}", found, span))?;

                nodes.push_expr(ExprKind::TypeInit(TypeInit {
                    path,
                    field_inits: fields,
                }))
            }
        }
    } else if let Ok((lit, _)) = tok.next_if_lit() {
        nodes.push_expr(ExprKind::Lit(lit))
    } else if let Ok(_) = tok.peek_if(Token::LBrace) {
        parse_block_expr(tok, nodes)?
    } else if let Ok(_) = tok.peek_if(Token::Kw(Kw::Let)) {
        parse_let_expr(tok, nodes)?
    } else {
        match tok.next() {
            None => return Err(Diagnostic::error().with_message("unexpected end of filed")),
            Some((found, span)) => return Err(diag_expected_bound("EXPRESSION", found, span)),
        }
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

        if let Operator::UnOp(UnOp::Call) = op {
            let mut elements = Vec::new();
            while let Err(_) = tok.next_if(Token::RParen) {
                elements.push(parse_expr(tok, nodes, 0)?);

                match tok.next_if(Token::Comma) {
                    Ok(_) => continue,
                    Err(_) => match tok.next_if(Token::RParen) {
                        Ok(_) => break,
                        Err((found, span)) => {
                            return Err(diag_expected_bound(")", found, span.clone()))
                        }
                    },
                }
            }

            match &lhs.kind.unwrap_expr().kind {
                &ExprKind::BinOp(BinOp::Dot, receiver, func) => {
                    lhs = nodes.push_expr(ExprKind::MethodCall(MethodCall {
                        receiver,
                        func,
                        args: elements,
                    }))
                }
                _ => {
                    lhs = nodes.push_expr(ExprKind::FnCall(FnCall {
                        func: lhs,
                        args: elements,
                    }))
                }
            }
            continue;
        }

        let rhs = parse_expr(tok, nodes, r_bp.unwrap())?;
        lhs = nodes.push_expr(ExprKind::BinOp(op.binop().unwrap(), lhs, rhs));
    }
}

fn parse_path<'a>(tok: &mut Tokenizer<'a>) -> Result<Path, Diagnostic<usize>> {
    let ident = |tok: &mut Tokenizer<'_>| {
        tok.next_if_ident()
            .map(|(tok, sp)| (tok.to_owned(), sp))
            .map_err(|(found, span)| diag_expected_bound("IDENTIFIER", found, span))
    };

    let mut segments = vec![ident(tok)?];
    while let Ok(_) = tok.next_if(Token::PathSep) {
        let segment = ident(tok)?;
        segments.push(segment);
    }

    Ok(Path { segments })
}

fn parse_let_expr<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &'a Nodes<'a>,
) -> Result<&'a Node<'a>, Diagnostic<usize>> {
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
    nodes: &'a Nodes<'a>,
) -> Result<&'a Node<'a>, Diagnostic<usize>> {
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
    nodes: &'a Nodes<'a>,
) -> Result<&'a Node<'a>, Diagnostic<usize>> {
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
        params.push((ident.to_owned(), parse_ty(tok, nodes)?));

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

    Ok(nodes.push_fn(|id| Fn {
        id,
        visibility,
        name,
        params,
        ret_ty,
        body,
    }))
}

pub fn parse_type_def<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &'a Nodes<'a>,
    parent_field: Option<String>,
) -> Result<&'a Node<'a>, Diagnostic<usize>> {
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
        let field_name = parent_field.ok_or_else(|| {
            Diagnostic::error()
                .with_message("expected a name")
                .with_labels(vec![Label::primary(0, type_span)])
        })?;
        let mut prefix = match field_name.chars().next().unwrap() {
            '_' => "_",
            _ => "",
        }
        .to_string();
        let ty_name = heck::CamelCase::to_camel_case(&field_name[..]);
        prefix.push_str(&ty_name);
        name = Some(prefix);
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

            let variant = &*nodes.push_variant_def(|id| VariantDef {
                id,
                visibility,
                name: Some(name),
                type_defs: type_defs.into_boxed_slice(),
                field_defs: field_defs.into_boxed_slice(),
            });
            variants.push(variant.kind.unwrap_variant_def());

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
        let variant = &*nodes.push_variant_def(|id| VariantDef {
            id,
            visibility,
            name: None,
            type_defs: type_defs.into_boxed_slice(),
            field_defs: field_defs.into_boxed_slice(),
        });
        variants.push(variant.kind.unwrap_variant_def());
    }

    tok.next_if(Token::RBrace)
        .map_err(|(found, span)| diag_expected_bound("}", found, span))?;

    let id = nodes.push_type_def(|id| TypeDef {
        id,
        visibility,
        name: name.unwrap(),
        variants: variants.into_boxed_slice(),
    });
    Ok(id)
}

struct Fields<'a> {
    type_defs: Vec<&'a TypeDef<'a>>,
    field_defs: Vec<&'a FieldDef<'a>>,
}

fn parse_fields<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &'a Nodes<'a>,
) -> Result<Fields<'a>, Diagnostic<usize>> {
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
                let ty_def = parse_type_def(tok, nodes, Some(name.clone()))?;
                type_defs.push(ty_def.kind.unwrap_type_def());
                ty_def
            }
            _ => parse_ty(tok, nodes)?,
        };

        field_defs.push(
            &*nodes
                .push_field_def(|id| FieldDef {
                    id,
                    visibility,
                    name,
                    ty,
                })
                .kind
                .unwrap_field_def(),
        );

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
    nodes: &'a Nodes<'a>,
) -> Result<&'a Node<'a>, Diagnostic<usize>> {
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

        let item_node = match &peeked.0 {
            Token::Kw(Kw::Mod) => parse_mod(tok, nodes)?,
            Token::Kw(Kw::Type) => parse_type_def(tok, nodes, None)?,
            Token::Kw(Kw::Fn) => parse_fn(tok, nodes)?,
            _ => {
                return Err(Diagnostic::error()
                    .with_message("non-item in module")
                    .with_labels(vec![Label::primary(0, peeked.1.clone())]))
            }
        };
        items.push(item_node.kind.unwrap_item());
    }

    Ok(nodes.push_mod_def(|id| Module {
        id,
        visibility,
        name: name.0.into(),
        items,
    }))
}

pub fn parse_crate<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &'a Nodes<'a>,
) -> Result<&'a Node<'a>, Diagnostic<usize>> {
    let mut items = Vec::new();
    while let Some(_) = tok.peek() {
        let peeked = match tok.peek_if(Token::Kw(Kw::Pub)) {
            Ok(_) => tok.peek_second(),
            Err(_) => tok.peek(),
        }
        .ok_or_else(|| Diagnostic::error().with_message("unexpected end of file"))?;

        let item_node = match &peeked.0 {
            Token::Kw(Kw::Mod) => parse_mod(tok, nodes)?,
            Token::Kw(Kw::Type) => parse_type_def(tok, nodes, None)?,
            Token::Kw(Kw::Fn) => parse_fn(tok, nodes)?,
            _ => {
                return Err(Diagnostic::error()
                    .with_message("non-item in module")
                    .with_labels(vec![Label::primary(0, peeked.1.clone())]))
            }
        };
        items.push(item_node.kind.unwrap_item());
    }

    Ok(nodes.push_mod_def(|id| Module {
        id,
        visibility: Some(Visibility::Pub),
        name: "".into(),
        items,
    }))
}

pub fn parse_ty<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &'a Nodes<'a>,
) -> Result<&'a Node<'a>, Diagnostic<usize>> {
    tok.peek_if_ident()
        .map_err(|(found, span)| diag_expected_bound("IDENTIFIER", found, span))?;
    if let Some((Token::PathSep, _)) = tok.peek_second() {
        let path = parse_path(tok)?;
        Ok(nodes.push_ty(Ty { path }))
    } else {
        let (ident, span) = tok.next_if_ident().unwrap();
        Ok(nodes.push_ty(Ty {
            path: Path {
                segments: vec![(ident.to_string(), span)],
            },
        }))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn paths() {
        let nodes = Nodes::new();
        parse_path(&mut Tokenizer::new("Foo::Bar::Variant::Idk")).unwrap();
        parse_path(&mut Tokenizer::new("Foo::Bar")).unwrap();
        parse_path(&mut Tokenizer::new("Foo::Bar::")).unwrap_err();
        parse_path(&mut Tokenizer::new("Foo::")).unwrap_err();
        parse_expr(&mut Tokenizer::new("Foo::Bar + 10"), &nodes, 0).unwrap();
    }

    #[test]
    fn crate_root_valid() {
        let nodes = Nodes::new();
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
            "fn foo() { let _ = 10; }",
            "pub fn baz() { let _ = 10; }",
            "",
        ];
        for code in valid_code {
            parse_crate(&mut Tokenizer::new(code), &nodes).unwrap();
        }

        let joined = "
            mod Foo {}
            pub mod Foo {}
            mod Foo { 
                fn bar() { let _ = 10; } 
            }
            mod Foo { 
                fn bar() { let _ = 10; } 
                pub fn baz() { let _ = 10; }
            }
            mod Foo {
                type Bar {
                    field: Blah,
                }
                fn bar() { let _ = 10; } 
                pub fn baz() { let _ = 10; }
            }
            mod Foo {
                mod Bar {
                    type Foo {}
                }
            }
            fn foo() { let _ = 10; }
            pub fn baz() { let _ = 10; }
        ";
        parse_crate(&mut Tokenizer::new(joined), &nodes).unwrap();
    }

    #[test]
    fn mod_defs_valid() {
        let nodes = Nodes::new();
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
            parse_mod(&mut Tokenizer::new(code), &nodes).unwrap();
        }
    }

    #[test]
    fn mod_defs_invalid() {
        let nodes = Nodes::new();
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
            parse_mod(&mut Tokenizer::new(code), &nodes).unwrap_err();
        }
    }

    #[test]
    fn type_defs_valid() {
        let nodes = Nodes::new();
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
            parse_type_def(&mut Tokenizer::new(code), &nodes, None).unwrap();
        }
    }

    #[test]
    fn type_defs_invalid() {
        let nodes = Nodes::new();
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
            parse_type_def(&mut Tokenizer::new(code), &nodes, None)
                .map(|_| panic!(""))
                .unwrap_err();
        }
    }

    #[test]
    fn let_expr() {
        let nodes = Nodes::new();
        parse_let_expr(&mut Tokenizer::new("let foo = 10 + 12"), &nodes).unwrap();
        parse_let_expr(&mut Tokenizer::new("let foo = { 10 + 12; bar }"), &nodes).unwrap();
    }

    #[test]
    fn block_expr() {
        let nodes = Nodes::new();
        parse_block_expr(&mut Tokenizer::new("{ 10 + 14 - 2; -1; {10} }"), &nodes).unwrap();
    }

    #[test]
    fn fn_header() {
        let nodes = Nodes::new();

        // succeeds
        parse_fn(&mut Tokenizer::new("fn foo() { 1 }"), &nodes).unwrap();
        parse_fn(&mut Tokenizer::new("fn foo(foo: Bar) { 1 }"), &nodes).unwrap();
        parse_fn(&mut Tokenizer::new("fn foo() -> RetTy { 1 }"), &nodes).unwrap();
        parse_fn(
            &mut Tokenizer::new("fn foo(foo: Bar) -> RetTy { 1 }"),
            &nodes,
        )
        .unwrap();
        parse_fn(&mut Tokenizer::new("fn foo() -> RetTy { 1 }"), &nodes).unwrap();
        parse_fn(
            &mut Tokenizer::new("fn foo(foo: Bar,baz: Bar,) { 1 }"),
            &nodes,
        )
        .unwrap();

        // fails
        parse_fn(&mut Tokenizer::new("pub pub fn foo() { 1 }"), &nodes).unwrap_err();
        parse_fn(&mut Tokenizer::new("foo() { 1 }"), &nodes).unwrap_err();
        parse_fn(&mut Tokenizer::new("fn foo(foo:: Bar) { 1 }"), &nodes).unwrap_err();
        parse_fn(&mut Tokenizer::new("fn foo() -> Ty Ty { 1 }"), &nodes).unwrap_err();
        parse_fn(&mut Tokenizer::new("fn foo() -> { 1 }"), &nodes).unwrap_err();
        parse_fn(&mut Tokenizer::new("fn foo(Foo: Bar,,) -> { 1 }"), &nodes).unwrap_err();
    }

    #[test]
    fn braces() {
        let nodes = Nodes::new();
        parse_expr(&mut Tokenizer::new("1 * (2 + 3)"), &nodes, 0).unwrap();
        parse_expr(&mut Tokenizer::new("(1 + 2) * 3"), &nodes, 0).unwrap();
        parse_expr(&mut Tokenizer::new("((((((3))))))"), &nodes, 0).unwrap();
    }

    #[test]
    fn exprs() {
        let nodes = Nodes::new();
        parse_expr(&mut Tokenizer::new("1 + 2 / 3"), &nodes, 0).unwrap();
        parse_expr(&mut Tokenizer::new("1 / 2 + 3"), &nodes, 0).unwrap();
        parse_expr(&mut Tokenizer::new("1 + 2 - 3 + 4"), &nodes, 0).unwrap();
        parse_expr(&mut Tokenizer::new("3 * foo.bar.baz.blah + 2"), &nodes, 0).unwrap();
    }

    #[test]
    fn disambig_op() {
        let nodes = Nodes::new();
        parse_expr(&mut Tokenizer::new("1 - 2"), &nodes, 0).unwrap();
        parse_expr(&mut Tokenizer::new("1 - -2"), &nodes, 0).unwrap();
        parse_expr(&mut Tokenizer::new("-1 - -2"), &nodes, 0).unwrap();
    }
}
