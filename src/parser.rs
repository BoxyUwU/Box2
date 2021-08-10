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

fn parse_expr<'a>(tok: &mut Tokenizer<'a>, nodes: &mut Nodes, min_bp: u8) -> Option<NodeId> {
    let mut lhs = if let Some(unop) = tok.next_if_disambig_un_op() {
        let (_, r_bp) = unop.bp();
        let rhs = parse_expr(tok, nodes, r_bp)?;
        nodes.push_expr(ExprKind::UnOp(unop, rhs))
    } else if let Some(_) = tok.next_if(Token::LParen) {
        let inner = parse_expr(tok, nodes, 0)?;
        tok.next_if(Token::RParen)?;
        inner
    } else if let Some(ident) = tok.next_if_ident() {
        nodes.push_expr(ExprKind::Ident(ident.to_owned()))
    } else if let Some(lit) = tok.next_if_lit() {
        nodes.push_expr(ExprKind::Lit(lit))
    } else if let Some(_) = tok.peek_if(Token::LBrace) {
        parse_block_expr(tok, nodes)?
    } else if let Some(_) = tok.peek_if(Token::Kw(Kw::Let)) {
        parse_let_expr(tok, nodes)?
    } else {
        return None;
    };

    loop {
        let op = match tok.peek().and_then(Token::to_operator) {
            Some(op) => op.disambig_bin(),
            None => return Some(lhs),
        };
        let (l_bp, r_bp) = op.bp();
        let l_bp = l_bp.unwrap();

        if l_bp < min_bp {
            return Some(lhs);
        }
        tok.next().unwrap();

        let rhs = parse_expr(tok, nodes, r_bp)?;
        lhs = nodes.push_expr(ExprKind::BinOp(op.binop().unwrap(), lhs, rhs));
    }
}

fn parse_let_expr<'a>(tok: &mut Tokenizer<'a>, nodes: &mut Nodes) -> Option<NodeId> {
    tok.next_if(Token::Kw(Kw::Let))?;
    let name = tok.next_if_ident()?;
    tok.next_if(Token::Eq)?;
    let expr = parse_expr(tok, nodes, 0)?;
    Some(nodes.push_expr(ExprKind::Let(name.to_owned(), expr)))
}

pub fn parse_block_expr<'a>(tok: &mut Tokenizer<'a>, nodes: &mut Nodes) -> Option<NodeId> {
    tok.next_if(Token::LBrace)?;
    let mut stmts = vec![];
    while let None = tok.next_if(Token::RBrace) {
        let expr = parse_expr(tok, nodes, 0)?;
        let terminator = tok.next_if(Token::SemiColon).is_some();
        stmts.push((expr, terminator));
    }
    Some(nodes.push_expr(ExprKind::Block(stmts)))
}

fn parse_fn<'a>(tok: &mut Tokenizer<'a>, nodes: &mut Nodes) -> Option<NodeId> {
    // (pub)? fn ( (ident: ty),* ) (-> ty)? { expr }

    let visibility = tok.next_if(Token::Kw(Kw::Pub)).map(|_| Visibility::Pub);
    tok.next_if(Token::Kw(Kw::Fn))?;
    let name = tok.next_if_ident()?.to_owned();

    tok.next_if(Token::LParen)?;
    let mut params = Vec::new();
    while let Some(ident) = tok.next_if_ident() {
        tok.next_if(Token::Colon)?;
        let ty = tok.next_if_ident()?;
        params.push((ident.to_owned(), ty.to_owned()));

        match tok.next_if(Token::Comma) {
            Some(_) => continue,
            None => break,
        }
    }
    tok.next_if(Token::RParen)?;

    let mut ret_ty = None;
    if let Some(_) = tok.next_if(Token::Arrow) {
        ret_ty = Some(tok.next_if_ident()?.to_owned());
    }

    let body = parse_block_expr(tok, nodes)?;

    Some(nodes.push_fn(Fn {
        visibility,
        name,
        params,
        ret_ty,
        body,
    }))
}

fn parse_type_def<'a>(
    tok: &mut Tokenizer<'a>,
    nodes: &mut Nodes,
    parent_field: Option<String>,
) -> Option<NodeId> {
    let visibility = tok.next_if(Token::Kw(Kw::Pub)).map(|_| Visibility::Pub);
    tok.next_if(Token::Kw(Kw::Type))?;

    let mut name = tok.next_if_ident().map(|s| s.to_string());
    // type def is only permitted to not have a name if it is
    // the rhs of a field i.e. `field: type { ... }`
    if let None = name {
        name = Some(parent_field?); // FIXME change casing of `parent_field` to be type cased
    }

    tok.next_if(Token::LBrace)?;

    let mut variants = Vec::new();
    if let Some(_) = tok.peek_if(Token::UpLine) {
        // type { | Foo, | Bar, }
        while let None = tok.peek_if(Token::RBrace) {
            tok.next_if(Token::UpLine)?;
            let visibility = tok.next_if(Token::Kw(Kw::Pub)).map(|_| Visibility::Pub);
            let name = tok.next_if_ident()?.to_owned();
            tok.next_if(Token::LBrace)?;
            let Fields {
                type_defs,
                field_defs,
            } = parse_fields(tok, nodes)?;
            tok.next_if(Token::RBrace)?;

            let variant_id = nodes.push_variant_def(VariantDef {
                visibility,
                name: Some(name),
                type_defs,
                field_defs,
            });
            variants.push(variant_id);

            match tok.next_if(Token::Comma) {
                Some(_) => continue,
                None => break,
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

    tok.next_if(Token::RBrace)?;

    let id = nodes.push_type_def(TypeDef {
        visibility,
        name,
        variants,
    });
    Some(id)
}

struct Fields {
    type_defs: Vec<NodeId>,
    field_defs: Vec<NodeId>,
}

fn parse_fields<'a>(tok: &mut Tokenizer<'a>, nodes: &mut Nodes) -> Option<Fields> {
    let mut type_defs = Vec::new();
    let mut field_defs = Vec::new();

    while let None = tok.peek_if(Token::RBrace) {
        let visibility = tok.next_if(Token::Kw(Kw::Pub)).map(|_| Visibility::Pub);
        let name = tok.next_if_ident()?.to_string();
        tok.next_if(Token::Colon)?;

        let ty = match tok.peek() {
            Some(Token::Kw(Kw::Type | Kw::Pub)) => {
                let ty_def_id = parse_type_def(tok, nodes, Some(name.clone()))?;
                type_defs.push(ty_def_id);
                ty_def_id
            }
            Some(Token::Ident(_)) => {
                let ty = unwrap_matches!(tok.next(), Some(Token::Ident(ty)) => ty);
                nodes.push_expr(ExprKind::Ident(ty.to_string()))
            }
            _ => return None,
        };

        field_defs.push(nodes.push_field_def(FieldDef {
            visibility,
            name,
            ty,
        }));

        match tok.next_if(Token::Comma) {
            Some(_) => continue,
            None => break,
        }
    }

    Some(Fields {
        type_defs,
        field_defs,
    })
}

#[cfg(test)]
mod test {
    use super::*;

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
            parse_type_def(&mut Tokenizer::new(code), &mut nodes, None).map(|_| panic!(""));
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
        parse_fn(&mut Tokenizer::new("pub pub fn foo() { 1 }"), &mut nodes).map(|_| panic!(""));
        parse_fn(&mut Tokenizer::new("foo() { 1 }"), &mut nodes).map(|_| panic!(""));
        parse_fn(&mut Tokenizer::new("fn foo(foo:: Bar) { 1 }"), &mut nodes).map(|_| panic!(""));
        parse_fn(&mut Tokenizer::new("fn foo() -> Ty Ty { 1 }"), &mut nodes).map(|_| panic!(""));
        parse_fn(&mut Tokenizer::new("fn foo() -> { 1 }"), &mut nodes).map(|_| panic!(""));
        parse_fn(
            &mut Tokenizer::new("fn foo(Foo: Bar,,) -> { 1 }"),
            &mut nodes,
        )
        .map(|_| panic!(""));
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
