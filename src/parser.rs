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

fn parse_block_expr<'a>(tok: &mut Tokenizer<'a>, nodes: &mut Nodes) -> Option<NodeId> {
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

#[cfg(test)]
mod test {
    use super::*;

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
