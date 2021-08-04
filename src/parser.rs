use crate::tokenize::{Token, Tokenizer};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct NodeId(usize);

#[derive(Debug)]
struct Node {
    id: NodeId,
    kind: NodeKind,
}

#[derive(Clone, Debug, PartialEq)]
enum NodeKind {
    BinOp(BinOp, NodeId, NodeId),
    UnOp(UnOp, NodeId),
    Bottom(Bottom),
}

impl NodeKind {
    fn op_string(&self) -> String {
        match self {
            NodeKind::BinOp(op, _, _) => match op {
                BinOp::Add => "+".into(),
                BinOp::Sub => "-".into(),
                BinOp::Div => "/".into(),
                BinOp::Mul => "*".into(),
            },
            NodeKind::UnOp(op, _) => match op {
                UnOp::Neg => "-".into(),
            },
            NodeKind::Bottom(bottom) => match bottom {
                Bottom::Float(f) => f.to_string(),
                Bottom::Int(i) => i.to_string(),
                Bottom::Ident(ident) => ident.to_string(),
            },
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
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

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum UnOp {
    Neg,
}

impl UnOp {
    /// Option is always `None`
    fn bp(&self) -> (Option<u8>, u8) {
        match self {
            UnOp::Neg => (None, 5),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
enum Bottom {
    Int(u64),
    Float(f64),
    Ident(String),
}

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

#[derive(Debug)]
struct Nodes(Vec<Node>);

impl Nodes {
    fn new(&mut self, kind: NodeKind) -> NodeId {
        let id = NodeId(self.0.len());
        self.0.push(Node { id, kind });
        id
    }
}

impl std::fmt::Display for Nodes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.last() {
            Some(_) => {
                fn print_node(
                    f: &mut std::fmt::Formatter<'_>,
                    nodes: &Nodes,
                    node: NodeId,
                ) -> std::fmt::Result {
                    let kind = (&nodes.0[node.0]).kind.clone();
                    let op_str = &kind.op_string();

                    match kind {
                        NodeKind::Bottom(_) => {
                            f.write_str(op_str)?;
                        }
                        NodeKind::BinOp(_, lhs, rhs) => {
                            f.write_str("(")?;
                            f.write_str(op_str)?;
                            f.write_str(" ")?;
                            print_node(f, nodes, lhs)?;
                            f.write_str(" ")?;
                            print_node(f, nodes, rhs)?;
                            f.write_str(")")?;
                        }
                        NodeKind::UnOp(_, lhs) => {
                            f.write_str("(")?;
                            f.write_str(op_str)?;
                            f.write_str(" ")?;
                            print_node(f, nodes, lhs)?;
                            f.write_str(")")?;
                        }
                    }
                    Ok(())
                }
                print_node(f, self, NodeId(self.0.len() - 1))
            }
            None => Ok(()),
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
        nodes.new(NodeKind::UnOp(unop, rhs))
    } else if let Some(_) = tok.next_if(Token::LParen) {
        let inner = parse_expr(tok, nodes, 0)?;
        tok.next_if(Token::RParen)?;
        inner
    } else {
        parse_bottom(tok, nodes)?
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
        lhs = nodes.new(NodeKind::BinOp(op.binop().unwrap(), lhs, rhs));
    }
}

fn parse_bottom<'a>(tok: &mut Tokenizer<'a>, nodes: &mut Nodes) -> Option<NodeId> {
    use crate::tokenize::Literal;

    let bottom = match tok.next_if_bottom()? {
        Token::Literal(Literal::Float(f)) => Bottom::Float(f),
        Token::Literal(Literal::Int(i)) => Bottom::Int(i),
        Token::Ident(ident) => Bottom::Ident(ident.to_owned()),
        _ => return None,
    };

    Some(nodes.new(NodeKind::Bottom(bottom)))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn braces() {
        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 * (2 + 3)"), &mut nodes, 0);
        assert_eq!(&nodes.to_string(), "(* 1 (+ 2 3))");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("(1 + 2) * 3"), &mut nodes, 0);
        assert_eq!(&nodes.to_string(), "(* (+ 1 2) 3)");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("((((((3))))))"), &mut nodes, 0);
        assert_eq!(&nodes.to_string(), "3");
    }

    #[test]
    fn exprs() {
        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 + 2 / 3"), &mut nodes, 0);
        assert_eq!(&nodes.to_string(), "(+ 1 (/ 2 3))");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 / 2 + 3"), &mut nodes, 0);
        assert_eq!(&nodes.to_string(), "(+ (/ 1 2) 3)");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 + 2 - 3 + 4"), &mut nodes, 0);
        assert_eq!(&nodes.to_string(), "(+ (- (+ 1 2) 3) 4)");
    }

    #[test]
    fn disambig() {
        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 - 2"), &mut nodes, 0);
        assert_eq!(&nodes.to_string(), "(- 1 2)");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("1 - -2"), &mut nodes, 0);
        assert_eq!(&nodes.to_string(), "(- 1 (- 2))");

        let mut nodes = Nodes(vec![]);
        parse_expr(&mut Tokenizer::new("-1 - -2"), &mut nodes, 0);
        assert_eq!(&nodes.to_string(), "(- (- 1) (- 2))");
    }
}
