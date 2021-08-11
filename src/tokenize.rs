use logos::Logos;
use std::{ops::Range, str::FromStr};

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Literal {
    Float(f64),
    Int(u64),
}

impl Literal {
    fn float_from_lex<'a>(lex: &mut logos::Lexer<'a, Token<'a>>) -> Self {
        Self::Float(f64::from_str(lex.slice()).unwrap())
    }

    fn int_from_lex<'a>(lex: &mut logos::Lexer<'a, Token<'a>>) -> Self {
        Self::Int(u64::from_str(lex.slice()).unwrap())
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Kw {
    Mod,
    Let,
    Fn,
    Pub,
    Type,
}

#[derive(Logos, Copy, Clone, Debug, PartialEq)]
pub enum Token<'a> {
    #[regex("[a-zA-Z_-]+", |lex| lex.slice())]
    Ident(&'a str),
    #[regex("[0-9]+", Literal::int_from_lex)]
    #[regex(r"[0-9]+\.[0-9]+", Literal::float_from_lex)]
    Literal(Literal),

    #[token("+")]
    Plus,
    #[token("-")]
    Hyphen,
    #[token("*")]
    Star,
    #[token("/")]
    FwdSlash,

    #[token("mod", |_| Kw::Mod)]
    #[token("let", |_| Kw::Let)]
    #[token("fn", |_| Kw::Fn)]
    #[token("pub", |_| Kw::Pub)]
    #[token("type", |_| Kw::Type)]
    Kw(Kw),

    #[token("|")]
    UpLine,
    #[token("->")]
    Arrow,
    #[token(":")]
    Colon,
    #[token(";")]
    SemiColon,
    #[token(",")]
    Comma,
    #[token("=")]
    Eq,

    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Error,
}

struct PeekableTwo<I: Iterator> {
    iter: I,
    peeked: [Option<I::Item>; 2],
}

impl<I: Iterator> PeekableTwo<I> {
    pub fn new(iter: I) -> Self {
        Self {
            iter,
            peeked: [None, None],
        }
    }

    pub fn peek(&mut self) -> Option<&I::Item> {
        if let None = &self.peeked[0] {
            self.peeked[0] = Some(self.iter.next())?;
        }
        self.peeked[0].as_ref()
    }

    pub fn peek_second(&mut self) -> Option<&I::Item> {
        self.peek()?;
        if let None = &self.peeked[1] {
            self.peeked[1] = Some(self.iter.next())?;
        }
        self.peeked[1].as_ref()
    }

    pub fn next(&mut self) -> Option<I::Item> {
        self.peek()?;
        let [first, second] = &mut self.peeked;
        std::mem::swap(first, second);
        second.take()
    }
}

type Span = Range<usize>;
pub struct Tokenizer<'a> {
    lex: PeekableTwo<logos::SpannedIter<'a, Token<'a>>>,
}

impl<'a> Tokenizer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            lex: PeekableTwo::new(Token::lexer(src).spanned()),
        }
    }

    pub fn peek(&mut self) -> Option<&(Token<'a>, Span)> {
        self.lex.peek()
    }

    pub fn peek_second(&mut self) -> Option<&(Token<'a>, Span)> {
        self.lex.peek_second()
    }

    #[must_use]
    pub fn next_if(&mut self, expected: Token<'a>) -> Result<(Token<'a>, Span), (Token<'a>, Span)> {
        match self.peek() {
            Some((tok, span)) if tok == &expected => {
                let span = span.clone();
                self.next().unwrap();
                Ok((expected, span))
            }
            Some(r) => Err(r.clone()),
            _ => Err((Token::Error, 0..0)),
        }
    }

    #[must_use]
    pub fn peek_if(&mut self, expected: Token<'a>) -> Result<(Token<'a>, Span), (Token<'a>, Span)> {
        match self.peek() {
            Some((tok, span)) if tok == &expected => Ok((expected, span.clone())),
            Some(r) => Err(r.clone()),
            _ => Err((Token::Error, 0..0)),
        }
    }

    #[must_use]
    pub fn next_if_ident(&mut self) -> Result<(&'a str, Span), (Token<'a>, Span)> {
        match self.peek() {
            Some((Token::Ident(_), _)) => {
                Ok(unwrap_matches!(self.next(), Some((Token::Ident(ident), span)) => (ident, span)))
            }
            Some(r) => Err(r.clone()),
            _ => Err((Token::Error, 0..0)),
        }
    }

    #[must_use]
    pub fn peek_if_ident(&mut self) -> Result<(&'a str, Span), (Token<'a>, Span)> {
        match self.peek() {
            Some((Token::Ident(ident), span)) => Ok((ident, span.clone())),
            Some(r) => Err(r.clone()),
            _ => Err((Token::Error, 0..0)),
        }
    }

    #[must_use]
    pub fn next_if_lit(&mut self) -> Result<(Literal, Span), (Token<'a>, Span)> {
        match self.peek() {
            Some((Token::Literal(_), _)) => {
                unwrap_matches!(self.next(), Some((Token::Literal(l), span)) => Ok((l, span)))
            }
            Some(r) => Err(r.clone()),
            _ => Err((Token::Error, 0..0)),
        }
    }
}

impl<'a> Iterator for Tokenizer<'a> {
    type Item = (Token<'a>, Span);

    fn next(&mut self) -> Option<(Token<'a>, Span)> {
        self.lex.next()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn foo() {
        dbg!(Tokenizer::new("1 + 2 + 133.21 / 3 - hello (foo)").collect::<Vec<_>>());
    }
}
