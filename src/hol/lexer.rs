#[derive(Debug)]
pub enum Token<'a> {
  Ident(&'a str),
  Type(u32),
  Term(u32),
  Fetch(u32),
  Subproof(u32),
  Str(&'a str),
  Int(&'a str),
  Heading(&'a str),
  Char(char),
  Eol,
}

fn is_digit(c: u8) -> bool { (b'0'..=b'9').contains(&c) }
fn is_alpha(c: u8) -> bool { (b'A'..=b'Z').contains(&c) || (b'a'..=b'z').contains(&c) }
fn is_alphanum(c: u8) -> bool { is_alpha(c) || is_digit(c) }
fn as_digit(c: u8) -> Option<u8> { if is_digit(c) { Some(c - b'0') } else { None } }

pub struct Lexer<I> {
  input: I,
  buf: Vec<u8>,
  peek: u8,
}

impl<I> Lexer<I> {
  fn buf(&self) -> &str {
    unsafe { std::str::from_utf8_unchecked(&self.buf) }
  }
}

impl<I: Iterator<Item=u8>> Lexer<I> {
  pub fn from(input: I) -> Self {
    let mut lex = Self {input, buf: vec![], peek: 0};
    lex.bump();
    lex
  }

  fn bump_opt(&mut self) -> Option<u8> {
    let peeked = self.input.next()?;
    self.peek = peeked;
    Some(peeked)
  }

  fn bump(&mut self) -> u8 {
    self.peek = self.bump_opt().unwrap_or(0);
    self.peek
  }

  fn lex_while_inclusive(&mut self, f: impl Fn(u8) -> bool) -> &str {
    self.buf.clear();
    loop {
      self.buf.push(self.peek);
      if !f(self.bump()) { return self.buf() }
    }
  }

  fn lex_while(&mut self, f: impl Fn(u8) -> bool) -> &str {
    self.buf.clear();
    while f(self.bump()) { self.buf.push(self.peek) }
    self.buf()
  }

  fn lex_int(&mut self) -> u32 {
    assert!(is_digit(self.bump()));
    let mut n: u32 = (self.peek - b'0').into();
    while is_digit(self.bump()) {
      n = n.checked_mul(10).unwrap().checked_add((self.peek - b'0').into()).unwrap();
    }
    n
  }

  pub fn next(&mut self) -> Option<Token<'_>> {
    loop {
      match self.peek {
        b'\n' => { self.bump(); return Some(Token::Eol) }
        0 => return None,
        b' ' | b'\t' => { self.bump(); }
        b'#' => loop {
          match self.bump() {
            b'\n' => { self.bump(); return Some(Token::Eol) }
            0 => return None,
            _ => {}
          }
        }
        b'A'..=b'Z' => return Some(Token::Ident(self.lex_while_inclusive(is_alphanum))),
        b'z' => return Some(Token::Type(self.lex_int())),
        b't' => return Some(Token::Term(self.lex_int())),
        b'f' => return Some(Token::Fetch(self.lex_int())),
        b's' => return Some(Token::Subproof(self.lex_int())),
        b'>' => return Some(Token::Heading(self.lex_while(is_alphanum))),
        b'0'..=b'9' => return Some(Token::Int(self.lex_while_inclusive(is_digit))),
        b'"' => {
          self.buf.clear();
          loop {
            match self.bump() {
              b'\n' | 0 => panic!("unclosed string literal"),
              b'"' => {
                self.bump();
                return Some(Token::Str(std::str::from_utf8(&self.buf).unwrap()))
              }
              b'\\' => match self.bump() {
                b'\\' | b'"' => self.buf.push(self.peek),
                c1 => {
                  let c1 = as_digit(c1).expect("invalid escape");
                  let c2 = as_digit(self.bump()).expect("invalid escape");
                  let c3 = as_digit(self.bump()).expect("invalid escape");
                  self.buf.push((c1 * 10 + c2).checked_mul(10).unwrap().checked_add(c3).unwrap())
                }
              }
              c => self.buf.push(c),
            }
          }
        }
        c => { self.bump(); return Some(Token::Char(c as _)) }
      }
    }
  }
}

#[derive(Debug, Copy, Clone)]
pub enum PackedToken {
  Ident,
  Type(u32),
  Term(u32),
  Fetch(u32),
  Subproof(u32),
  Str,
  Int,
  Heading,
  Char(char),
  Eol,
}

impl Token<'_> {
  pub fn pack(self) -> PackedToken {
    match self {
        Token::Ident(_)    => PackedToken::Ident,
        Token::Type(n)     => PackedToken::Type(n),
        Token::Term(n)     => PackedToken::Term(n),
        Token::Fetch(n)    => PackedToken::Fetch(n),
        Token::Subproof(n) => PackedToken::Subproof(n),
        Token::Str(_)      => PackedToken::Str,
        Token::Int(_)      => PackedToken::Int,
        Token::Heading(_)  => PackedToken::Heading,
        Token::Char(n)     => PackedToken::Char(n),
        Token::Eol         => PackedToken::Eol,
    }
  }
}

impl PackedToken {
  pub fn unpack<I>(self, lexer: &Lexer<I>) -> Token<'_> {
    match self {
        PackedToken::Ident       => Token::Ident(lexer.buf()),
        PackedToken::Type(n)     => Token::Type(n),
        PackedToken::Term(n)     => Token::Term(n),
        PackedToken::Fetch(n)    => Token::Fetch(n),
        PackedToken::Subproof(n) => Token::Subproof(n),
        PackedToken::Str         => Token::Str(lexer.buf()),
        PackedToken::Int         => Token::Int(lexer.buf()),
        PackedToken::Heading     => Token::Heading(lexer.buf()),
        PackedToken::Char(n)     => Token::Char(n),
        PackedToken::Eol         => Token::Eol,
    }
  }
}

impl<I> Lexer<I> {
  pub fn unpack(&mut self, tk: Option<PackedToken>) -> Option<Token<'_>> {
    Some(tk?.unpack(self))
  }
}
