use std::convert::TryFrom;
use std::fs::File;
use std::io::Read;

use crate::{Dedup, Importer};
use crate::lexer::{Token, PackedToken, Lexer};
use crate::types::*;

const COMMONHOL_VERSION: &str = "0.5";
// const HOL_ZERO: &str = "HOL Zero";

pub struct Summary<I> {
  pub hol_system: String,
  pub hol_version: String,
  lexer: Lexer<I>,
  next: Option<ObjectSpec>,
}

macro_rules! parse {
  ($lexer:expr, $tk:ident;) => {};
  ($lexer:expr, $tk:ident; let $x:pat = $pat:pat => $e:expr, $($es:tt)*) => {
    let $x = if let Some($pat) = $tk { $e } else { panic!("parse failed") };
    $tk = $lexer.next();
    parse!($lexer, $tk; $($es)*)
  };
  ($lexer:expr, $tk:ident; let $x:pat = Opt($e:pat), $($es:tt)*) => {
    let $x = matches!($tk, Some($e)) && { $tk = $lexer.next(); true };
    parse!($lexer, $tk; $($es)*)
  };
  ($lexer:expr, $tk:ident; $pat:pat => $e:expr, $($es:tt)*) => {
    if let Some($pat) = $tk { $e } else { panic!("parse failed") };
    $tk = $lexer.next();
    parse!($lexer, $tk; $($es)*)
  };
  ($lexer:expr, $tk:ident; Eols, $($es:tt)*) => {
    while let Some(Token::Eol) = $tk { $tk = $lexer.next() }
    parse!($lexer, $tk; $($es)*)
  };
  ($lexer:expr, $tk:ident; $pat:pat, $($es:tt)*) => {
    if let Some($pat) = $tk { } else { panic!("parse failed") }
    $tk = $lexer.next();
    parse!($lexer, $tk; $($es)*)
  };
}

impl<I: Iterator<Item=u8>> Summary<I> {
  pub fn from(input: I) -> Self {
    use Token::*;
    let mut lexer = Lexer::from(input);
    let mut tk = lexer.next();
    parse! { lexer, tk;
      Heading("Common"), Ident("HOL"), Ident("Version"), Char(':'),
      Str(v) => assert!(v == COMMONHOL_VERSION, "unsupported Common HOL version"), Eols,
      Heading("HOL"), Ident("System"), Char(':'),
        let hol_system = Str(v) => v.to_owned(), Eols,
      Heading("HOL"), Ident("System"), Ident("Version"), Char(':'),
        let hol_version = Str(v) => v.to_owned(), Eols,
      Heading(""), Eols,
    }
    let next = tk.map(From::from);
    Self { hol_system, hol_version, lexer, next }
  }
}

impl From<Token<'_>> for ObjectSpec {
  fn from(tk: Token<'_>) -> ObjectSpec {
    match tk {
      Token::Ident(v) => ObjectSpec::try_from(v).unwrap(),
      _ => panic!("parse error"),
    }
  }
}

struct Abbrev<'a>(&'a str);
impl TryFrom<Abbrev<'_>> for ObjectSpec {
  type Error = ();

  fn try_from(value: Abbrev<'_>) -> Result<Self, Self::Error> {
    match value.0 {
      "Z"   => Ok(Self::TypeDecl(Default::default())),
      "C"   => Ok(Self::ConstDecl(Default::default())),
      "A"   => Ok(Self::Axiom(Default::default())),
      "BD"  => Ok(Self::BasicDef(Default::default())),
      "D"   => Ok(Self::Def(Default::default())),
      "S"   => Ok(Self::Spec(Default::default())),
      "BZD" => Ok(Self::BasicTypedef(Default::default())),
      "ZD"  => Ok(Self::Typedef(Default::default())),
      "ZB"  => Ok(Self::TypeBij(Default::default())),
      "T"   => Ok(Self::Thm(Default::default())),
      "O"   => Ok(Self::OpenThm(Default::default())),
      "N"   => Ok(Self::NumThm(Default::default())),
      _     => Err(())
    }
  }
}

impl TryFrom<&str> for ObjectSpec {
  type Error = ();
  fn try_from(value: &str) -> Result<Self, Self::Error> {
    match value {
      "Typedecl"     => Ok(Self::TypeDecl(Default::default())),
      "Constdecl"    => Ok(Self::ConstDecl(Default::default())),
      "Axiom"        => Ok(Self::Axiom(Default::default())),
      "Basicdef"     => Ok(Self::BasicDef(Default::default())),
      "Def"          => Ok(Self::Def(Default::default())),
      "Spec"         => Ok(Self::Spec(Default::default())),
      "Basictypedef" => Ok(Self::BasicTypedef(Default::default())),
      "Typedef"      => Ok(Self::Typedef(Default::default())),
      "Typebij"      => Ok(Self::TypeBij(Default::default())),
      "Thm"          => Ok(Self::Thm(Default::default())),
      "Othm"         => Ok(Self::OpenThm(Default::default())),
      "Nthm"         => Ok(Self::NumThm(Default::default())),
      _              => Err(())
    }
  }
}

impl ObjectSpec {
  fn set_args(&mut self, args: Vec<String>) {
    match self {
      Self::Spec(s) => *s = args.into(),
      Self::TypeBij(s) => **s = <[String; 3]>::try_from(args).unwrap(),
      Self::TypeDecl(s) |
      Self::ConstDecl(s) |
      Self::Axiom(s) |
      Self::BasicDef(s) |
      Self::Def(s) |
      Self::BasicTypedef(s) |
      Self::Typedef(s) |
      Self::Thm(s) |
      Self::OpenThm(s) => {
        let [a] = <[_; 1]>::try_from(args).unwrap();
        *s = a
      }
      Self::NumThm(n) => {
        let [a] = <[_; 1]>::try_from(args).unwrap();
        *n = a.parse().unwrap();
      }
    }
  }
}

impl TryFrom<&str> for FetchKind {
  type Error = ();

  fn try_from(value: &str) -> Result<Self, Self::Error> {
    match value {
      "A"    => Ok(Self::Axiom),
      "BD"   => Ok(Self::BasicDef),
      "D"    => Ok(Self::Def),
      "S"    => Ok(Self::Spec),
      "SI"   => Ok(Self::SpecInput),
      "BZD"  => Ok(Self::BasicTypedef),
      "BZDI" => Ok(Self::BasicTypedefInput),
      "ZD"   => Ok(Self::Typedef),
      "ZDI"  => Ok(Self::TypedefInput),
      "ZB1"  => Ok(Self::TypeBij1),
      "ZB2"  => Ok(Self::TypeBij2),
      "T"    => Ok(Self::Thm),
      "O"    => Ok(Self::OThm),
      "N"    => Ok(Self::NThm),
      _      => Err(()),
    }
  }
}

impl<I: Iterator<Item=u8>> Iterator for Summary<I> {
  type Item = (ObjectSpec, ObjectData);

  fn next(&mut self) -> Option<Self::Item> {
    use Token::*;
    let mut kind = self.next.take()?;
    let mut tk = self.lexer.next();
    let mut args = vec![];
    while let Some(Str(v)) = tk {
      args.push(v.to_owned());
      tk = self.lexer.next();
    }
    kind.set_args(args);
    parse! { self.lexer, tk;
      let fl1 = Opt(Char('+')),
      let fl2 = Opt(Char('*')),
      Char(':'),
      let file = Str(v) => v.to_owned(), Eols,
    }
    self.next = tk.map(From::from);

    Some((kind, ObjectData { fl1, fl2, file }))
  }
}

// pub fn import_trans_table(rpath: &Path, src: &str, predefs: &Predefs) -> Option<TransTable> {
//   let mut lexer = match File::open(rpath.join("HOL_TRANS_TABLE")) {
//     Err(e) if matches!(e.kind(), io::ErrorKind::NotFound) => return None,
//     file => Lexer::from(file.unwrap().bytes().map(Result::unwrap)),
//   };
//   use Token::{Heading, Ident, Char, Str};
//   let mut tk = lexer.next();
//   parse! { lexer, tk;
//     Heading("Common"), Ident("HOL"), Ident("Version"), Char(':'), Str(COMMONHOL_VERSION), Eols,
//   }
//   macro_rules! parse_line {($i:ident, $($t:tt)*) => {{
//     let mut $i = 0usize;
//     loop {
//       parse! { lexer, tk; $($t)*, }
//       if matches!(tk, Some(Char(':'))) {
//         tk = lexer.next();
//       } else {
//         parse! { lexer, tk; Eols, }
//         break
//       }
//       $i += 1;
//     }
//   }}}

//   let (mut from, mut to) = (None, None);
//   parse_line! { i, Str(v) =>
//     if v == HOL_ZERO { to = Some(i) } else if v == src { from = Some(i) }
//   }
//   let (from, to) = (from.unwrap(), to.unwrap());
//   parse! { lexer, tk; Heading(""), Eols, }
//   macro_rules! parse_sections {
//     ($(let $out:ident: $ty:ty = $name:expr, $decode:ident, $unwrap:expr, $insert:expr,
//         [$($v:pat => |$k:ident| $e:expr),*];
//     )*) => {$(
//       parse! { lexer, tk; Heading($name), Eols, }
//       while let Some(Str(_) | Ident(_)) = tk {
//         let (mut key, mut value) = <($ty, $ty)>::default();
//         parse_line! { i, $($v =>
//           if i == from { let $k = &mut key; $e } else
//           if i == to { let $k = &mut value; $e }),*
//         }
//         let value = $unwrap(value);
//         let value = predefs.$decode(&value).unwrap_or_else(|| panic!("missing primitive: {:?}", value));
//         $insert($unwrap(key), value);
//       }
//     )*}
//   }
//   let mut trans = TransTable::default();
//   parse_sections! {
//     let tyops: _ = "Tyops", decode_tyop, Option::unwrap,
//       |k, v| assert!(trans.tyops.insert(k, v).is_none()),
//       [Str(v) => |k| *k = Some(v.to_owned())];
//     let consts: _ = "Consts", decode_const, Option::unwrap,
//       |k, v| assert!(trans.consts.insert(k, v).is_none()),
//       [Str(v) => |k| *k = Some(v.to_owned())];
//     let fetches: (Option<_>, Option<_>) = "Fetches", decode_fetch,
//       |(a, b): (Option<_>, Option<_>)| Fetch(a.unwrap(), b.unwrap()),
//       |Fetch(k, s), v| {
//         println!("insert {:?}, {:?} = {:?}", k, s, v);
//         trans.fetches[k].insert(s, v)
//       },
//       [
//         Ident(v) => |k| k.0 = Some(FetchKind::try_from(v).unwrap()),
//         Str(v) => |k| k.1 = Some(v.to_owned())
//       ];
//   }
//   assert!(matches!(tk, None));
//   Some(trans)
// }

fn parse_type<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, de: &mut Dedup<Type>
) -> TypeId {
  #[derive(Debug)]
  enum Stack {
    Paren,
    Fun,
    Fun1(TypeId),
    Comp(String, Vec<TypeId>),
  }
  #[derive(Debug)]
  enum State {
    Start,
    Ret(TypeId),
  }
  let mut stk = vec![];
  let mut tk = lexer.unpack(*ptk);
  use Token::{Char, Ident, Str, Type as TType};
  let mut state = State::Start;
  loop {
    // println!("{:?}: state = {:?}, stack = {:?}", tk, state, stk);
    state = match state {
      State::Start => match tk {
        Some(TType(i)) => { tk = lexer.next(); State::Ret(de.reuse(de.named(i))) }
        Some(Char('(')) => { tk = lexer.next(); stk.push(Stack::Paren); State::Start }
        Some(Ident("V")) => { tk = lexer.next();
          parse! { lexer, tk; let x = Str(v) => v.to_owned(), }
          State::Ret(de.add(Type::Var(x)))
        }
        Some(Ident("K")) => { tk = lexer.next();
          parse! { lexer, tk; let x = Str(v) => v.to_owned(), }
          stk.push(Stack::Comp(x, vec![]));
          State::Start
        }
        Some(Ident("F")) => { tk = lexer.next();
          stk.push(Stack::Fun);
          State::Start
        }
        ref tk => match stk.pop() {
          Some(Stack::Comp(x, args)) => State::Ret(de.add(Type::Comp(x, args))),
          _ => panic!("parse_type parse error: {:?}", tk)
        }
      }
      State::Ret(ty) => match stk.pop() {
        Some(Stack::Paren) => {
          parse! { lexer, tk; Char(')'), }
          State::Ret(ty)
        }
        Some(Stack::Fun) => {
          stk.push(Stack::Fun1(ty));
          State::Start
        }
        Some(Stack::Fun1(ty1)) => {
          State::Ret(de.add(Type::Fun(ty1, ty)))
        }
        Some(Stack::Comp(x, mut args)) => {
          args.push(ty);
          stk.push(Stack::Comp(x, args));
          State::Start
        }
        None => {
          parse! { lexer, tk; Eols, }
          *ptk = tk.map(Token::pack);
          return ty
        }
      }
    }
  }
}

fn parse_type_preamble<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>
) -> Dedup<Type> {
  let mut de = Dedup::new();
  if matches!(lexer.unpack(*ptk), Some(Token::Heading("Types"))) {
    let mut tk = lexer.next();
    parse! { lexer, tk; Eols, }
    while let Some(Token::Int(v)) = tk {
      assert_eq!(v.parse::<usize>().unwrap(), de.named.len());
      *ptk = lexer.next().map(Token::pack);
      let n = parse_type(ptk, lexer, &mut de);
      de.named.push(Idx::into_u32(n));
      tk = lexer.unpack(*ptk);
      parse! { lexer, tk; Eols, }
    }
  }
  de
}

fn parse_term<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>,
  tys: &Dedup<Type>, de: &mut Dedup<Term>
) -> TermId {
  #[derive(Debug)]
  enum Stack {
    Paren,
    Binop(Binop),
    Binop1(Binop, TermId),
    Bin0,
    Not,
  }
  #[derive(Debug)]
  enum Binop {
    Comb,
    Bin(Binary),
    Quant(Quant),
  }
  #[derive(Debug)]
  enum State {
    Start,
    Ret(TermId),
  }
  let mut stk = vec![];
  let mut tk = lexer.unpack(*ptk);
  use Token::{Char, Ident, Str, Int, Type as TType, Term as TTerm};
  let mut state = State::Start;
  loop {
    // println!("{:?}: state = {:?}, stack = {:?}", tk, state, stk);
    state = match state {
      State::Start => match tk.unwrap() {
        TTerm(i) => { tk = lexer.next(); State::Ret(de.reuse(de.named(i))) }
        Char('(') => { tk = lexer.next(); stk.push(Stack::Paren); State::Start }
        Ident("V") => { tk = lexer.next();
          parse! { lexer, tk; let x = Str(v) => v.to_owned(), let n = TType(v) => tys.named(v), }
          State::Ret(de.add(Term::Var(x, n)))
        }
        Ident("K") => { tk = lexer.next();
          parse! { lexer, tk; let x = Str(v) => v.to_owned(), }
          let mut args = vec![];
          while let Some(TType(i)) = tk {
            tk = lexer.next();
            args.push(tys.named(i))
          }
          State::Ret(de.add(Term::OConst(x, args)))
        }
        Ident("M") => { tk = lexer.next();
          parse! { lexer, tk; let n = Int(v) => v.parse().unwrap(), }
          State::Ret(de.add(Term::BigInt(n)))
        }
        Ident("A") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Comb));
          State::Start
        }
        Ident("L") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Quant(Quant::Lambda)));
          State::Start
        }
        Ident("B") => { tk = lexer.next();
          stk.push(Stack::Bin0);
          State::Start
        }
        Ident("E") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Bin(Binary::Eq)));
          State::Start
        }
        Ident("N") => { tk = lexer.next();
          stk.push(Stack::Not);
          State::Start
        }
        Ident("C") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Bin(Binary::Conj)));
          State::Start
        }
        Ident("D") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Bin(Binary::Disj)));
          State::Start
        }
        Ident("I") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Bin(Binary::Imp)));
          State::Start
        }
        Ident("P") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Bin(Binary::Pair)));
          State::Start
        }
        Ident("X") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Quant(Quant::Exists)));
          State::Start
        }
        Ident("UX") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Quant(Quant::UExists)));
          State::Start
        }
        Ident("U") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Quant(Quant::Forall)));
          State::Start
        }
        Ident("S") => { tk = lexer.next();
          stk.push(Stack::Binop(Binop::Quant(Quant::Select)));
          State::Start
        }
        ref tk => panic!("parse_term parse error: {:?}", tk)
      }
      State::Ret(tm) => match stk.pop() {
        Some(Stack::Paren) => {
          parse! { lexer, tk; Char(')'), }
          State::Ret(tm)
        }
        Some(Stack::Not) => State::Ret(de.add(Term::Not(tm))),
        Some(Stack::Bin0) => {
          stk.push(Stack::Binop(Binop::Bin(Binary::Bin(tm))));
          State::Start
        }
        Some(Stack::Binop(o)) => { stk.push(Stack::Binop1(o, tm)); State::Start }
        Some(Stack::Binop1(o, tm1)) => State::Ret(de.add(match o {
          Binop::Comb => Term::Comb(tm1, tm),
          Binop::Quant(q) => Term::Quant(q, tm1, tm),
          Binop::Bin(b) => Term::Binary(b, tm1, tm),
        })),
        None => {
          parse! { lexer, tk; Eols, }
          *ptk = tk.map(Token::pack);
          return tm
        }
      }
    }
  }
}

fn parse_proof<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>,
  p: &Preambles, de: &mut Dedup<Proof>
) -> ProofId {
  #[derive(Debug)]
  enum Binary {
    Choose(TermId),
    Conj,
    DeductAntiSym,
    DisjCases,
    DisjCases1(ProofId),
    EqMp,
    ImpAntiSym,
    ImpTrans,
    Mp,
    ProveAsm,
    Trans,
    Comb,
    Bin(self::Binary),
  }
  #[derive(Debug)]
  enum Unary {
    AddAsm(TermId),
    Binary(Binary),
    Binary1(Binary, ProofId),
    CContr(TermId),
    Conj1,
    Conj2,
    Contr(TermId),
    Disch(TermId),
    Disj1,
    Disj2(TermId),
    EqfElim,
    EqfIntro,
    EqImp1,
    EqImp2,
    EqtElim,
    EqtIntro,
    Exists(TermId, TermId),
    Gen(TermId),
    Inst(Vec<(TermId, TermId)>),
    InstType(Vec<(TypeId, TypeId)>),
    NotElim,
    NotIntro,
    SelectRule,
    Spec(TermId),
    Subs(Vec<ProofId>),
    Subst(Vec<(TermId, ProofId)>, TermId),
    Sym,
    Undisch,
    Quant(Quant, TermId),
    Comb1,
    Comb2(TermId),
    Bin1(self::Binary),
    Bin2(self::Binary, TermId),
    Not,
  }
  #[derive(Debug)]
  enum ThmList {
    Subs,
    SubsConv,
  }
  #[derive(Debug)]
  enum TermThmList {
    Subst,
    SubstConv,
  }
  #[derive(Debug)]
  enum List {
    Thm(ThmList),
    TermThm(TermThmList),
  }
  #[derive(Debug)]
  enum Stack {
    Paren,
    Unary(Unary),
    ThmList(ThmList, Vec<ProofId>),
    TermThmList(TermThmList, Vec<(TermId, ProofId)>, TermId),
  }
  #[derive(Debug)]
  enum State {
    Start,
    Ret(ProofId),
    ListStart(List),
    ThmListEnd(ThmList, Vec<ProofId>),
    TermThmListEnd(TermThmList, Vec<(TermId, ProofId)>),
  }

  let mut stk = vec![];
  let mut tk = lexer.unpack(*ptk);
  macro_rules! next {() => {tk = lexer.next()}}
  macro_rules! term {() => {{
    parse! { lexer, tk; let tm = TTerm(v) => p.tms.named(v), }
    tm
  }}}
  use Token::{Char, Ident, Type as TType, Term as TTerm};
  let mut state = State::Start;
  loop {
    state = match state {
      State::Start => match tk.unwrap() {
        Token::Fetch(i) => { next!(); State::Ret(de.add(Proof::Fetch(p.fetches[i as usize].0))) }
        Token::Subproof(i) => { next!(); State::Ret(de.reuse(de.named(i))) }
        Char('(') => { next!(); stk.push(Stack::Paren); State::Start }
        Ident("AA") => { next!(); stk.push(Stack::Unary(Unary::AddAsm(term!()))); State::Start }
        Ident("AL") => { next!(); State::Ret(de.add(Proof::Alpha(term!(), term!()))) }
        Ident("ALC") => { next!(); State::Ret(de.add(Proof::AlphaConv(term!(), term!()))) }
        Ident("A") => { next!(); State::Ret(de.add(Proof::Assume(term!()))) }
        Ident("B") => { next!(); State::Ret(de.add(Proof::BetaConv(term!()))) }
        Ident("CC") => { next!(); stk.push(Stack::Unary(Unary::CContr(term!()))); State::Start }
        Ident("CH") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Choose(term!())))); State::Start }
        Ident("CI") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Conj))); State::Start }
        Ident("CE1") => { next!(); stk.push(Stack::Unary(Unary::Conj1)); State::Start }
        Ident("CE2") => { next!(); stk.push(Stack::Unary(Unary::Conj2)); State::Start }
        Ident("C") => { next!(); stk.push(Stack::Unary(Unary::Contr(term!()))); State::Start }
        Ident("DAS") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::DeductAntiSym))); State::Start }
        Ident("D") => { next!(); stk.push(Stack::Unary(Unary::Disch(term!()))); State::Start }
        Ident("DI1") => { next!(); stk.push(Stack::Unary(Unary::Disj1)); State::Start }
        Ident("DI2") => { next!(); stk.push(Stack::Unary(Unary::Disj2(term!()))); State::Start }
        Ident("DE") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::DisjCases))); State::Start }
        Ident("FE") => { next!(); stk.push(Stack::Unary(Unary::EqfElim)); State::Start }
        Ident("FI") => { next!(); stk.push(Stack::Unary(Unary::EqfIntro)); State::Start }
        Ident("EE1") => { next!(); stk.push(Stack::Unary(Unary::EqImp1)); State::Start }
        Ident("EE2") => { next!(); stk.push(Stack::Unary(Unary::EqImp2)); State::Start }
        Ident("E") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::EqMp))); State::Start }
        Ident("TE") => { next!(); stk.push(Stack::Unary(Unary::EqtElim)); State::Start }
        Ident("TI") => { next!(); stk.push(Stack::Unary(Unary::EqtIntro)); State::Start }
        Ident("EC") => { next!(); State::Ret(de.add(Proof::EtaConv(term!()))) }
        Ident("X") => { next!(); stk.push(Stack::Unary(Unary::Exists(term!(), term!()))); State::Start }
        Ident("G") => { next!(); stk.push(Stack::Unary(Unary::Gen(term!()))); State::Start }
        Ident("EI") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::ImpAntiSym))); State::Start }
        Ident("IT") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::ImpTrans))); State::Start }
        Ident("I") => { next!();
          parse! { lexer, tk; Char('['), }
          let mut args = vec![];
          if !matches!(tk, Some(Char(']'))) {
            loop {
              let tm1 = term!(); parse! { lexer, tk; Char(','), }
              let tm2 = term!(); parse! { lexer, tk; let next = Opt(Char(';')), }
              args.push((tm1, tm2));
              if !next { break }
            }
          }
          parse! { lexer, tk; Char(']'), }
          stk.push(Stack::Unary(Unary::Inst(args)));
          State::Start
        }
        Ident("J") => { next!();
          parse! { lexer, tk; Char('['), }
          let mut args = vec![];
          if !matches!(tk, Some(Char(']'))) {
            loop {
              parse! { lexer, tk;
                let ty1 = TType(v) => p.tys.named(v), Char(','),
                let ty2 = TType(v) => p.tys.named(v), let next = Opt(Char(';')),
              }
              args.push((ty1, ty2));
              if !next { break }
            }
          }
          parse! { lexer, tk; Char(']'), }
          stk.push(Stack::Unary(Unary::InstType(args)));
          State::Start
        }
        Ident("M") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Mp))); State::Start }
        Ident("NE") => { next!(); stk.push(Stack::Unary(Unary::NotElim)); State::Start }
        Ident("NI") => { next!(); stk.push(Stack::Unary(Unary::NotIntro)); State::Start }
        Ident("H") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::ProveAsm))); State::Start }
        Ident("R") => { next!(); State::Ret(de.add(Proof::Refl(term!()))) }
        Ident("SR") => { next!(); stk.push(Stack::Unary(Unary::SelectRule)); State::Start }
        Ident("S") => { next!(); stk.push(Stack::Unary(Unary::Spec(term!()))); State::Start }
        Ident("SB") => { next!(); State::ListStart(List::Thm(ThmList::Subs)) }
        Ident("SBC") => { next!(); State::ListStart(List::Thm(ThmList::SubsConv)) }
        Ident("ST") => { next!(); State::ListStart(List::TermThm(TermThmList::Subst)) }
        Ident("STC") => { next!(); State::ListStart(List::TermThm(TermThmList::SubstConv)) }
        Ident("Y") => { next!(); stk.push(Stack::Unary(Unary::Sym)); State::Start }
        Ident("YC") => { next!(); State::Ret(de.add(Proof::SymConv(term!()))) }
        Ident("T") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Trans))); State::Start }
        Ident("U") => { next!(); stk.push(Stack::Unary(Unary::Undisch)); State::Start }
        Ident("ML") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::Lambda, term!()))); State::Start }
        Ident("MA") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Comb))); State::Start }
        Ident("MA1") => { next!(); stk.push(Stack::Unary(Unary::Comb1)); State::Start }
        Ident("MA2") => { next!(); stk.push(Stack::Unary(Unary::Comb2(term!()))); State::Start }
        Ident("MB") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Bin(self::Binary::Bin(term!()))))); State::Start }
        Ident("MB1") => { next!(); stk.push(Stack::Unary(Unary::Bin1(self::Binary::Bin(term!())))); State::Start }
        Ident("MB2") => { next!(); stk.push(Stack::Unary(Unary::Bin2(self::Binary::Bin(term!()), term!()))); State::Start }
        Ident("MC") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Bin(self::Binary::Conj)))); State::Start }
        Ident("MC1") => { next!(); stk.push(Stack::Unary(Unary::Bin1(self::Binary::Conj))); State::Start }
        Ident("MC2") => { next!(); stk.push(Stack::Unary(Unary::Bin2(self::Binary::Conj, term!()))); State::Start }
        Ident("MD") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Bin(self::Binary::Disj)))); State::Start }
        Ident("MD1") => { next!(); stk.push(Stack::Unary(Unary::Bin1(self::Binary::Disj))); State::Start }
        Ident("MD2") => { next!(); stk.push(Stack::Unary(Unary::Bin2(self::Binary::Disj, term!()))); State::Start }
        Ident("ME") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Bin(self::Binary::Eq)))); State::Start }
        Ident("ME1") => { next!(); stk.push(Stack::Unary(Unary::Bin1(self::Binary::Eq))); State::Start }
        Ident("ME2") => { next!(); stk.push(Stack::Unary(Unary::Bin2(self::Binary::Eq, term!()))); State::Start }
        Ident("MP") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Bin(self::Binary::Pair)))); State::Start }
        Ident("MP1") => { next!(); stk.push(Stack::Unary(Unary::Bin1(self::Binary::Pair))); State::Start }
        Ident("MP2") => { next!(); stk.push(Stack::Unary(Unary::Bin2(self::Binary::Pair, term!()))); State::Start }
        Ident("MX") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::Exists, term!()))); State::Start }
        Ident("MUX") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::UExists, term!()))); State::Start }
        Ident("MU") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::Forall, term!()))); State::Start }
        Ident("MI") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Bin(self::Binary::Imp)))); State::Start }
        Ident("MI1") => { next!(); stk.push(Stack::Unary(Unary::Bin1(self::Binary::Imp))); State::Start }
        Ident("MI2") => { next!(); stk.push(Stack::Unary(Unary::Bin2(self::Binary::Imp, term!()))); State::Start }
        Ident("MN") => { next!(); stk.push(Stack::Unary(Unary::Not)); State::Start }
        Ident("MS") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::Select, term!()))); State::Start }
        Ident("NCSC") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Suc, term!()))) }
        Ident("NCPR") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Pre, term!()))) }
        Ident("NCA") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Add, term!()))) }
        Ident("NCS") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Sub, term!()))) }
        Ident("NCM") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Mult, term!()))) }
        Ident("NCE") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Exp, term!()))) }
        Ident("NCEV") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Even, term!()))) }
        Ident("NCOD") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Odd, term!()))) }
        Ident("NCEQ") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Eq, term!()))) }
        Ident("NCLT") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Lt, term!()))) }
        Ident("NCLE") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Le, term!()))) }
        Ident("NCGT") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Gt, term!()))) }
        Ident("NCGE") => { next!(); State::Ret(de.add(Proof::NumConv(NumOp::Ge, term!()))) }
        _ => panic!("parse_proof parse error")
      }
      State::ListStart(l) => {
        parse! { lexer, tk; Char('['), }
        if let Some(Char(']')) = tk {
          match l {
            List::Thm(l) => State::ThmListEnd(l, vec![]),
            List::TermThm(l) => State::TermThmListEnd(l, vec![]),
          }
        } else {
          match l {
            List::Thm(l) => stk.push(Stack::ThmList(l, vec![])),
            List::TermThm(l) => {
              stk.push(Stack::TermThmList(l, vec![], term!()));
              parse! { lexer, tk; Char(','), }
            }
          }
          State::Start
        }
      }
      State::ThmListEnd(l, args) => {
        parse! { lexer, tk; Char(']'), }
        match l {
          ThmList::Subs => { stk.push(Stack::Unary(Unary::Subs(args))); State::Start }
          ThmList::SubsConv => State::Ret(de.add(Proof::SubsConv(args, term!())))
        }
      }
      State::TermThmListEnd(l, args) => {
        parse! { lexer, tk; Char(']'), }
        match l {
          TermThmList::Subst => { stk.push(Stack::Unary(Unary::Subst(args, term!()))); State::Start }
          TermThmList::SubstConv => State::Ret(de.add(Proof::SubstConv(args, term!(), term!()))),
        }
      }
      State::Ret(pr) => match stk.pop() {
        Some(Stack::Paren) => {
          parse! { lexer, tk; Char(')'), }
          State::Ret(pr)
        }
        Some(Stack::ThmList(l, mut args)) => {
          args.push(pr);
          parse! { lexer, tk; let next = Opt(Char(';')), }
          if next { stk.push(Stack::ThmList(l, args)); State::Start }
          else { State::ThmListEnd(l, args) }
        }
        Some(Stack::TermThmList(l, mut args, tm)) => {
          args.push((tm, pr));
          parse! { lexer, tk; let next = Opt(Char(';')), }
          if next {
            stk.push(Stack::TermThmList(l, args, term!()));
            parse! { lexer, tk; Char(','), }
            State::Start
          } else {
            State::TermThmListEnd(l, args)
          }
        }
        Some(Stack::Unary(u)) => match u {
          Unary::AddAsm(tm) => State::Ret(de.add(Proof::AddAsm(tm, pr))),
          Unary::Binary(b) => { stk.push(Stack::Unary(Unary::Binary1(b, pr))); State::Start }
          Unary::CContr(tm) => State::Ret(de.add(Proof::CContr(tm, pr))),
          Unary::Conj1 => State::Ret(de.add(Proof::Conj1(pr))),
          Unary::Conj2 => State::Ret(de.add(Proof::Conj2(pr))),
          Unary::Contr(tm) => State::Ret(de.add(Proof::Contr(tm, pr))),
          Unary::Disch(tm) => State::Ret(de.add(Proof::Disch(tm, pr))),
          Unary::Disj1 => State::Ret(de.add(Proof::Disj1(pr, term!()))),
          Unary::Disj2(tm) => State::Ret(de.add(Proof::Disj2(tm, pr))),
          Unary::EqfElim => State::Ret(de.add(Proof::EqfElim(pr))),
          Unary::EqfIntro => State::Ret(de.add(Proof::EqfIntro(pr))),
          Unary::EqImp1 => State::Ret(de.add(Proof::EqImp1(pr))),
          Unary::EqImp2 => State::Ret(de.add(Proof::EqImp2(pr))),
          Unary::EqtElim => State::Ret(de.add(Proof::EqtElim(pr))),
          Unary::EqtIntro => State::Ret(de.add(Proof::EqtIntro(pr))),
          Unary::Exists(tm1, tm2) => State::Ret(de.add(Proof::Exists(tm1, tm2, pr))),
          Unary::Gen(tm) => State::Ret(de.add(Proof::Gen(tm, pr))),
          Unary::Inst(inst) => State::Ret(de.add(Proof::Inst(inst, pr))),
          Unary::InstType(inst) => State::Ret(de.add(Proof::InstType(inst, pr))),
          Unary::NotElim => State::Ret(de.add(Proof::NotElim(pr))),
          Unary::NotIntro => State::Ret(de.add(Proof::NotIntro(pr))),
          Unary::SelectRule => State::Ret(de.add(Proof::SelectRule(pr))),
          Unary::Spec(tm) => State::Ret(de.add(Proof::Spec(tm, pr))),
          Unary::Subs(sub) => State::Ret(de.add(Proof::Subs(sub, pr))),
          Unary::Subst(sub, tm) => State::Ret(de.add(Proof::Subst(sub, tm, pr))),
          Unary::Sym => State::Ret(de.add(Proof::Sym(pr))),
          Unary::Undisch => State::Ret(de.add(Proof::Undisch(pr))),
          Unary::Quant(q, tm) => State::Ret(de.add(Proof::Quant(q, tm, pr))),
          Unary::Comb1 => State::Ret(de.add(Proof::Comb1(pr, term!()))),
          Unary::Comb2(tm) => State::Ret(de.add(Proof::Comb2(tm, pr))),
          Unary::Bin1(f) => State::Ret(de.add(Proof::Bin1(f, pr, term!()))),
          Unary::Bin2(f, tm) => State::Ret(de.add(Proof::Bin2(f, tm, pr))),
          Unary::Not => State::Ret(de.add(Proof::Not(pr))),
          Unary::Binary1(b, pr1) => match b {
            Binary::Choose(tm) => State::Ret(de.add(Proof::Choose(tm, pr1, pr))),
            Binary::Conj => State::Ret(de.add(Proof::Conj(pr1, pr))),
            Binary::DeductAntiSym => State::Ret(de.add(Proof::DeductAntiSym(pr1, pr))),
            Binary::DisjCases => {
              stk.push(Stack::Unary(Unary::Binary1(Binary::DisjCases1(pr1), pr)));
              State::Start
            }
            Binary::DisjCases1(pr0) => State::Ret(de.add(Proof::DisjCases(pr0, pr1, pr))),
            Binary::EqMp => State::Ret(de.add(Proof::EqMp(pr1, pr))),
            Binary::ImpAntiSym => State::Ret(de.add(Proof::ImpAntiSym(pr1, pr))),
            Binary::ImpTrans => State::Ret(de.add(Proof::ImpTrans(pr1, pr))),
            Binary::Mp => State::Ret(de.add(Proof::Mp(pr1, pr))),
            Binary::ProveAsm => State::Ret(de.add(Proof::ProveAsm(pr1, pr))),
            Binary::Trans => State::Ret(de.add(Proof::Trans(pr1, pr))),
            Binary::Comb => State::Ret(de.add(Proof::Comb(pr1, pr))),
            Binary::Bin(f) => State::Ret(de.add(Proof::Bin(f, pr1, pr))),
          }
        }
        None => {
          parse! { lexer, tk; Eols, }
          *ptk = tk.map(Token::pack);
          return pr
        }
      }
    }
  }
}

pub fn parse_type_str(de: &mut Dedup<Type>, x: &str) -> TypeId {
  let mut lexer = Lexer::from(x.bytes());
  parse_type(&mut lexer.next().map(Token::pack), &mut lexer, de)
}

fn parse_type_str_preamble(tys: &[&str]) -> Dedup<Type> {
  let mut de = Dedup::new();
  for &ty in tys {
    let n = parse_type_str(&mut de, ty);
    de.named.push(Idx::into_u32(n));
  }
  de
}

pub fn parse_term_str(tys: &Dedup<Type>, de: &mut Dedup<Term>, tm: &str) -> TermId {
  let mut lexer = Lexer::from(tm.bytes());
  parse_term(&mut lexer.next().map(Token::pack), &mut lexer, tys, de)
}

fn parse_term_str_preamble(tys: &Dedup<Type>, tms: &[&str]) -> Dedup<Term> {
  let mut de = Dedup::new();
  for &tm in tms {
    let n = parse_term_str(tys, &mut de, tm);
    de.named.push(Idx::into_u32(n));
  }
  de
}

fn parse_term_preamble<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tys: &Dedup<Type>,
) -> Dedup<Term> {
  let mut de = Dedup::new();
  if matches!(lexer.unpack(*ptk), Some(Token::Heading("Terms"))) {
    let mut tk = lexer.next();
    parse! { lexer, tk; Eols, }
    while let Some(Token::Int(v)) = tk {
      assert_eq!(v.parse::<usize>().unwrap(), de.named.len());
      *ptk = lexer.next().map(Token::pack);
      let n = parse_term(ptk, lexer, tys, &mut de);
      de.named.push(Idx::into_u32(n));
      tk = lexer.unpack(*ptk);
      parse! { lexer, tk; Eols, }
    }
  }
  de
}

fn parse_int_section<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>,
) -> u32 {
  let mut tk = lexer.unpack(*ptk);
  parse! { lexer, tk;
    Token::Heading("Num"), Eols,
    let n = Token::Int(v) => v.parse().unwrap(), Eols,
  }
  *ptk = tk.map(Token::pack);
  n
}

fn parse_type_section<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tys: &Dedup<Type>
) -> TypeId {
  let mut tk = lexer.unpack(*ptk);
  parse! { lexer, tk;
    Token::Heading("Type"), Eols,
    let ty = Token::Type(v) => tys.named(v), Eols,
  }
  *ptk = tk.map(Token::pack);
  ty
}

fn parse_term_section<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tms: &Dedup<Term>
) -> TermId {
  let mut tk = lexer.unpack(*ptk);
  parse! { lexer, tk;
    Token::Heading("Term"), Eols,
    let tm = Token::Term(v) => tms.named(v), Eols,
  }
  *ptk = tk.map(Token::pack);
  tm
}

fn parse_subproofs_section<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, p: &Preambles
) -> Dedup<Proof> {
  let mut de = Dedup::new();
  if matches!(lexer.unpack(*ptk), Some(Token::Heading("Subproofs"))) {
    let mut tk = lexer.next();
    parse! { lexer, tk; Eols, }
    while let Some(Token::Int(v)) = tk {
      assert_eq!(v.parse::<usize>().unwrap(), de.named.len());
      *ptk = lexer.next().map(Token::pack);
      let n = parse_proof(ptk, lexer, p, &mut de);
      de.named.push(Idx::into_u32(n));
      tk = lexer.unpack(*ptk);
      parse! { lexer, tk; Eols, }
    }
  }
  de
}

fn parse_proof_section<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>,
  p: &Preambles, de: &mut Dedup<Proof>
) -> ProofId {
  let mut tk = lexer.unpack(*ptk);
  parse! { lexer, tk; Token::Heading("Proof"), Eols, }
  *ptk = tk.map(Token::pack);
  parse_proof(ptk, lexer, p, de)
}

fn parse_alphalink_section<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tms: &Dedup<Term>
) -> TermId {
  let mut tk = lexer.unpack(*ptk);
  parse! { lexer, tk;
    Token::Heading("Target"), Eols,
    let tm = Token::Term(v) => tms.named(v), Eols,
  }
  *ptk = tk.map(Token::pack);
  tm
}

impl Environment {
  fn parse_fetch_preamble<I: Iterator<Item=u8>>(&self,
    ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tys: &Dedup<Type>,
  ) -> Vec<(ThmId, Vec<TypeId>)> {
    let mut named = vec![];
    if matches!(lexer.unpack(*ptk), Some(Token::Heading("Fetches"))) {
      let mut tk = lexer.next();
      named.push((Idx::from(u32::MAX), vec![]));
      parse! { lexer, tk; Eols, }
      while let Some(Token::Int(v)) = tk {
        assert_eq!(v.parse::<usize>().unwrap(), named.len());
        tk = lexer.next();
        parse! { lexer, tk; Eols,
          let k = Token::Ident(v) => FetchKind::try_from(v).unwrap(),
          let thm = Token::Str(v) => *self.trans.fetches[k].get(v)
            .unwrap_or_else(|| panic!("can't find {:?} {:?}", k, v)),
        }
        let mut args = vec![];
        while let Some(Token::Type(i)) = tk {
          tk = lexer.next();
          args.push(tys.named(i))
        }
        parse! { lexer, tk; Eols, }
        named.push((thm, args));
      }
    }
    named
  }

  fn parse_preambles<I: Iterator<Item=u8>>(&self,
    tk: &mut Option<PackedToken>, lexer: &mut Lexer<I>,
  ) -> Preambles {
    let tys = parse_type_preamble(tk, lexer);
    let tms = parse_term_preamble(tk, lexer, &tys);
    let fetches = self.parse_fetch_preamble(tk, lexer, &tys);
    Preambles { tys, tms, fetches }
  }

  pub fn parse_basic_def<'a>(&mut self, x: &str, tys: &[&str], tms: &[&str], tm: &str) {
    let tys = parse_type_str_preamble(tys);
    let mut tms = parse_term_str_preamble(&tys, tms);
    let tm = parse_term_str(&tys, &mut tms, tm);
    self.add_basic_def(x, tys, tms, tm);
  }
}

impl Importer {
  pub fn import_target_object(&mut self, kind: ObjectSpec, data: ObjectData, defer: bool) -> bool {
    println!("{:?}", kind);
    let file = self.mpath.join(&data.file);
    let mut lexer = Lexer::from(File::open(file).unwrap().bytes().map(Result::unwrap));
    let mut tk = lexer.next();
    use Token::{Heading, Ident, Char, Str};
    parse! { lexer, tk; let kind_ = Heading(v) => ObjectSpec::try_from(v).unwrap(), Eols, }
    let mut kind_ = kind_;
    let mut args = vec![];
    while let Some(Str(v)) = tk {
      args.push(v.to_owned());
      tk = lexer.next();
    }
    kind_.set_args(args);
    assert_eq!(kind, kind_);
    let _fl2 = matches!(tk, Some(Char('*'))) && { tk = lexer.next(); true };
    parse! { lexer, tk; Eols, }
    let mut inherits = vec![];
    if let Some(Heading("Inherit")) = tk {
      tk = lexer.next(); parse! { lexer, tk; Eols, }
      while let Some(Ident(v)) = tk {
        let mut kind = ObjectSpec::try_from(Abbrev(v)).unwrap();
        tk = lexer.next();
        let mut args = vec![];
        while let Some(Str(v)) = tk {
          args.push(v.to_owned());
          tk = lexer.next();
        }
        kind.set_args(args);
        inherits.push(kind);
        parse! { lexer, tk; Eols, }
      }
    }
    for k in inherits {
      if !self.env.trans.contains(&k) {
        if defer {
          self.deferred.push_back((kind, data));
          return false
        }
        panic!("missing inherited object: {:?}", k);
      }
    }
    if !matches!(kind, ObjectSpec::TypeBij(_)) {
      parse! { lexer, tk; Heading(""), Eols, }
    }
    let mut tk = tk.map(Token::pack);
    let obj = match kind {
      ObjectSpec::TypeDecl(x) => {
        Object::TypeDecl(x, parse_int_section(&mut tk, &mut lexer))
      }
      ObjectSpec::ConstDecl(x) => {
        let tys = parse_type_preamble(&mut tk, &mut lexer);
        let ty = parse_type_section(&mut tk, &mut lexer, &tys);
        Object::ConstDecl(x, tys, ty)
      }
      ObjectSpec::Axiom(x) => {
        let tys = parse_type_preamble(&mut tk, &mut lexer);
        let tms = parse_term_preamble(&mut tk, &mut lexer, &tys);
        let tm = parse_term_section(&mut tk, &mut lexer, &tms);
        Object::Axiom(x, tys, tms, tm)
      }
      ObjectSpec::BasicDef(x) => {
        let tys = parse_type_preamble(&mut tk, &mut lexer);
        let tms = parse_term_preamble(&mut tk, &mut lexer, &tys);
        let tm = parse_term_section(&mut tk, &mut lexer, &tms);
        Object::BasicDef(x, tys, tms, tm)
      }
      ObjectSpec::Def(x) => {
        let tys = parse_type_preamble(&mut tk, &mut lexer);
        let tms = parse_term_preamble(&mut tk, &mut lexer, &tys);
        let tm = parse_term_section(&mut tk, &mut lexer, &tms);
        Object::Def(x, tys, tms, tm)
      }
      ObjectSpec::Spec(xs) => {
        let p = self.env.parse_preambles(&mut tk, &mut lexer);
        let mut subproofs = parse_subproofs_section(&mut tk, &mut lexer, &p);
        let pr = parse_proof_section(&mut tk, &mut lexer, &p, &mut subproofs);
        Object::Spec(xs, p, subproofs, pr)
      }
      ObjectSpec::BasicTypedef(x) => {
        let p = self.env.parse_preambles(&mut tk, &mut lexer);
        let mut subproofs = parse_subproofs_section(&mut tk, &mut lexer, &p);
        let pr = parse_proof_section(&mut tk, &mut lexer, &p, &mut subproofs);
        Object::BasicTypedef(x, p, subproofs, pr)
      }
      ObjectSpec::Typedef(_) => unimplemented!(),
      ObjectSpec::TypeBij(xs) => Object::TypeBij(*xs),
      ObjectSpec::Thm(x) => {
        let p = self.env.parse_preambles(&mut tk, &mut lexer);
        let mut subproofs = parse_subproofs_section(&mut tk, &mut lexer, &p);
        let pr = parse_proof_section(&mut tk, &mut lexer, &p, &mut subproofs);
        let link = parse_alphalink_section(&mut tk, &mut lexer, &p.tms);
        Object::Thm(x, p, subproofs, pr, link)
      }
      ObjectSpec::OpenThm(x) => {
        let p = self.env.parse_preambles(&mut tk, &mut lexer);
        let mut subproofs = parse_subproofs_section(&mut tk, &mut lexer, &p);
        let pr = parse_proof_section(&mut tk, &mut lexer, &p, &mut subproofs);
        Object::OpenThm(x, p, subproofs, pr)
      }
      ObjectSpec::NumThm(x) => {
        let p = self.env.parse_preambles(&mut tk, &mut lexer);
        let mut subproofs = parse_subproofs_section(&mut tk, &mut lexer, &p);
        let pr = parse_proof_section(&mut tk, &mut lexer, &p, &mut subproofs);
        Object::NumThm(x, p, subproofs, pr)
      }
    };
    assert!(matches!(tk, None));
    // println!("{:?}", obj);
    self.env.add(obj);
    true
  }
}
