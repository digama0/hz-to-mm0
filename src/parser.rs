#![allow(clippy::eval_order_dependence)]

use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fs::File;
use std::io::Read;

use crate::Importer;
use crate::lexer::{Token, PackedToken, Lexer};
use crate::kernel::{Environment, OwnedTerm, OwnedType,
  ProofArena, TermArena, TypeArena, TypedefInfo, HasTypeStore, HasTermStore};
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
      // "SI"   => Ok(Self::SpecInput),
      // "BZD"  => Ok(Self::BasicTypedef),
      // "BZDI" => Ok(Self::BasicTypedefInput),
      "ZD"   => Ok(Self::Typedef),
      // "ZDI"  => Ok(Self::TypedefInput),
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

impl<'a> TypeArena<'a> {
  fn parse_type<I: Iterator<Item=u8>>(&mut self,
    ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tys: &[TypeId],
  ) -> TypeId {
    #[derive(Debug)]
    enum Stack {
      Paren,
      Fun,
      Fun1(TypeId),
      Const(TyopId, Vec<TypeId>),
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
          Some(TType(i)) => { tk = lexer.next(); State::Ret(tys[i as usize]) }
          Some(Char('(')) => { tk = lexer.next(); stk.push(Stack::Paren); State::Start }
          Some(Ident("V")) => { tk = lexer.next();
            parse! { lexer, tk; let x = Str(v) => self.mk_var_name(v.to_owned()), }
            State::Ret(self.mk_var(x))
          }
          Some(Ident("K")) => { tk = lexer.next();
            parse! { lexer, tk; let x = Str(v) => self.env.trans.tyops[v], }
            stk.push(Stack::Const(x, vec![]));
            State::Start
          }
          Some(Ident("F")) => { tk = lexer.next();
            stk.push(Stack::Fun);
            State::Start
          }
          ref tk => match stk.pop() {
            Some(Stack::Const(x, args)) => State::Ret(self.mk_const(x, args)),
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
            State::Ret(self.mk_fun(ty1, ty))
          }
          Some(Stack::Const(x, mut args)) => {
            args.push(ty);
            stk.push(Stack::Const(x, args));
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

  fn parse_type_preamble<I: Iterator<Item=u8>>(&mut self,
    ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>
  ) -> Vec<TypeId> {
    let mut tys = vec![TypeId(u32::MAX)];
    if matches!(lexer.unpack(*ptk), Some(Token::Heading("Types"))) {
      let mut tk = lexer.next();
      parse! { lexer, tk; Eols, }
      while let Some(Token::Int(v)) = tk {
        assert_eq!(v.parse::<usize>().unwrap(), tys.len());
        *ptk = lexer.next().map(Token::pack);
        let n = self.parse_type(ptk, lexer, &tys);
        tys.push(n);
        tk = lexer.unpack(*ptk);
        parse! { lexer, tk; Eols, }
      }
    }
    tys
  }

  pub fn parse_type_str(&mut self, tys: &[TypeId], x: &str) -> TypeId {
    let mut lexer = Lexer::from(x.bytes());
    self.parse_type(&mut lexer.next().map(Token::pack), &mut lexer, tys)
  }

  fn parse_type_str_preamble(&mut self, tys: &[&str]) -> Vec<TypeId> {
    let mut named = vec![TypeId(u32::MAX)];
    for &ty in tys {
      let n = self.parse_type_str(&named, ty);
      named.push(n);
    }
    named
  }
}

impl<'a> TermArena<'a> {
  fn parse_term<I: Iterator<Item=u8>>(&mut self,
    ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>,
    tys: &[TypeId], tms: &[TermId],
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
      App,
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
    macro_rules! next {() => {tk = lexer.next()}}
    let mut state = State::Start;
    loop {
      // println!("{:?}: state = {:?}, stack = {:?}", tk, state, stk);
      state = match state {
        State::Start => match tk.unwrap() {
          TTerm(i) => { next!(); State::Ret(tms[i as usize]) }
          Char('(') => { next!(); stk.push(Stack::Paren); State::Start }
          Ident("V") => { next!();
            parse! { lexer, tk; let x = Str(v) => v.to_owned(), let n = TType(v) => tys[v as usize], }
            State::Ret(self.mk_var_term(x, n).1)
          }
          Ident("K") => { next!();
            parse! { lexer, tk; let x = Str(v) => self.env.trans.consts[v], }
            let mut args = vec![];
            while let Some(TType(i)) = tk {
              next!();
              args.push(tys[i as usize])
            }
            State::Ret(self.mk_const(x, args))
          }
          Ident("M") => { next!();
            parse! { lexer, tk; let n = Int(v) => v.parse().unwrap(), }
            State::Ret(self.mk_int(n))
          }
          Ident("A") => { next!(); stk.push(Stack::Binop(Binop::App)); State::Start }
          Ident("L") => { next!(); stk.push(Stack::Binop(Binop::Quant(Quant::Lambda))); State::Start }
          Ident("B") => { next!(); stk.push(Stack::Bin0); State::Start }
          Ident("E") => { next!(); stk.push(Stack::Binop(Binop::Bin(Binary::Eq))); State::Start }
          Ident("N") => { next!(); stk.push(Stack::Not); State::Start }
          Ident("C") => { next!(); stk.push(Stack::Binop(Binop::Bin(Binary::Conj))); State::Start }
          Ident("D") => { next!(); stk.push(Stack::Binop(Binop::Bin(Binary::Disj))); State::Start }
          Ident("I") => { next!(); stk.push(Stack::Binop(Binop::Bin(Binary::Imp))); State::Start }
          Ident("P") => { next!(); stk.push(Stack::Binop(Binop::Bin(Binary::Pair))); State::Start }
          Ident("X") => { next!(); stk.push(Stack::Binop(Binop::Quant(Quant::Exists))); State::Start }
          Ident("UX") => { next!(); stk.push(Stack::Binop(Binop::Quant(Quant::UExists))); State::Start }
          Ident("U") => { next!(); stk.push(Stack::Binop(Binop::Quant(Quant::Forall))); State::Start }
          Ident("S") => { next!(); stk.push(Stack::Binop(Binop::Quant(Quant::Select))); State::Start }
          ref tk => panic!("parse_term parse error: {:?}", tk)
        }
        State::Ret(tm) => match stk.pop() {
          Some(Stack::Paren) => {
            parse! { lexer, tk; Char(')'), }
            State::Ret(tm)
          }
          Some(Stack::Not) => State::Ret(self.mk_not(tm)),
          Some(Stack::Bin0) => {
            stk.push(Stack::Binop(Binop::Bin(Binary::Bin(tm))));
            State::Start
          }
          Some(Stack::Binop(o)) => { stk.push(Stack::Binop1(o, tm)); State::Start }
          Some(Stack::Binop1(o, tm1)) => State::Ret(match o {
            Binop::App => self.mk_app(tm1, tm),
            Binop::Quant(q) => self.mk_quant(q, self.dest_var(tm1), tm),
            Binop::Bin(b) => self.mk_binary(b, tm1, tm),
          }),
          None => {
            parse! { lexer, tk; Eols, }
            *ptk = tk.map(Token::pack);
            return tm
          }
        }
      }
    }
  }

  pub fn parse_term_str(&mut self, tys: &[TypeId], tms: &[TermId], tm: &str) -> TermId {
    let mut lexer = Lexer::from(tm.bytes());
    self.parse_term(&mut lexer.next().map(Token::pack), &mut lexer, tys, tms)
  }

  fn parse_term_str_preamble(&mut self, tys: &[TypeId], tms: &[&str]
  ) -> Vec<TermId> {
    let mut named = vec![TermId(u32::MAX)];
    for &tm in tms {
      let n = self.parse_term_str(tys, &named, tm);
      named.push(n);
    }
    named
  }

  fn parse_term_preamble<I: Iterator<Item=u8>>(&mut self,
    ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tys: &[TypeId],
  ) -> Vec<TermId> {
    let mut named = vec![TermId(u32::MAX)];
    if matches!(lexer.unpack(*ptk), Some(Token::Heading("Terms"))) {
      let mut tk = lexer.next();
      parse! { lexer, tk; Eols, }
      while let Some(Token::Int(v)) = tk {
        assert_eq!(v.parse::<usize>().unwrap(), named.len());
        *ptk = lexer.next().map(Token::pack);
        let n = self.parse_term(ptk, lexer, tys, &named);
        named.push(n);
        tk = lexer.unpack(*ptk);
        parse! { lexer, tk; Eols, }
      }
    }
    named
  }
}

type Preambles = (Vec<TypeId>, Vec<TermId>, Vec<ProofId>);

impl<'a> ProofArena<'a> {
  fn parse<I: Iterator<Item=u8>>(&mut self,
    ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>,
    (tys, tms, fetches): &Preambles, pfs: &[ProofId],
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
      App,
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
      Gen(VarId),
      Inst(Vec<(VarId, TermId)>),
      InstType(Vec<(TyVarId, TypeId)>),
      NotElim,
      NotIntro,
      SelectRule,
      Spec(TermId),
      Subs(Vec<ProofId>),
      Subst(HashMap<VarId, ProofId>, TermId),
      Sym,
      Undisch,
      Quant(Quant, VarId),
      App1,
      App2(TermId),
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
    enum VarThmList {
      Subst,
      SubstConv,
    }
    #[derive(Debug)]
    enum List {
      Thm(ThmList),
      VarThm(VarThmList),
    }
    #[derive(Debug)]
    enum Stack {
      Paren,
      Unary(Unary),
      ThmList(ThmList, Vec<ProofId>),
      VarThmList(VarThmList, HashMap<VarId, ProofId>, VarId),
    }
    #[derive(Debug)]
    enum State {
      Start,
      Ret(ProofId),
      ListStart(List),
      ThmListEnd(ThmList, Vec<ProofId>),
      VarThmListEnd(VarThmList, HashMap<VarId, ProofId>),
    }

    let mut stk = vec![];
    let mut tk = lexer.unpack(*ptk);
    macro_rules! next {() => {tk = lexer.next()}}
    macro_rules! term {() => {{ parse! { lexer, tk; let tm = TTerm(v) => tms[v as usize], } tm }}}
    macro_rules! var {() => { self.dest_var(term!()) }}
    macro_rules! ty {() => {{ parse! { lexer, tk; let ty = TType(v) => tys[v as usize], } ty }}}
    macro_rules! tyvar {() => { self.dest_tyvar(ty!()) }}
    macro_rules! list {($m:ident!, $n:ident!) => {{
      parse! { lexer, tk; Char('['), }
      let mut args = vec![];
      if !matches!(tk, Some(Char(']'))) {
        loop {
          let a = $m!(); parse! { lexer, tk; Char(','), }
          let b = $n!(); parse! { lexer, tk; let next = Opt(Char(';')), }
          args.push((a, b));
          if !next { break }
        }
      }
      parse! { lexer, tk; Char(']'), }
      args
    }}}
    use Token::{Char, Ident, Type as TType, Term as TTerm};
    let mut state = State::Start;
    loop {
      state = match state {
        State::Start => match tk.unwrap() {
          Token::Fetch(i) => { next!(); State::Ret(fetches[i as usize]) }
          Token::Subproof(i) => { next!(); State::Ret(pfs[i as usize]) }
          Char('(') => { next!(); stk.push(Stack::Paren); State::Start }
          Ident("AA") => { next!(); stk.push(Stack::Unary(Unary::AddAsm(term!()))); State::Start }
          Ident("AL") => { next!(); State::Ret(self.alpha(term!(), term!())) }
          Ident("ALC") => { next!(); State::Ret(self.alpha_conv(term!(), term!())) }
          Ident("A") => { next!(); State::Ret(self.assume(term!())) }
          Ident("B") => { next!(); State::Ret(self.beta(term!())) }
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
          Ident("EC") => { next!(); State::Ret(self.eta(term!())) }
          Ident("X") => { next!(); stk.push(Stack::Unary(Unary::Exists(term!(), term!()))); State::Start }
          Ident("G") => { next!(); stk.push(Stack::Unary(Unary::Gen(var!()))); State::Start }
          Ident("EI") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::ImpAntiSym))); State::Start }
          Ident("IT") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::ImpTrans))); State::Start }
          Ident("I") => { next!(); stk.push(Stack::Unary(Unary::Inst(list!(var!, term!)))); State::Start }
          Ident("J") => { next!(); stk.push(Stack::Unary(Unary::InstType(list!(tyvar!, ty!)))); State::Start }
          Ident("M") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Mp))); State::Start }
          Ident("NE") => { next!(); stk.push(Stack::Unary(Unary::NotElim)); State::Start }
          Ident("NI") => { next!(); stk.push(Stack::Unary(Unary::NotIntro)); State::Start }
          Ident("H") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::ProveAsm))); State::Start }
          Ident("R") => { next!(); State::Ret(self.refl(term!())) }
          Ident("SR") => { next!(); stk.push(Stack::Unary(Unary::SelectRule)); State::Start }
          Ident("S") => { next!(); stk.push(Stack::Unary(Unary::Spec(term!()))); State::Start }
          Ident("SB") => { next!(); State::ListStart(List::Thm(ThmList::Subs)) }
          Ident("SBC") => { next!(); State::ListStart(List::Thm(ThmList::SubsConv)) }
          Ident("ST") => { next!(); State::ListStart(List::VarThm(VarThmList::Subst)) }
          Ident("STC") => { next!(); State::ListStart(List::VarThm(VarThmList::SubstConv)) }
          Ident("Y") => { next!(); stk.push(Stack::Unary(Unary::Sym)); State::Start }
          Ident("YC") => { next!(); State::Ret(self.sym_conv(term!())) }
          Ident("T") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Trans))); State::Start }
          Ident("U") => { next!(); stk.push(Stack::Unary(Unary::Undisch)); State::Start }
          Ident("ML") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::Lambda, var!()))); State::Start }
          Ident("MA") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::App))); State::Start }
          Ident("MA1") => { next!(); stk.push(Stack::Unary(Unary::App1)); State::Start }
          Ident("MA2") => { next!(); stk.push(Stack::Unary(Unary::App2(term!()))); State::Start }
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
          Ident("MX") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::Exists, var!()))); State::Start }
          Ident("MUX") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::UExists, var!()))); State::Start }
          Ident("MU") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::Forall, var!()))); State::Start }
          Ident("MI") => { next!(); stk.push(Stack::Unary(Unary::Binary(Binary::Bin(self::Binary::Imp)))); State::Start }
          Ident("MI1") => { next!(); stk.push(Stack::Unary(Unary::Bin1(self::Binary::Imp))); State::Start }
          Ident("MI2") => { next!(); stk.push(Stack::Unary(Unary::Bin2(self::Binary::Imp, term!()))); State::Start }
          Ident("MN") => { next!(); stk.push(Stack::Unary(Unary::Not)); State::Start }
          Ident("MS") => { next!(); stk.push(Stack::Unary(Unary::Quant(Quant::Select, var!()))); State::Start }
          Ident("NCSC") => { next!(); State::Ret(self.mk_num_conv(NumOp::Suc, term!())) }
          Ident("NCPR") => { next!(); State::Ret(self.mk_num_conv(NumOp::Pre, term!())) }
          Ident("NCA") => { next!(); State::Ret(self.mk_num_conv(NumOp::Add, term!())) }
          Ident("NCS") => { next!(); State::Ret(self.mk_num_conv(NumOp::Sub, term!())) }
          Ident("NCM") => { next!(); State::Ret(self.mk_num_conv(NumOp::Mult, term!())) }
          Ident("NCE") => { next!(); State::Ret(self.mk_num_conv(NumOp::Exp, term!())) }
          Ident("NCEV") => { next!(); State::Ret(self.mk_num_conv(NumOp::Even, term!())) }
          Ident("NCOD") => { next!(); State::Ret(self.mk_num_conv(NumOp::Odd, term!())) }
          Ident("NCEQ") => { next!(); State::Ret(self.mk_num_conv(NumOp::Eq, term!())) }
          Ident("NCLT") => { next!(); State::Ret(self.mk_num_conv(NumOp::Lt, term!())) }
          Ident("NCLE") => { next!(); State::Ret(self.mk_num_conv(NumOp::Le, term!())) }
          Ident("NCGT") => { next!(); State::Ret(self.mk_num_conv(NumOp::Gt, term!())) }
          Ident("NCGE") => { next!(); State::Ret(self.mk_num_conv(NumOp::Ge, term!())) }
          _ => panic!("parse_proof parse error")
        }
        State::ListStart(l) => {
          parse! { lexer, tk; Char('['), }
          if let Some(Char(']')) = tk {
            match l {
              List::Thm(l) => State::ThmListEnd(l, vec![]),
              List::VarThm(l) => State::VarThmListEnd(l, HashMap::new()),
            }
          } else {
            match l {
              List::Thm(l) => stk.push(Stack::ThmList(l, vec![])),
              List::VarThm(l) => {
                stk.push(Stack::VarThmList(l, HashMap::new(), var!()));
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
            ThmList::SubsConv => State::Ret(self.subs_conv(&args, term!()))
          }
        }
        State::VarThmListEnd(l, args) => {
          parse! { lexer, tk; Char(']'), }
          match l {
            VarThmList::Subst => { stk.push(Stack::Unary(Unary::Subst(args, term!()))); State::Start }
            VarThmList::SubstConv => State::Ret(self.subst_conv(&args, term!(), term!())),
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
          Some(Stack::VarThmList(l, mut args, v)) => {
            args.entry(v).or_insert(pr);
            parse! { lexer, tk; let next = Opt(Char(';')), }
            if next {
              stk.push(Stack::VarThmList(l, args, var!()));
              parse! { lexer, tk; Char(','), }
              State::Start
            } else {
              State::VarThmListEnd(l, args)
            }
          }
          Some(Stack::Unary(u)) => match u {
            Unary::AddAsm(tm) => State::Ret(self.add_asm(tm, pr)),
            Unary::Binary(b) => { stk.push(Stack::Unary(Unary::Binary1(b, pr))); State::Start }
            Unary::CContr(tm) => State::Ret(self.ccontr(tm, pr)),
            Unary::Conj1 => State::Ret(self.conj1(pr)),
            Unary::Conj2 => State::Ret(self.conj2(pr)),
            Unary::Contr(tm) => State::Ret(self.contr(tm, pr)),
            Unary::Disch(tm) => State::Ret(self.disch(tm, pr)),
            Unary::Disj1 => State::Ret(self.disj1(pr, term!())),
            Unary::Disj2(tm) => State::Ret(self.disj2(tm, pr)),
            Unary::EqfElim => State::Ret(self.eqf_elim(pr)),
            Unary::EqfIntro => State::Ret(self.eqf_intro(pr)),
            Unary::EqImp1 => State::Ret(self.eq_imp1(pr)),
            Unary::EqImp2 => State::Ret(self.eq_imp2(pr)),
            Unary::EqtElim => State::Ret(self.eqt_elim(pr)),
            Unary::EqtIntro => State::Ret(self.eqt_intro(pr)),
            Unary::Exists(tm1, tm2) => State::Ret(self.exists(tm1, tm2, pr)),
            Unary::Gen(v) => State::Ret(self.gen(v, pr)),
            Unary::Inst(inst) => State::Ret(self.inst(&inst, pr)),
            Unary::InstType(inst) => State::Ret(self.inst_type(&inst, pr)),
            Unary::NotElim => State::Ret(self.not_elim(pr)),
            Unary::NotIntro => State::Ret(self.not_intro(pr)),
            Unary::SelectRule => State::Ret(self.select_rule(pr)),
            Unary::Spec(tm) => State::Ret(self.spec(tm, pr)),
            Unary::Subs(sub) => State::Ret(self.subs(&sub, pr)),
            Unary::Subst(sub, tm) => State::Ret(self.subst(&sub, tm, pr)),
            Unary::Sym => State::Ret(self.sym(pr)),
            Unary::Undisch => State::Ret(self.undisch(pr)),
            Unary::Quant(q, v) => State::Ret(self.eq_quant(q, v, pr)),
            Unary::App1 => State::Ret(self.eq_app1(pr, term!())),
            Unary::App2(tm) => State::Ret(self.eq_app2(tm, pr)),
            Unary::Bin1(f) => State::Ret(self.eq_binary1(f, pr, term!())),
            Unary::Bin2(f, tm) => State::Ret(self.eq_binary2(f, tm, pr)),
            Unary::Not => State::Ret(self.eq_not(pr)),
            Unary::Binary1(b, pr1) => match b {
              Binary::Choose(tm) => State::Ret(self.choose(tm, pr1, pr)),
              Binary::Conj => State::Ret(self.conj(pr1, pr)),
              Binary::DeductAntiSym => State::Ret(self.deduct_antisym(pr1, pr)),
              Binary::DisjCases => {
                stk.push(Stack::Unary(Unary::Binary1(Binary::DisjCases1(pr1), pr)));
                State::Start
              }
              Binary::DisjCases1(pr0) => State::Ret(self.disj_cases(pr0, pr1, pr)),
              Binary::EqMp => State::Ret(self.eq_mp(pr1, pr)),
              Binary::ImpAntiSym => State::Ret(self.imp_antisym(pr1, pr)),
              Binary::ImpTrans => State::Ret(self.imp_trans(pr1, pr)),
              Binary::Mp => State::Ret(self.mp(pr1, pr)),
              Binary::ProveAsm => State::Ret(self.prove_asm(pr1, pr)),
              Binary::Trans => State::Ret(self.trans(pr1, pr)),
              Binary::App => State::Ret(self.eq_app(pr1, pr)),
              Binary::Bin(f) => State::Ret(self.eq_binary(f, pr1, pr)),
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
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tys: &[TypeId]
) -> TypeId {
  let mut tk = lexer.unpack(*ptk);
  parse! { lexer, tk;
    Token::Heading("Type"), Eols,
    let ty = Token::Type(v) => tys[v as usize], Eols,
  }
  *ptk = tk.map(Token::pack);
  ty
}

fn parse_term_section<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tms: &[TermId]
) -> TermId {
  let mut tk = lexer.unpack(*ptk);
  parse! { lexer, tk;
    Token::Heading("Term"), Eols,
    let tm = Token::Term(v) => tms[v as usize], Eols,
  }
  *ptk = tk.map(Token::pack);
  tm
}

impl<'a> ProofArena<'a> {
  fn parse_subproofs_section<I: Iterator<Item=u8>>(&mut self,
    ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, p: &Preambles,
  ) -> Vec<ProofId> {
    let mut named = vec![ProofId(u32::MAX)];
    if matches!(lexer.unpack(*ptk), Some(Token::Heading("Subproofs"))) {
      let mut tk = lexer.next();
      parse! { lexer, tk; Eols, }
      while let Some(Token::Int(v)) = tk {
        assert_eq!(v.parse::<usize>().unwrap(), named.len());
        *ptk = lexer.next().map(Token::pack);
        let n = self.parse(ptk, lexer, p, &named);
        named.push(n);
        tk = lexer.unpack(*ptk);
        parse! { lexer, tk; Eols, }
      }
    }
    named
  }

  fn parse_proof_section<I: Iterator<Item=u8>>(&mut self,
    ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, p: &Preambles, pfs: &[ProofId],
  ) -> ProofId {
    let mut tk = lexer.unpack(*ptk);
    parse! { lexer, tk; Token::Heading("Proof"), Eols, }
    *ptk = tk.map(Token::pack);
    self.parse(ptk, lexer, p, pfs)
  }
}

fn parse_alphalink_section<I: Iterator<Item=u8>>(
  ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tms: &[TermId]
) -> TermId {
  let mut tk = lexer.unpack(*ptk);
  parse! { lexer, tk;
    Token::Heading("Target"), Eols,
    let tm = Token::Term(v) => tms[v as usize], Eols,
  }
  *ptk = tk.map(Token::pack);
  tm
}

impl<'a> ProofArena<'a> {
  fn parse_fetch_preamble<I: Iterator<Item=u8>>(&mut self,
    ptk: &mut Option<PackedToken>, lexer: &mut Lexer<I>, tys: &[TypeId],
  ) -> Vec<ProofId> {
    let mut named = vec![];
    if matches!(lexer.unpack(*ptk), Some(Token::Heading("Fetches"))) {
      let mut tk = lexer.next();
      named.push(ProofId(u32::MAX));
      parse! { lexer, tk; Eols, }
      while let Some(Token::Int(v)) = tk {
        assert_eq!(v.parse::<usize>().unwrap(), named.len());
        tk = lexer.next();
        parse! { lexer, tk; Eols,
          let k = Token::Ident(v) => FetchKind::try_from(v).unwrap(),
          let thm = Token::Str(v) => *self.env.trans.fetches[k].get(v)
            .unwrap_or_else(|| panic!("can't find {:?} {:?}", k, v)),
        }
        let mut args = vec![];
        while let Some(Token::Type(i)) = tk {
          tk = lexer.next();
          args.push(tys[i as usize])
        }
        parse! { lexer, tk; Eols, }
        named.push(self.fetch(thm, args));
      }
    }
    named
  }
}

impl<'a> ProofArena<'a> {
  fn parse_preambles<I: Iterator<Item=u8>>(&mut self,
    tk: &mut Option<PackedToken>, lexer: &mut Lexer<I>,
  ) -> Preambles {
    let tys = self.parse_type_preamble(tk, lexer);
    let tms = self.parse_term_preamble(tk, lexer, &tys);
    let fetches = self.parse_fetch_preamble(tk, lexer, &tys);
    (tys, tms, fetches)
  }
}

impl Environment {
  pub fn parse_owned_type(&mut self, tys: &[&str], ty: &str) -> OwnedType {
    OwnedType::with(self, |a| {
      let tys = a.parse_type_str_preamble(tys);
      a.parse_type_str(&tys, ty)
    }).0
  }
  pub fn parse_owned_term(&mut self, tys: &[&str], tms: &[&str], tm: &str) -> OwnedTerm {
    OwnedTerm::with(self, |a| {
      let tys = a.parse_type_str_preamble(tys);
      let tms = a.parse_term_str_preamble(&tys, tms);
      a.parse_term_str(&tys, &tms, tm)
    }).0
  }
  pub fn parse_thm_def(&mut self, tys: &[&str], tms: &[&str], hyps: &[&str], concl: &str) -> ThmDef {
    ThmDef::with(self, |a| {
      let tys = a.parse_type_str_preamble(tys);
      let tms = a.parse_term_str_preamble(&tys, tms);
      let hyps = hyps.iter().map(|h| a.parse_term_str(&tys, &tms, h)).collect();
      let concl = a.parse_term_str(&tys, &tms, concl);
      a.axiom(hyps, concl)
    }).0
  }
  pub fn parse_typedef_info(&mut self, tys: &[&str], tms: &[&str], concl: &str) -> TypedefInfo {
    ThmDef::with_typedef_info(self, |a| {
      let tys = a.parse_type_str_preamble(tys);
      let tms = a.parse_term_str_preamble(&tys, tms);
      let concl = a.parse_term_str(&tys, &tms, concl);
      a.axiom(vec![], concl)
    }).0
  }
  pub fn parse_const(&mut self, x: &str, tys: &[&str], ty: &str) -> ConstId {
    let ty = self.parse_owned_type(tys, ty);
    self.add_const(x, ty)
  }
  pub fn parse_basic_def(&mut self, x: &str, tys: &[&str], tms: &[&str], tm: &str) -> (ConstId, ThmId) {
    let tm = self.parse_owned_term(tys, tms, tm);
    self.add_basic_def(x, tm)
  }
  pub fn parse_def(&mut self, x: &str, arity: u32, tys: &[&str], tms: &[&str], tm: &str) -> (ConstId, ThmId) {
    let tm = self.parse_owned_term(tys, tms, tm);
    self.add_basic_def(x, tm)
  }
  pub fn parse_basic_typedef(&mut self, x: &str, tys: &[&str], tms: &[&str], tm: &str) -> TyopId {
    let tm = self.parse_typedef_info(tys, tms, tm);
    self.add_basic_typedef(x, tm)
  }
  pub fn parse_thm(&mut self, k: FetchKind,
    x: &str, tys: &[&str], tms: &[&str], hyps: &[&str], concl: &str) -> ThmId {
    let th = self.parse_thm_def(tys, tms, hyps, concl);
    self.add_thm(k, x, th)
  }
  pub fn parse_spec<const N: usize>(&mut self,
    xs: &[&str; N], tys: &[&str], tms: &[&str], tm: &str
  ) -> ([ConstId; N], ThmId) {
    let th = self.parse_thm_def(tys, tms, &[], tm);
    let (cs, th) = self.add_spec(xs, th);
    (cs.try_into().unwrap(), th)
  }
}

impl Importer {
  pub fn import(&mut self, kind: ObjectSpec, data: ObjectData, defer: bool) -> bool {
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
    match kind {
      ObjectSpec::TypeDecl(x) => {
        let arity = parse_int_section(&mut tk, &mut lexer);
        self.env.add_tyop(x, arity, None);
      }
      ObjectSpec::ConstDecl(x) => {
        let (ty, _) = OwnedType::with(&self.env, |a| {
          let tys = a.parse_type_preamble(&mut tk, &mut lexer);
          parse_type_section(&mut tk, &mut lexer, &tys)
        });
        self.env.add_const(x, ty);
      }
      ObjectSpec::Axiom(x) => {
        let (tm, _) = OwnedTerm::with(&self.env, |a| {
          let tys = a.parse_type_preamble(&mut tk, &mut lexer);
          let tms = a.parse_term_preamble(&mut tk, &mut lexer, &tys);
          parse_term_section(&mut tk, &mut lexer, &tms)
        });
        self.env.add_axiom(x, tm);
      }
      ObjectSpec::BasicDef(x) => {
        let (tm, _) = OwnedTerm::with(&self.env, |a| {
          let tys = a.parse_type_preamble(&mut tk, &mut lexer);
          let tms = a.parse_term_preamble(&mut tk, &mut lexer, &tys);
          parse_term_section(&mut tk, &mut lexer, &tms)
        });
        self.env.add_basic_def(x, tm);
      }
      ObjectSpec::Def(x) => {
        let (tm, _) = OwnedTerm::with(&self.env, |a| {
          let tys = a.parse_type_preamble(&mut tk, &mut lexer);
          let tms = a.parse_term_preamble(&mut tk, &mut lexer, &tys);
          parse_term_section(&mut tk, &mut lexer, &tms)
        });
        self.env.add_def(x);
      }
      ObjectSpec::Spec(xs) => {
        let (pr, _) = ThmDef::with(&self.env, |a| {
          let p = a.parse_preambles(&mut tk, &mut lexer);
          let subproofs = a.parse_subproofs_section(&mut tk, &mut lexer, &p);
          a.parse_proof_section(&mut tk, &mut lexer, &p, &subproofs)
        });
        self.env.add_spec(&xs, pr);
      }
      ObjectSpec::BasicTypedef(x) => {
        let (pr, _) = ThmDef::with_typedef_info(&self.env, |a| {
          let p = a.parse_preambles(&mut tk, &mut lexer);
          let subproofs = a.parse_subproofs_section(&mut tk, &mut lexer, &p);
          a.parse_proof_section(&mut tk, &mut lexer, &p, &subproofs)
        });
        self.env.add_basic_typedef(x, pr);
      }
      ObjectSpec::Typedef(_) => unimplemented!(),
      ObjectSpec::TypeBij(xs) => {
        let [x, x1, x2] = *xs;
        let c = self.env.trans.tyops[&x];
        self.env.add_type_bijs(c, &x, x1, x2);
      }
      ObjectSpec::Thm(x) => {
        let pr = ThmDef::with(&self.env, |a| {
          let p = a.parse_preambles(&mut tk, &mut lexer);
          let subproofs = a.parse_subproofs_section(&mut tk, &mut lexer, &p);
          let pr = a.parse_proof_section(&mut tk, &mut lexer, &p, &subproofs);
          a.alpha_link0(pr, parse_alphalink_section(&mut tk, &mut lexer, &p.1))
        });
        self.env.add_thm(FetchKind::Thm, x, ThmDef::default());
      }
      ObjectSpec::OpenThm(x) => {
        let pr = ThmDef::with(&self.env, |a| {
          let p = a.parse_preambles(&mut tk, &mut lexer);
          let subproofs = a.parse_subproofs_section(&mut tk, &mut lexer, &p);
          a.parse_proof_section(&mut tk, &mut lexer, &p, &subproofs)
        });
        self.env.add_thm(FetchKind::OThm, x, ThmDef::default());
      }
      ObjectSpec::NumThm(x) => {
        let pr = ThmDef::with(&self.env, |a| {
          let p = a.parse_preambles(&mut tk, &mut lexer);
          let subproofs = a.parse_subproofs_section(&mut tk, &mut lexer, &p);
          a.parse_proof_section(&mut tk, &mut lexer, &p, &subproofs)
        });
        self.env.add_thm(FetchKind::NThm, x.to_string(), ThmDef::default());
      }
    };
    assert!(matches!(tk, None));
    true
  }
}
