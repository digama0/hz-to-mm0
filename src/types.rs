use std::borrow::Cow;
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::{Index, IndexMut};
use num_bigint::BigUint;
use crate::{Dedup};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ObjectSpec {
  Axiom(String),
  Thm(String),
  OpenThm(String),
  NumThm(u32),
  TypeDecl(String),
  BasicTypedef(String),
  Typedef(String),
  ConstDecl(String),
  BasicDef(String),
  Def(String),
  Spec(Box<[String]>),
  TypeBij(Box<[String; 3]>),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum FetchKind {
  Axiom,
  Thm,
  OThm,
  NThm,
  BasicDef,
  BasicTypedef,
  BasicTypedefInput,
  Typedef,
  TypedefInput,
  Def,
  Spec,
  SpecInput,
  TypeBij1,
  TypeBij2,
}

#[derive(Default, Debug)]
pub struct FetchVec<T>([T; 14]);

impl<T> Index<FetchKind> for FetchVec<T> {
  type Output = T;
  fn index(&self, i: FetchKind) -> &T { &self.0[i as usize] }
}
impl<T> IndexMut<FetchKind> for FetchVec<T> {
  fn index_mut(&mut self, i: FetchKind) -> &mut T { &mut self.0[i as usize] }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fetch(pub FetchKind, pub String);

#[derive(Clone, Debug)]
pub enum ParsedObjectData {
  _Thm(ThmId),
}

#[derive(Clone, Debug)]
pub struct UnparsedObjectData {
  pub fl1: bool,
  pub fl2: bool,
  pub file: String,
}

pub enum ObjectData {
  Unparsed(UnparsedObjectData),
  _Parsed(ParsedObjectData),
}

pub trait Idx: Copy {
  fn from(_: u32) -> Self;
  fn into_u32(self) -> u32;
}

macro_rules! idx {($($ty:ident),*) => {
  $(
    #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
    pub struct $ty(u32);
    impl Idx for $ty {
      fn from(n: u32) -> Self { Self(n) }
      fn into_u32(self) -> u32 { self.0 }
    }
  )*
}}

idx! { TyopId, ConstId, ThmId, TypeId, TermId, ProofId }

#[derive(Default, Debug)]
pub struct TransTable {
  pub tyops: HashMap<String, TyopId>,
  pub consts: HashMap<String, ConstId>,
  pub fetches: FetchVec<HashMap<String, ThmId>>,
}

impl TransTable {
  pub fn contains(&self, k: &ObjectSpec) -> bool {
    match k {
      ObjectSpec::TypeDecl(x) => self.tyops.contains_key(x),
      ObjectSpec::ConstDecl(x) => self.consts.contains_key(x),
      ObjectSpec::Axiom(x) => self.fetches[FetchKind::Axiom].contains_key(x),
      ObjectSpec::BasicDef(x) => self.fetches[FetchKind::BasicDef].contains_key(x),
      ObjectSpec::Def(x) => self.fetches[FetchKind::Def].contains_key(x),
      ObjectSpec::Spec(xs) => xs.iter().any(|x| self.fetches[FetchKind::Spec].contains_key(x)),
      ObjectSpec::BasicTypedef(x) => self.fetches[FetchKind::BasicTypedef].contains_key(x),
      ObjectSpec::Typedef(x) => self.fetches[FetchKind::Typedef].contains_key(x),
      ObjectSpec::TypeBij(x) => self.fetches[FetchKind::TypeBij1].contains_key(&x[0]),
      ObjectSpec::Thm(x) => self.fetches[FetchKind::Thm].contains_key(x),
      ObjectSpec::OpenThm(x) => self.fetches[FetchKind::OThm].contains_key(x),
      ObjectSpec::NumThm(x) => self.fetches[FetchKind::NThm].contains_key(&x.to_string()),
    }
  }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Type {
  Var(String),
  Fun(TypeId, TypeId),
  Comp(String, Vec<TypeId>),
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Binary {
  Conj,
  Disj,
  Imp,
  Eq,
  Pair,
  Bin(TermId),
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum NumOp {
  Suc,
  Pre,
  Add,
  Sub,
  Mult,
  Exp,
  Even,
  Odd,
  Eq,
  Lt,
  Le,
  Gt,
  Ge,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Quant {
  Lambda,
  Forall,
  Exists,
  UExists,
  Select,
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Term {
  Var(String, TypeId),
  OConst(String, Vec<TypeId>),
  BigInt(BigUint),
  Comb(TermId, TermId),
  Quant(Quant, TermId, TermId),
  Binary(Binary, TermId, TermId),
  Not(TermId),
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Proof {
  Fetch(ThmId),
  AddAsm(TermId, ProofId),
  Alpha(TermId, TermId),
  AlphaConv(TermId, TermId),
  Assume(TermId),
  BetaConv(TermId),
  CContr(TermId, ProofId),
  Choose(TermId, ProofId, ProofId),
  Conj(ProofId, ProofId),
  Conj1(ProofId),
  Conj2(ProofId),
  Contr(TermId, ProofId),
  DeductAntiSym(ProofId, ProofId),
  Disch(TermId, ProofId),
  Disj1(ProofId, TermId),
  Disj2(TermId, ProofId),
  DisjCases(ProofId, ProofId, ProofId),
  EqfElim(ProofId),
  EqfIntro(ProofId),
  EqImp1(ProofId),
  EqImp2(ProofId),
  EqMp(ProofId, ProofId),
  EqtElim(ProofId),
  EqtIntro(ProofId),
  EtaConv(TermId),
  Exists(TermId, TermId, ProofId),
  Gen(TermId, ProofId),
  ImpAntiSym(ProofId, ProofId),
  ImpTrans(ProofId, ProofId),
  Inst(Vec<(TermId, TermId)>, ProofId),
  InstType(Vec<(TypeId, TypeId)>, ProofId),
  Mp(ProofId, ProofId),
  NotElim(ProofId),
  NotIntro(ProofId),
  ProveAsm(ProofId, ProofId),
  Refl(TermId),
  SelectRule(ProofId),
  Spec(TermId, ProofId),
  Subs(Vec<ProofId>, ProofId),
  SubsConv(Vec<ProofId>, TermId),
  Subst(Vec<(TermId, ProofId)>, TermId, ProofId),
  SubstConv(Vec<(TermId, ProofId)>, TermId, TermId),
  Sym(ProofId),
  SymConv(TermId),
  Trans(ProofId, ProofId),
  Undisch(ProofId),
  Quant(Quant, TermId, ProofId),
  Comb(ProofId, ProofId),
  Comb1(ProofId, TermId),
  Comb2(TermId, ProofId),
  Bin(Binary, ProofId, ProofId),
  Bin1(Binary, ProofId, TermId),
  Bin2(Binary, TermId, ProofId),
  Not(ProofId),
  NumConv(NumOp, TermId),
}

pub trait Node: Hash + Eq { type Idx: Idx; }
impl Node for Type { type Idx = TypeId; }
impl Node for Term { type Idx = TermId; }
impl Node for Proof { type Idx = ProofId; }

#[derive(Debug)]
pub struct Preambles {
  pub tys: Dedup<Type>,
  pub tms: Dedup<Term>,
  pub fetches: Vec<(ThmId, Vec<TypeId>)>,
}

#[derive(Debug)]
pub enum Object {
  TypeDecl(String, u32),
  ConstDecl(String, Dedup<Type>, TypeId),
  Axiom(String, Dedup<Type>, Dedup<Term>, TermId),
  BasicDef(String, Dedup<Type>, Dedup<Term>, TermId),
  Def(String, Dedup<Type>, Dedup<Term>, TermId),
  Spec(Box<[String]>, Preambles, Dedup<Proof>, ProofId),
  BasicTypedef(String, Preambles, Dedup<Proof>, ProofId),
  Thm(String, Preambles, Dedup<Proof>, ProofId, TermId),
  OpenThm(String, Preambles, Dedup<Proof>, ProofId),
  NumThm(u32, Preambles, Dedup<Proof>, ProofId),
  TypeBij([String; 3]),
}

#[derive(Debug)]
pub struct TyopDef {
  pub arity: u32
}

#[derive(Debug)]
pub struct ConstDef;
#[derive(Debug)]
pub struct ThmDef;

#[derive(Debug)]
pub struct Environment {
  pub tyops: Vec<TyopDef>,
  pub consts: Vec<ConstDef>,
  pub thms: Vec<ThmDef>,
  pub trans: TransTable,
}

impl Environment {
  pub fn add_tyop<'a>(&mut self, name: impl Into<Cow<'a, str>>, d: TyopDef) {
    let n = Idx::from(self.tyops.len() as u32);
    self.tyops.push(d);
    assert!(self.trans.tyops.insert(name.into().into_owned(), n).is_none());
  }
  pub fn add_const<'a>(&mut self, name: impl Into<Cow<'a, str>>, d: ConstDef) {
    let n = Idx::from(self.consts.len() as u32);
    self.consts.push(d);
    assert!(self.trans.consts.insert(name.into().into_owned(), n).is_none());
  }
  pub fn add_thm<'a>(&mut self, k: FetchKind, name: impl Into<Cow<'a, str>>, d: ThmDef) {
    let n = Idx::from(self.thms.len() as u32);
    self.thms.push(d);
    assert!(self.trans.fetches[k].insert(name.into().into_owned(), n).is_none());
  }

  pub fn add_type_bijs<'a>(&mut self, x: impl Into<Cow<'a, str>>, x1: impl Into<Cow<'a, str>>, x2: impl Into<Cow<'a, str>>) {
    self.add_const(x1, ConstDef);
    self.add_const(x2, ConstDef);
    let x = x.into();
    self.add_thm(FetchKind::TypeBij1, &*x, ThmDef);
    self.add_thm(FetchKind::TypeBij2, x, ThmDef);
  }

  pub fn add_basic_def<'a>(&mut self, x: impl Into<Cow<'a, str>>) {
    let x = x.into(); self.add_const(&*x, ConstDef);
    self.add_thm(FetchKind::BasicDef, x, ThmDef);
  }

  pub fn add_def<'a>(&mut self, x: impl Into<Cow<'a, str>>) {
    let x = x.into(); self.add_const(&*x, ConstDef);
    self.add_thm(FetchKind::Def, x, ThmDef);
  }

  pub fn add_basic_typedef<'a>(&mut self, x: impl Into<Cow<'a, str>>) {
    let x = x.into(); self.add_tyop(&*x, TyopDef {arity: 0}); // TODO
    self.add_thm(FetchKind::BasicTypedef, &*x, ThmDef);
    self.add_thm(FetchKind::BasicTypedefInput, x, ThmDef);
  }

  pub fn add_spec<'a, I: Into<Cow<'a, str>>>(&mut self, xs: impl IntoIterator<Item=I>) {
    for x in xs {
      let x = x.into(); self.add_const(&*x, ConstDef);
      self.add_thm(FetchKind::Spec, x, ThmDef)
    }
  }

  pub fn add(&mut self, o: Object) {
    match o {
      Object::TypeDecl(x, arity) => self.add_tyop(x, TyopDef {arity}),
      Object::ConstDecl(x, _, _) => self.add_const(x, ConstDef),
      Object::Axiom(x, _, _, _) => self.add_thm(FetchKind::Axiom, x, ThmDef),
      Object::BasicDef(x, _, _, _) => self.add_basic_def(x),
      Object::Def(x, _, _, _) => self.add_def(x),
      Object::Spec(xs, _, _, _) => self.add_spec(Vec::from(xs)),
      Object::BasicTypedef(x, _, _, _) => self.add_basic_typedef(x),
      Object::Thm(x, _, _, _, _) => self.add_thm(FetchKind::Thm, x, ThmDef),
      Object::OpenThm(x, _, _, _) => self.add_thm(FetchKind::OThm, x, ThmDef),
      Object::NumThm(x, _, _, _) => self.add_thm(FetchKind::NThm, x.to_string(), ThmDef),
      Object::TypeBij([x, x1, x2]) => self.add_type_bijs(&x, x1, x2),
    }
  }
}