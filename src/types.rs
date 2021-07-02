use std::collections::HashMap;
use std::hash::Hash;
use std::ops::{Index, IndexMut};
use num_bigint::BigUint;

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
pub struct ObjectData {
  pub fl1: bool,
  pub fl2: bool,
  pub file: String,
}

pub trait Idx: Copy {
  fn from(_: u32) -> Self;
  fn into_u32(self) -> u32;
}

macro_rules! idx {($($ty:ident),*) => {
  $(
    #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
    pub struct $ty(pub u32);
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
  App(TermId, TermId),
  Quant(Quant, TermId, TermId),
  Binary(Binary, TermId, TermId),
  Not(TermId),
}

#[derive(Debug)]
pub struct TyopDef {
  pub arity: u32
}

#[derive(Debug)]
pub struct ConstDef {

}

#[derive(Debug)]
pub struct ThmDef {

}
