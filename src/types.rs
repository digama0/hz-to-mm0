use std::collections::HashMap;
use std::hash::Hash;
use std::ops::{Index, IndexMut};

use crate::kernel::{OwnedType, TermStore};

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
  // BasicTypedef,
  // BasicTypedefInput,
  Typedef,
  // TypedefInput,
  Def,
  Spec,
  // SpecInput,
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
  fn into_usize(self) -> usize { self.into_u32() as usize }
}

macro_rules! idx {($($ty:ident),*) => {
  $(
    #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
    pub struct $ty(pub u32);
    impl Idx for $ty {
      fn from(n: u32) -> Self { Self(n) }
      fn into_u32(self) -> u32 { self.0 }
    }
    impl Default for $ty {
      fn default() -> $ty { $ty(u32::MAX) }
    }
  )*
}}

idx! { TyopId, ConstId, ThmId, TyVarId, TypeId, VarId, TermId, HypsId, ProofId }

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
      ObjectSpec::BasicTypedef(_) => false, //self.fetches[FetchKind::BasicTypedef].contains_key(x),
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
  TyVar(TyVarId),
  Tyop(TyopId, Vec<TypeId>),
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Binary {
  Conj,
  Disj,
  Imp,
  Eq,
  Pair,
  Bin(TermId),
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
  Var(VarId),
  Const(ConstId, Vec<TypeId>),
  App(TermId, TermId),
  Lam(VarId, TermId),
}

#[derive(Debug)]
pub struct TyopDef {
  pub name: String,
  pub arity: u32,
  pub tydef: Option<ThmId>,
}

#[derive(Debug)]
pub struct ConstDef {
  pub name: String,
  pub ty: OwnedType,
}

#[derive(Debug)]
pub struct ThmDef {
  pub arena: TermStore,
  pub tyvars: Box<[TyVarId]>,
  pub hyps: Box<[TermId]>,
  pub concl: TermId,
}
