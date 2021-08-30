use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::convert::TryInto;
use std::hash::Hash;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Index;
use std::ops::IndexMut;
use std::borrow::Cow;
use std::sync::{Arc, Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::sync::atomic::{AtomicBool, Ordering::SeqCst};
use bitvec::{bitbox, prelude::BitBox};
use num::{BigUint, Zero, CheckedSub};
use crate::mm0;
use super::print::EnvPrint;
use super::print::Print;
use super::types::*;

pub trait Node: Hash + Eq { type Idx: Idx; }
impl Node for TyVar { type Idx = TyVarId; }
impl Node for Type { type Idx = TypeId; }
impl Node for Var { type Idx = VarId; }
impl Node for Term { type Idx = TermId; }
impl Node for Proof { type Idx = ProofId; }
impl Node for Hyps { type Idx = HypsId; }

pub static PRINT: AtomicBool = AtomicBool::new(false);

#[allow(unused)] pub fn get_print() -> bool { PRINT.load(SeqCst) }
#[allow(unused)] pub fn set_print(b: bool) { PRINT.store(b, SeqCst) }

#[derive(Debug)]
pub struct Store<H: ?Sized, A = ()>(Vec<(Arc<H>, A)>);

impl<H: ?Sized, A: Clone> Clone for Store<H, A> {
  fn clone(&self) -> Self { Self(self.0.clone()) }
}
impl<H: Node + ?Sized, A> Index<H::Idx> for Store<H, A> {
  type Output = (Arc<H>, A);
  fn index(&self, n: H::Idx) -> &Self::Output {
    &self.0[n.into_usize()]
  }
}
impl<H: Node + ?Sized, A> IndexMut<H::Idx> for Store<H, A> {
  fn index_mut(&mut self, n: H::Idx) -> &mut Self::Output {
    &mut self.0[n.into_usize()]
  }
}

impl<H: ?Sized, A> Default for Store<H, A> {
  fn default() -> Self { Self(vec![]) }
}

#[derive(Debug)]
struct Dedup<H: ?Sized, A = ()> {
  map: HashMap<Arc<H>, u32>,
  store: Store<H, A>,
}

impl<H: ?Sized, A> Default for Dedup<H, A> {
  fn default() -> Self { Self { map: Default::default(), store: Default::default() } }
}

impl<H: Node + ?Sized, A> Index<H::Idx> for Dedup<H, A> {
  type Output = (Arc<H>, A);
  fn index(&self, n: H::Idx) -> &Self::Output { &self.store[n] }
}

impl<H: Node + ?Sized, A> IndexMut<H::Idx> for Dedup<H, A> {
  fn index_mut(&mut self, n: H::Idx) -> &mut Self::Output { &mut self.store[n] }
}

impl<H: Node + ?Sized, A> Dedup<H, A> {
  fn add_inner(&mut self, v: Arc<H>, a: A) -> (H::Idx, bool) {
    match self.map.entry(v) {
      Entry::Vacant(e) => {
        let vec = &mut self.store.0;
        let n = vec.len() as u32;
        vec.push((e.key().clone(), a));
        e.insert(n);
        (Idx::from(n), false)
      }
      Entry::Occupied(e) => (Idx::from(*e.get()), true),
    }
  }
}

impl<H: Node, A> Dedup<H, A> {
  #[inline] fn add_val(&mut self, v: H, a: A) -> H::Idx { self.add_inner(Arc::new(v), a).0 }
  #[inline] fn add_default(&mut self, v: H) -> (H::Idx, bool) where A: Default {
    self.add_inner(Arc::new(v), A::default())
  }
}
impl<H: Node> Dedup<H> {
  #[inline] fn add(&mut self, v: H) -> H::Idx { self.add_val(v, ()) }
}

pub type TyVar = str;

#[derive(Debug, Clone, Default)]
pub struct TypeStore(pub Store<Type>);

pub trait HasTypeStore: Index<TypeId, Output=Arc<Type>> {
  fn type_store(&self) -> &Store<Type>;

  fn dest_tyvar(&self, a: TypeId) -> TyVarId {
    if let Type::TyVar(v) = *self[a] { v }
    else { panic!("dest_tyvar: not a variable") }
  }

  fn dest_fun(&self, a: TypeId) -> (TypeId, TypeId) {
    if let Type::Tyop(TyopId::FUN, ref args) = *self[a] { (args[0], args[1]) }
    else { panic!("dest_fun: not a function type") }
  }

  fn dest_prod(&self, a: TypeId) -> (TypeId, TypeId) {
    if let Type::Tyop(TyopId::PROD, ref args) = *self[a] { (args[0], args[1]) }
    else { panic!("dest_prod: not a product type") }
  }

  fn is_bool(&self, ty: TypeId) -> bool {
    matches!(*self[ty], Type::Tyop(TyopId::BOOL, _))
  }

  fn types(&self) -> &[(Arc<Type>, ())] { &self.type_store().0 }

  fn print_with_env<'a, T>(&'a self, env: Option<&'a EnvRef<'a>>, t: T) -> Print<'a, Self, T> {
    Print {env, arena: self, t}
  }

  fn tyvars_in_type(&self, ty: TypeId) -> Box<[TyVarId]> {
    let mut c = CollectTyVarsType::new(self);
    c.collect(self, ty);
    c.get()
  }
}

macro_rules! impl_index { ($ty:ty: $($tgt:ty => $f:ident),*) => {$(
  impl Index<<$tgt as Node>::Idx> for $ty {
    type Output = Arc<$tgt>;
    fn index(&self, n: <$tgt as Node>::Idx) -> &Arc<$tgt> { &self.$f()[n].0 }
  }
)*}}

impl_index!(TypeStore: Type => type_store);
impl HasTypeStore for TypeStore {
  fn type_store(&self) -> &Store<Type> { &self.0 }
}

#[derive(Debug)]
pub struct TypeArena<'a> {
  pub env: &'a Environment,
  tys: Dedup<Type>,
  bool: Option<TypeId>,
  bool_unop: Option<TypeId>,
  bool_binop: Option<TypeId>,
}

impl_index!(TypeArena<'_>: Type => type_store);
impl HasTypeStore for TypeArena<'_> {
  fn type_store(&self) -> &Store<Type> { &self.tys.store }
}

#[macro_export]
macro_rules! ty {
  ($self:expr, {$($e:tt)*}) => { {$($e)*} };
  ($self:expr, ($($e:tt)*)) => { ty!($self, $($e)*) };
  ($self:expr, bool) => {{ $self.mk_bool() }};
  ($self:expr, V($x:expr)) => {{ let x = $x; $self.mk_tyvar(x) }};
  ($self:expr, $e:tt -> $($e2:tt)*) => {{
    let e = ty!($self, $e); let e2 = ty!($self, $($e2)*); $self.mk_fun(e, e2)
  }};
  ($self:expr, $e:tt * $($e2:tt)*) => {{
    let e = ty!($self, $e); let e2 = ty!($self, $($e2)*); $self.mk_prod(e, e2)
  }};
  ($self:expr, $($e:tt)*) => {{$($e)*}};
}

#[macro_export]
macro_rules! term {
  ($self:expr, {$($e:tt)*}) => { {$($e)*} };
  ($self:expr, ($($e:tt)*)) => { term!($self, $($e)*) };
  ($self:expr, A $e:tt $e2:tt) => {{
    let e = term!($self, $e); let e2 = term!($self, $e2); $self.mk_app(e, e2)
  }};
  ($self:expr, A $e:tt $e2:tt $e3:tt) => {{
    let e = term!($self, $e); let e2 = term!($self, $e2); let e3 = term!($self, $e3);
    $self.mk_app2(e, e2, e3)
  }};
  ($self:expr, K($e:expr, $args:expr)) => {{
    let e = $e; let args = $args; $self.mk_const(e, args)
  }};
  ($self:expr, K($e:expr)) => {{ let e = $e; $self.mk_const0(e) }};
  ($self:expr, V($x:ident: $($t:tt)*)) => {{
    let ty = ty!($self, $($t)*);
    $self.mk_var_id(VarName::Str(stringify!($x).into()), ty)
  }};
  ($self:expr, V($e:expr)) => {{ let e = $e; $self.mk_var(e) }};
  ($self:expr, L $x:tt $t:tt) => {{
    let x = $x; let t = term!($self, $t); $self.mk_lam(x, t)
  }};
  ($self:expr, !$x:tt. $($t:tt)*) => {{
    let x = $x; let t = term!($self, $($t)*); $self.mk_forall(x, t)
  }};
  ($self:expr, ?$x:tt. $($t:tt)*) => {{
    let x = $x; let t = term!($self, $($t)*); $self.mk_exists(x, t)
  }};
  ($self:expr, $e:tt => $($e2:tt)*) => {{
    let e = term!($self, $e); let e2 = term!($self, $($e2)*); $self.mk_imp(e, e2)
  }};
  ($self:expr, $e:tt = $e2:tt) => {{
    let e = term!($self, $e); let e2 = term!($self, $e2); $self.mk_eq(e, e2)
  }};
  ($self:expr, $($e:tt)*) => {{$($e)*}};
}

#[macro_export]
macro_rules! thm {
  ($self:expr, {$($e:tt)*}) => { {$($e)*} };
  ($self:expr, ($($e:tt)*)) => { thm!($self, $($e)*) };
  ($self:expr, A [$($e:tt)*] [$($e2:tt)*]) => {{
    let e = thm!($self, $($e)*); let e2 = thm!($self, $($e2)*); $self.eq_app(e, e2)
  }};
  ($self:expr, A [$($e:tt)*] $e2:tt) => {{
    let e = thm!($self, $($e)*); let e2 = term!($self, $e2); $self.eq_app1(e, e2)
  }};
  ($self:expr, A $e:tt [$($e2:tt)*]) => {{
    let e = term!($self, $e); let e2 = thm!($self, $($e2)*); $self.eq_app2(e, e2)
  }};
  ($self:expr, A $e:tt [$($e2:tt)*] [$($e3:tt)*]) => {{
    let e = term!($self, $e); let e2 = thm!($self, $($e2)*); let e3 = thm!($self, $($e3)*);
    $self.eq_bin(e, e2, e3)
  }};
  ($self:expr, A $e:tt [$($e2:tt)*] $e3:tt) => {{
    let e = term!($self, $e); let e2 = thm!($self, $($e2)*); let e3 = term!($self, $e3);
    $self.eq_bin1(e, e2, e3)
  }};
  ($self:expr, A $e:tt $e2:tt [$($e3:tt)*]) => {{
    let e = term!($self, $e); let e2 = term!($self, $e2); let e3 = thm!($self, $($e3)*);
    $self.eq_bin2(e, e2, e3)
  }};
  ($self:expr, L $x:tt [$($t:tt)*]) => {{
    let x = $x; let t = thm!($self, $($t)*); $self.eq_lam(x, t)
  }};
  ($self:expr, add($src:expr, $hyps:expr, $($t:tt)*)) => {{
    let src = { #[allow(unused)] use ProofTrace::*; $src };
    let hyps = $hyps; let concl = term!($self, $($t)*); $self.add(hyps, concl, src)
  }};
  ($self:expr, add0($src:expr, $($t:tt)*)) => {{
    let src = { #[allow(unused)] use ProofTrace::*; $src };
    let concl = term!($self, $($t)*); $self.add0(concl, src)
  }};
  ($self:expr, $($e:tt)*) => {{$($e)*}};
}

impl<'a> TypeArena<'a> {
  pub fn into_store(self) -> TypeStore { TypeStore(self.tys.store) }
  pub fn new(env: &'a Environment) -> Self {

    Self {
      env, tys: Dedup::default(),
      bool: None, bool_unop: None, bool_binop: None,
    }
  }

  pub fn mk_tyvar(&mut self, x: TyVarId) -> TypeId {
    self.tys.add(Type::TyVar(x))
  }

  pub fn mk_fun(&mut self, a: TypeId, b: TypeId) -> TypeId {
    self.tys.add(Type::Tyop(TyopId::FUN, vec![a, b]))
  }

  pub fn mk_prod(&mut self, ty1: TypeId, ty2: TypeId) -> TypeId {
    self.tys.add(Type::Tyop(TyopId::PROD, vec![ty1, ty2]))
  }

  pub fn mk_tyop(&mut self, c: TyopId, tys: Vec<TypeId>) -> TypeId {
    assert_eq!(self.env.read()[c].arity as usize, tys.len());
    self.tys.add(Type::Tyop(c, tys))
  }

  fn inst_owned(&mut self, inst: &[TypeId],
    &OwnedType {ref tyvars, ref arena, ty}: &OwnedType) -> TypeId {
    assert_eq!(tyvars.len(), inst.len());
    let map = tyvars.iter().copied().zip(inst.iter().copied()).collect();
    (self, arena).inst_type(&map, |mut tr| tr.tr(ty))
  }

  fn import<R, S: HasTypeStore>(&mut self, store: &S,
    f: impl FnOnce(TypeTranslator<'_, (&mut TypeArena<'a>, &S)>) -> R
  ) -> R { (self, store).import(f) }

  fn mk_bool(&mut self) -> TypeId {
    if let Some(t) = self.bool { t } else {
      let bool = self.mk_tyop(TyopId::BOOL, vec![]);
      *self.bool.insert(bool)
    }
  }

  fn get_bool_unop(&mut self) -> TypeId {
    if let Some(t) = self.bool_unop { t } else {
      let bool = self.mk_bool();
      let f = self.mk_fun(bool, bool);
      *self.bool_unop.insert(f)
    }
  }

  fn get_bool_binop(&mut self) -> TypeId {
    if let Some(t) = self.bool_binop { t } else {
      let f = ty!(self, bool -> self.get_bool_unop());
      *self.bool_binop.insert(f)
    }
  }

  #[allow(unused)]
  pub fn pp<'b, T>(&'b self, env: &'b EnvRef<'b>, t: T) -> Print<'b, Self, T> {
    self.print_with_env(Some(env), t)
  }
}

pub trait TypeArenaPair<'a>: Sized {
  type S: HasTypeStore;
  fn ty_dest_ref(&self) -> &TypeArena<'a>;
  fn ty_dest(&mut self) -> &mut TypeArena<'a>;
  fn ty_src(&self) -> &Self::S;

  fn inst_type<R>(&mut self, inst: &HashMap<TyVarId, TypeId>,
    f: impl FnOnce(TypeTranslator<'_, Self>) -> R
  ) -> R {
    let mut vec = vec![None; self.ty_src().types().len()];
    f(TypeTranslator { arena: self, inst, tys: &mut vec })
  }

  fn import<R>(&mut self, f: impl FnOnce(TypeTranslator<'_, Self>) -> R) -> R {
    self.inst_type(&Default::default(), f)
  }
}

impl<'a, S: HasTypeStore> TypeArenaPair<'a> for (&mut TypeArena<'a>, &S) {
  type S = S;
  #[inline] fn ty_dest_ref(&self) -> &TypeArena<'a> { self.0 }
  #[inline] fn ty_dest(&mut self) -> &mut TypeArena<'a> { self.0 }
  #[inline] fn ty_src(&self) -> &Self::S { self.1 }
}

impl<'a> TypeArenaPair<'a> for TypeArena<'a> {
  type S = Self;
  #[inline] fn ty_dest_ref(&self) -> &TypeArena<'a> { self }
  #[inline] fn ty_dest(&mut self) -> &mut TypeArena<'a> { self }
  #[inline] fn ty_src(&self) -> &Self::S { self }
}

pub struct TypeTranslator<'b, S> {
  pub arena: &'b mut S,
  inst: &'b HashMap<TyVarId, TypeId>,
  tys: &'b mut [Option<TypeId>],
}

impl<'a, 'b, S: TypeArenaPair<'a>> TypeTranslator<'b, S> {
  fn tr(&mut self, ty: TypeId) -> TypeId {
    if let Some(i) = self.tys[ty.into_usize()] { return i }
    let n = match *self.arena.ty_src()[ty] {
      Type::TyVar(n) => self.inst.get(&n).copied().unwrap_or_else(||
        self.arena.ty_dest().mk_tyvar(n)),
      Type::Tyop(c, ref tys) => {
        let tys = tys.clone().iter().map(|&ty| self.tr(ty)).collect();
        self.arena.ty_dest().mk_tyop(c, tys)
      }
    };
    self.tys[ty.into_usize()] = Some(n);
    n
  }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum VarName {
  Str(Arc<str>),
  Genvar(u32),
}
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Var {
  pub name: VarName,
  pub ty: TypeId
}

#[derive(Debug, Clone, Default)]
pub struct TermStore {
  pub tys: TypeStore,
  pub vars: Store<Var>,
  pub tms: Store<Term, TypeId>
}

pub trait HasTermStore:
  HasTypeStore +
  Index<VarId, Output=Arc<Var>> +
  Index<TermId, Output=Arc<Term>>
{
  fn var_store(&self) -> &Store<Var>;
  fn term_store(&self) -> &Store<Term, TypeId>;

  fn vars(&self) -> &[(Arc<Var>, ())] { &self.var_store().0 }

  fn terms(&self) -> &[(Arc<Term>, TypeId)] { &self.term_store().0 }

  fn type_of(&self, tm: TermId) -> TypeId { self.term_store()[tm].1 }

  fn is_boolean(&self, tm: TermId) -> bool { self.is_bool(self.type_of(tm)) }

  fn dest_var(&self, x: TermId) -> VarId {
    if let Term::Var(v) = *self[x] { v } else { panic!("dest_var: not a variable") }
  }

  fn try_dest_app(&self, a: TermId) -> Option<(TermId, TermId)> {
    if let Term::App(a, b) = *self[a] { Some((a, b)) } else { None }
  }

  fn try_dest_lam(&self, a: TermId) -> Option<(VarId, TermId)> {
    if let Term::Lam(a, b) = *self[a] { Some((a, b)) } else { None }
  }

  fn dest_app(&self, a: TermId) -> (TermId, TermId) {
    self.try_dest_app(a).expect("dest_app: not an application")
  }

  fn dest_lam(&self, a: TermId) -> (VarId, TermId) {
    self.try_dest_lam(a).expect("dest_lam: not a lambda")
  }

  fn try_dest_const(&self, c: ConstId, e: TermId) -> Option<&[TypeId]> {
    match *self[e] {
      Term::Const(c2, ref ts) if c == c2 => Some(ts),
      _ => None
    }
  }

  fn dest_const(&self, c: ConstId, e: TermId) -> &[TypeId] {
    self.try_dest_const(c, e).expect("dest_const: constant mismatch")
  }

  fn try_dest_binder(&self, c: ConstId, a: TermId) -> Option<(VarId, TermId)> {
    let (e, f) = self.try_dest_app(a)?;
    self.try_dest_const(c, e)?;
    self.try_dest_lam(f)
  }

  fn try_dest_forall(&self, a: TermId) -> Option<(VarId, TermId)> {
    self.try_dest_binder(ConstId::FORALL, a)
  }

  fn try_dest_exists(&self, a: TermId) -> Option<(VarId, TermId)> {
    self.try_dest_binder(ConstId::EXISTS, a)
  }

  fn dest_forall(&self, a: TermId) -> (VarId, TermId) {
    self.try_dest_forall(a).expect("dest_forall: not a forall")
  }

  fn dest_exists(&self, a: TermId) -> (VarId, TermId) {
    self.try_dest_exists(a).expect("dest_exists: not an exists")
  }

  fn strip_forall(&self, mut a: TermId) -> (Vec<VarId>, TermId) {
    let mut vs = vec![];
    while let Some((v, t)) = self.try_dest_forall(a) { vs.push(v); a = t }
    (vs, a)
  }

  fn strip_app(&self, mut a: TermId) -> (TermId, Vec<TermId>) {
    let mut vs = vec![];
    while let Some((t, e)) = self.try_dest_app(a) { vs.push(e); a = t }
    vs.reverse();
    (a, vs)
  }

  fn try_dest_unop(&self, c: ConstId, a: TermId) -> Option<TermId> {
    let (f, x) = self.try_dest_app(a)?;
    self.try_dest_const(c, f)?;
    Some(x)
  }

  fn try_dest_bin(&self, c: ConstId, a: TermId) -> Option<(TermId, TermId)> {
    let (f, y) = self.try_dest_app(a)?;
    Some((self.try_dest_unop(c, f)?, y))
  }

  fn try_dest_conj(&self, a: TermId) -> Option<(TermId, TermId)> { self.try_dest_bin(ConstId::CONJ, a) }

  fn try_dest_disj(&self, a: TermId) -> Option<(TermId, TermId)> { self.try_dest_bin(ConstId::DISJ, a) }

  fn try_dest_imp(&self, a: TermId) -> Option<(TermId, TermId)> { self.try_dest_bin(ConstId::IMP, a) }

  fn try_dest_eq(&self, a: TermId) -> Option<(TermId, TermId)> { self.try_dest_bin(ConstId::EQ, a) }

  fn try_dest_pair(&self, a: TermId) -> Option<(TermId, TermId)> { self.try_dest_bin(ConstId::PAIR, a) }

  fn try_dest_not(&self, a: TermId) -> Option<TermId> { self.try_dest_unop(ConstId::NOT, a) }

  fn dest_conj(&self, a: TermId) -> (TermId, TermId) {
    self.try_dest_conj(a).expect("dest_conj: expected a conjunction")
  }

  fn dest_disj(&self, a: TermId) -> (TermId, TermId) {
    self.try_dest_disj(a).expect("dest_disj: expected a disjunction")
  }

  fn dest_imp(&self, a: TermId) -> (TermId, TermId) {
    self.try_dest_imp(a).expect("dest_imp: expected an implication")
  }

  fn dest_eq(&self, a: TermId) -> (TermId, TermId) {
    self.try_dest_eq(a).expect("dest_eq: expected an equality")
  }

  fn dest_pair(&self, a: TermId) -> (TermId, TermId) {
    self.try_dest_pair(a).expect("dest_pair: expected a pair")
  }

  fn dest_not(&self, a: TermId) -> TermId {
    self.try_dest_not(a).expect("dest_not: expected a negation")
  }

  fn try_dest_raw_int(&self, strict: bool, mut t: TermId) -> Option<BigUint> {
    let mut out = BigUint::zero();
    for bit in 0.. {
      match *self[t] {
        Term::Const(ConstId::ZERO, _) => {
          if strict && bit != 0 { return None }
          return Some(out)
        }
        Term::App(f, e) => {
          match *self[f] {
            Term::Const(ConstId::BIT0, _) => {}
            Term::Const(ConstId::BIT1, _) => { out.set_bit(bit, true) }
            _ => return None,
          }
          t = e;
        }
        _ => return None,
      }
    }
    unreachable!()
  }

  fn try_dest_int(&self, strict: bool, t: TermId) -> Option<BigUint> {
    let t = self.try_dest_unop(ConstId::NUMERAL, t)?;
    self.try_dest_raw_int(strict, t)
  }

  fn dest_int(&self, strict: bool, t: TermId) -> BigUint {
    self.try_dest_int(strict, t).expect("dest_int: not a numeral")
  }

  fn alpha_cmp(&self, a: TermId, b: TermId) -> Ordering {
    fn rec<T: HasTermStore + ?Sized>(this: &T,
      ctx: &mut Vec<(VarId, VarId)>, a: TermId, b: TermId
    ) -> Ordering {
      if a == b && ctx.iter().all(|&(x, y)| x == y) { return Ordering::Equal }
      // if get_print() {
      //   println!("alpha_cmp {}:\n  {}\n= {}",
      //     this.print_with_env(None, &**ctx),
      //     this.print_with_env(None, a), this.print_with_env(None, b))
      // }
      match (&*this[a], &*this[b]) {
        (&Term::Var(a), &Term::Var(b)) => {
          for &(v1, v2) in ctx.iter().rev() {
            match (a == v1, b == v2) {
              (true, true) => return Ordering::Equal,
              (true, false) => return Ordering::Less,
              (false, true) => return Ordering::Greater,
              (false, false) => {}
            }
          }
          a.cmp(&b)
        }
        (Term::Const(_, _), Term::Const(_, _)) => a.cmp(&b),
        (&Term::App(s1, t1), &Term::App(s2, t2)) =>
          rec(this, ctx, s1, s2).then_with(|| rec(this, ctx, t1, t2)),
        (&Term::Lam(x1, t1), &Term::Lam(x2, t2)) => {
          this[x1].ty.cmp(&this[x2].ty).then_with(|| {
            ctx.push((x1, x2));
            (rec(this, ctx, t1, t2), ctx.pop()).0
          })
        }
        (Term::Const(_, _), _) => Ordering::Less,
        (_, Term::Const(_, _)) => Ordering::Greater,
        (Term::Var(_), _) => Ordering::Less,
        (_, Term::Var(_)) => Ordering::Greater,
        (Term::App(_, _), _) => Ordering::Less,
        (_, Term::App(_, _)) => Ordering::Greater,
      }
    }
    rec(self, &mut vec![], a, b)
  }

  fn frees(&self, free: &mut HashSet<VarId>, bound: &mut HashSet<VarId>, t: TermId) {
    // if get_print() {
    //   println!("free: {}, bound: {} = {}",
    //     self.print_with_env(None, &*free),
    //     self.print_with_env(None, &*bound), self.print_with_env(None, t))
    // }
    match *self[t] {
      Term::Var(v) => if !bound.contains(&v) { free.insert(v); }
      Term::Const(_, _) => {}
      Term::App(f, x) => { self.frees(free, bound, f); self.frees(free, bound, x) }
      Term::Lam(v, t) => {
        let old = bound.insert(v);
        self.frees(free, bound, t);
        if old { bound.remove(&v); }
      }
    }
  }

  fn alpha_eq(&self, a: TermId, b: TermId) -> bool { a == b || self.alpha_cmp(a, b).is_eq() }

  fn tyvars_in_term(&self, tm: TermId) -> Box<[TyVarId]> {
    let mut c = CollectTyVarsTerm::new(self);
    c.collect(self, tm);
    c.c.get()
  }
}

impl_index!(TermStore: Type => type_store, Var => var_store, Term => term_store);

impl HasTypeStore for TermStore {
  fn type_store(&self) -> &Store<Type> { self.tys.type_store() }
}

impl HasTermStore for TermStore {
  fn var_store(&self) -> &Store<Var> { &self.vars }

  fn term_store(&self) -> &Store<Term, TypeId> { &self.tms }
}

#[derive(Debug)]
pub struct TermArena<'a> {
  pub tys: TypeArena<'a>,
  vars: Dedup<Var>,
  tms: Dedup<Term, TypeId>,
  genvars: u32,
  conj: Option<TermId>,
  disj: Option<TermId>,
  imp: Option<TermId>,
  not: Option<TermId>,
  tru: Option<TermId>,
  fal: Option<TermId>,
}

macro_rules! get_term_cache { ($self:ident, $cache:ident, $c:ident, $ty:ident) => {
  if let Some(t) = $self.$cache { t } else {
    $self.add(Term::Const(ConstId::$c, vec![]), |tys| tys.$ty())
  }
}}

impl_index!(TermArena<'_>: Type => type_store, Var => var_store, Term => term_store);

impl HasTypeStore for TermArena<'_> {
  fn type_store(&self) -> &Store<Type> { self.tys.type_store() }
}

impl HasTermStore for TermArena<'_> {
  fn var_store(&self) -> &Store<Var> { &self.vars.store }

  fn term_store(&self) -> &Store<Term, TypeId> { &self.tms.store }
}

impl<'a> Deref for TermArena<'a> {
  type Target = TypeArena<'a>;
  fn deref(&self) -> &Self::Target { &self.tys }
}

impl DerefMut for TermArena<'_> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.tys }
}

impl<'a> TermArena<'a> {
  pub fn into_store(self) -> TermStore {
    TermStore { tys: self.tys.into_store(), vars: self.vars.store, tms: self.tms.store }
  }

  pub fn new(env: &'a Environment) -> Self {
    Self {
      tys: TypeArena::new(env),
      vars: Dedup::default(), tms: Dedup::default(), genvars: 0,
      conj: None, disj: None, imp: None, not: None, tru: None, fal: None,
    }
  }

  fn add_self(&mut self, tm: Term, mk: impl FnOnce(&mut TermArena<'a>, TermId) -> TypeId) -> TermId {
    let (n, init) = self.tms.add_default(tm);
    if !init { self.tms[n].1 = mk(self, n) }
    n
  }

  fn add(&mut self, tm: Term, mk: impl FnOnce(&mut TypeArena<'a>) -> TypeId) -> TermId {
    self.add_self(tm, |this, _| mk(&mut this.tys))
  }

  pub fn mk_var_id(&mut self, name: VarName, ty: TypeId) -> VarId {
    self.vars.add(Var {name, ty})
  }

  pub fn mk_genvar(&mut self, ty: TypeId) -> VarId {
    let name = VarName::Genvar(self.genvars);
    self.genvars += 1;
    self.vars.add(Var {name, ty})
  }

  pub fn mk_genvar_term(&mut self, ty: TypeId) -> (VarId, TermId) {
    let v = self.mk_genvar(ty);
    (v, self.tms.add_val(Term::Var(v), ty))
  }

  pub fn mk_var_term(&mut self, x: Arc<str>, ty: TypeId) -> (VarId, TermId) {
    let v = self.mk_var_id(VarName::Str(x), ty);
    (v, self.tms.add_val(Term::Var(v), ty))
  }

  pub fn mk_var(&mut self, x: VarId) -> TermId {
    self.tms.add_val(Term::Var(x), self[x].ty)
  }

  pub fn mk_const(&mut self, c: ConstId, tys: Vec<TypeId>) -> TermId {
    let ty = &self.tys.env.read()[c].ty;
    assert_eq!(tys.len(), ty.tyvars.len());
    self.add_self(Term::Const(c, tys), |this, n| {
      let tys = if let Term::Const(_, tys) = &*this.tms[n].0 { tys } else { unreachable!() };
      this.tys.inst_owned(tys, ty)
    })
  }

  pub fn mk_const_natural(&mut self, c: ConstId) -> TermId {
    let tys = self.env.read()[c].ty.tyvars.iter().map(|&v| self.mk_tyvar(v)).collect();
    self.mk_const(c, tys)
  }

  #[inline] pub fn mk_const0(&mut self, c: ConstId) -> TermId { self.mk_const(c, vec![]) }

  pub fn mk_int(&mut self, n: BigUint) -> TermId {
    let mut tm = self.mk_const0(ConstId::ZERO);
    if !n.is_zero() {
      for &i in n.to_radix_le(2).iter().rev() {
        let c = self.mk_const0(if i == 0 { ConstId::BIT0 } else { ConstId::BIT1 });
        tm = self.mk_app(c, tm);
      }
    }
    let c = self.mk_const0(ConstId::NUMERAL);
    self.mk_app(c, tm)
  }

  pub fn mk_app(&mut self, f: TermId, x: TermId) -> TermId {
    let a = self.type_of(x);
    let (a2, b) = self.dest_fun(self.type_of(f));
    if a != a2 {
      self.env.print(self, |p| {
        panic!("mk_app: type mismatch:\n{}\nis applied to\n{}",
          p.pp_type(f), p.pp_type(x))
      });
    }
    self.tms.add_val(Term::App(f, x), b)
  }

  pub fn mk_app2(&mut self, b: TermId, x: TermId, y: TermId) -> TermId {
    term!(self, A (A b x) y)
  }

  pub fn mk_lam(&mut self, x: VarId, t: TermId) -> TermId {
    let a = self[x].ty;
    let b = self.type_of(t);
    self.tms.add_val(Term::Lam(x, t), self.tys.mk_fun(a, b))
  }

  pub fn mk_binder(&mut self, b: ConstId, x: VarId, t: TermId) -> TermId {
    term!(self, A (K(b, vec![self[x].ty])) (L x t))
  }

  pub fn mk_forall(&mut self, x: VarId, t: TermId) -> TermId { self.mk_binder(ConstId::FORALL, x, t) }

  pub fn mk_exists(&mut self, x: VarId, t: TermId) -> TermId { self.mk_binder(ConstId::EXISTS, x, t) }

  pub fn mk_uexists(&mut self, x: VarId, t: TermId) -> TermId { self.mk_binder(ConstId::UEXISTS, x, t) }

  pub fn mk_select(&mut self, x: VarId, t: TermId) -> TermId { self.mk_binder(ConstId::SELECT, x, t) }

  pub fn mk_quant(&mut self, q: Quant, x: VarId, t: TermId) -> TermId {
    match q {
      Quant::Lambda => self.mk_lam(x, t),
      Quant::Forall => self.mk_forall(x, t),
      Quant::Exists => self.mk_exists(x, t),
      Quant::UExists => self.mk_uexists(x, t),
      Quant::Select => self.mk_select(x, t),
    }
  }

  pub fn mk_conj_const(&mut self) -> TermId { get_term_cache!(self, conj, CONJ, get_bool_binop) }

  pub fn mk_disj_const(&mut self) -> TermId { get_term_cache!(self, disj, DISJ, get_bool_binop) }

  pub fn mk_imp_const(&mut self) -> TermId { get_term_cache!(self, imp, IMP, get_bool_binop) }

  pub fn mk_not_const(&mut self) -> TermId { get_term_cache!(self, not, NOT, get_bool_unop) }

  pub fn mk_true(&mut self) -> TermId { get_term_cache!(self, tru, TRUE, mk_bool) }

  pub fn mk_false(&mut self) -> TermId { get_term_cache!(self, fal, FALSE, mk_bool) }

  pub fn mk_bool_lit(&mut self, b: bool) -> TermId {
    if b { self.mk_true() } else { self.mk_false() }
  }

  pub fn mk_conj(&mut self, x: TermId, y: TermId) -> TermId { term!(self, A (self.mk_conj_const()) x y) }

  pub fn mk_disj(&mut self, x: TermId, y: TermId) -> TermId { term!(self, A (self.mk_disj_const()) x y) }

  pub fn mk_imp(&mut self, x: TermId, y: TermId) -> TermId { term!(self, A (self.mk_imp_const()) x y) }

  pub fn mk_not(&mut self, x: TermId) -> TermId { term!(self, A (self.mk_not_const()) x) }

  pub fn mk_eq_const(&mut self, ty: TypeId) -> TermId {
    self.add(Term::Const(ConstId::EQ, vec![ty]), |a| ty!(a, ty -> ty -> bool))
  }

  pub fn mk_pair_const(&mut self, ty1: TypeId, ty2: TypeId) -> TermId {
    self.add(Term::Const(ConstId::PAIR, vec![ty1, ty2]), |a| ty!(a, ty1 -> ty2 -> (ty1 * ty2)))
  }

  pub fn mk_fst_const(&mut self, ty1: TypeId, ty2: TypeId) -> TermId {
    self.add(Term::Const(ConstId::FST, vec![ty1, ty2]), |a| ty!(a, (ty1 * ty2) -> ty1))
  }

  pub fn mk_snd_const(&mut self, ty1: TypeId, ty2: TypeId) -> TermId {
    self.add(Term::Const(ConstId::SND, vec![ty1, ty2]), |a| ty!(a, (ty1 * ty2) -> ty2))
  }

  pub fn mk_eq(&mut self, x: TermId, y: TermId) -> TermId {
    let ty = self.type_of(x);
    term!(self, A (self.mk_eq_const(ty)) x y)
  }

  pub fn mk_pair(&mut self, x: TermId, y: TermId) -> TermId {
    let (tyx, tyy) = (self.type_of(x), self.type_of(y));
    term!(self, A (self.mk_pair_const(tyx, tyy)) x y)
  }

  pub fn mk_fst(&mut self, x: TermId) -> TermId {
    let (tyx, tyy) = self.dest_prod(self.type_of(x));
    term!(self, A (self.mk_fst_const(tyx, tyy)) x)
  }

  pub fn mk_snd(&mut self, x: TermId) -> TermId {
    let (tyx, tyy) = self.dest_prod(self.type_of(x));
    term!(self, A (self.mk_snd_const(tyx, tyy)) x)
  }

  pub fn mk_binary(&mut self, b: Binary, x: TermId, y: TermId) -> TermId {
    match b {
      Binary::Conj => self.mk_conj(x, y),
      Binary::Disj => self.mk_disj(x, y),
      Binary::Imp => self.mk_imp(x, y),
      Binary::Eq => self.mk_eq(x, y),
      Binary::Pair => self.mk_pair(x, y),
      Binary::Bin(t) => self.mk_app2(t, x, y),
    }
  }

  fn inst_type<'b, R, S: HasTermStore + 'a>(&'b mut self, store: &'b S,
    inst: &HashMap<TyVarId, TypeId>, f: impl FnOnce(TermInstTypeX<'a, 'b, '_, S>) -> R
  ) -> R {
    (self, store).term_inst_type(inst, f)
  }

  fn import<'b, R, S: HasTermStore>(&'b mut self, store: &'b S,
    f: impl FnOnce(TermImporter<'a, 'b, '_, S>) -> R) -> R {
    let tys = &mut vec![None; store.types().len()];
    let vars = &mut vec![None; store.vars().len()];
    let tms = &mut vec![None; store.terms().len()];
    let tytr = TypeTranslator { arena: &mut (self, store), inst: &Default::default(), tys };
    f(TermImporter { tytr, tms, vars })
  }

  fn inst_term_from(&mut self, inst: &[(VarId, TermId)], tm: TermId) -> TermId {
    let mut map = InstTerm::default();
    for &(v, t) in inst { map.insert(self, v, t) }
    map.apply(self, tm)
  }

  pub fn pp<'b, T>(&'b self, env: &'b EnvRef<'b>, t: T) -> Print<'b, Self, T> {
    self.print_with_env(Some(env), t)
  }

  pub fn pp_type<'b>(&'b self, env: &'b EnvRef<'b>, t: TermId) -> impl std::fmt::Display + '_ {
    struct PP<'a, 'b>(&'b TermArena<'a>, &'b EnvRef<'b>, TermId);
    impl std::fmt::Display for PP<'_, '_> {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}",
          self.0.pp(self.1, self.2),
          self.0.pp(self.1, self.0.type_of(self.2)))
      }
    }
    PP(self, env, t)
  }
}

impl<'a, 'b> EnvPrint<'b, TermArena<'a>> {
  pub fn pp_type(&'b self, t: TermId) -> impl std::fmt::Display + 'b {
    self.arena.pp_type(self.env, t)
  }
}

trait TermArenaPair<'a>: TypeArenaPair<'a> {
  type T: HasTermStore + 'a;
  const SAME: bool;
  fn tm_dest_ref(&self) -> &TermArena<'a>;
  fn tm_dest(&mut self) -> &mut TermArena<'a>;
  fn tm_src(&self) -> &Self::T;

  fn term_inst_type<R>(&mut self, inst: &HashMap<TyVarId, TypeId>,
    f: impl FnOnce(TermInstType<'_, Self>) -> R
  ) -> R {
    let mut vec = vec![None; self.ty_src().types().len()];
    f(TermInstType { tytr: TypeTranslator { arena: self, inst, tys: &mut vec }, scope: vec![] })
  }
}

impl<'a, S: HasTypeStore> TypeArenaPair<'a> for (&mut TermArena<'a>, &S) {
  type S = S;
  #[inline] fn ty_dest_ref(&self) -> &TypeArena<'a> { self.0 }
  #[inline] fn ty_dest(&mut self) -> &mut TypeArena<'a> { self.0 }
  #[inline] fn ty_src(&self) -> &Self::S { self.1 }
}
impl<'a, S: HasTermStore + 'a> TermArenaPair<'a> for (&mut TermArena<'a>, &S) {
  type T = S;
  const SAME: bool = false;
  #[inline] fn tm_dest_ref(&self) -> &TermArena<'a> { self.0 }
  #[inline] fn tm_dest(&mut self) -> &mut TermArena<'a> { self.0 }
  #[inline] fn tm_src(&self) -> &Self::T { self.1 }
}

impl<'a> TypeArenaPair<'a> for TermArena<'a> {
  type S = TypeArena<'a>;
  #[inline] fn ty_dest_ref(&self) -> &TypeArena<'a> { self }
  #[inline] fn ty_dest(&mut self) -> &mut TypeArena<'a> { self }
  #[inline] fn ty_src(&self) -> &Self::S { self }
}
impl<'a> TermArenaPair<'a> for TermArena<'a> {
  type T = Self;
  const SAME: bool = true;
  #[inline] fn tm_dest_ref(&self) -> &TermArena<'a> { self }
  #[inline] fn tm_dest(&mut self) -> &mut TermArena<'a> { self }
  #[inline] fn tm_src(&self) -> &Self::T { self }
}

impl<'a> TypeArenaPair<'a> for ProofArena<'a> {
  type S = TypeArena<'a>;
  #[inline] fn ty_dest_ref(&self) -> &TypeArena<'a> { self }
  #[inline] fn ty_dest(&mut self) -> &mut TypeArena<'a> { self }
  #[inline] fn ty_src(&self) -> &Self::S { self }
}
impl<'a> TermArenaPair<'a> for ProofArena<'a> {
  type T = Self;
  const SAME: bool = true;
  #[inline] fn tm_dest_ref(&self) -> &TermArena<'a> { self }
  #[inline] fn tm_dest(&mut self) -> &mut TermArena<'a> { self }
  #[inline] fn tm_src(&self) -> &Self::T { self }
}

trait InstType<'a: 'b, 'b>: 'b {
  type S: TermArenaPair<'a> + 'b;
  type Scope;
  fn as_type(&self) -> &TypeTranslator<'b, Self::S>;
  fn as_type_mut(&mut self) -> &mut TypeTranslator<'b, Self::S>;
  #[inline] fn dest<'c>(&'c mut self) -> &'c mut TermArena<'a> where 'b: 'c {
    self.as_type_mut().arena.tm_dest()
  }
  #[inline] fn dest_ref<'c>(&'c self) -> &'c TermArena<'a> where 'b: 'c {
    self.as_type().arena.tm_dest_ref()
  }
  #[inline] fn src<'c>(&'c self) -> &'c <Self::S as TermArenaPair<'a>>::T where 'b: 'c {
    self.as_type().arena.tm_src()
  }
  #[inline] fn var_mut(&mut self, _: VarId) -> Option<&mut Option<VarId>> { None }
  #[inline] fn tm_mut(&mut self, _: TermId) -> Option<&mut Option<TermId>> { None }

  fn enter_scope(&mut self, from: VarId, to: VarId) -> Self::Scope;
  fn leave_scope(&mut self, _: Self::Scope) {}
  fn is_binder(&mut self, _: VarId) -> Option<VarId> { None }

  #[inline] fn tr_type(&mut self, ty: TypeId) -> TypeId { self.as_type_mut().tr(ty) }

  fn try_tr_var(&mut self, check: bool, v: VarId) -> Result<VarId, VarId> {
    if let Some(i) = self.var_mut(v).and_then(|i| *i) { return Ok(i) }
    let Var {ref name, ty} = *self.src()[v];
    let name = name.clone();
    let ty2 = self.tr_type(ty);
    let n = if Self::S::SAME && ty2 == ty { v } else { self.dest().mk_var_id(name, ty2) };
    if check && !self.is_binder(n).map_or(true, |v2| v2 == v) { return Err(n) }
    if let Some(var) = self.var_mut(v) { *var = Some(n) }
    Ok(n)
  }

  fn tr_var(&mut self, v: VarId) -> VarId { self.try_tr_var(false, v).unwrap() }

  fn try_tr_term(&mut self, tm: TermId) -> Result<TermId, VarId> {
    if let Some(i) = self.tm_mut(tm).and_then(|i| *i) { return Ok(i) }
    let n = match *self.src()[tm].clone() {
      Term::Var(x) => term!(self.dest(), V(self.try_tr_var(true, x)?)),
      Term::Const(c, ref tyargs) => {
        let trty = self.as_type_mut();
        term!(self.dest(), K(c, tyargs.iter().map(|&ty| trty.tr(ty)).collect()))
      }
      Term::App(f, x) => term!(self.dest(), A (self.try_tr_term(f)?) (self.try_tr_term(x)?)),
      Term::Lam(x, t) => {
        let y = self.tr_var(x);
        let sc = self.enter_scope(x, y);
        let t2 = self.try_tr_term(t);
        self.leave_scope(sc);
        match t2 {
          Ok(t2) => {
            if Self::S::SAME && x == y && t == t2 { return Ok(tm) }
            term!(self.dest(), L y t2)
          }
          Err(v) => {
            if v != y { return Err(v) }
            let ty = self.dest()[x].ty;
            let (z, zt) = self.dest().mk_genvar_term(ty);
            let tm = term!(self.dest(), L z {self.dest().inst_term_from(&[(x, zt)], t)});
            self.try_tr_term(tm)?
          }
        }
      }
    };
    if let Some(tm) = self.tm_mut(tm) { *tm = Some(n) }
    Ok(n)
  }

  fn tr_term(&mut self, tm: TermId) -> TermId {
    self.try_tr_term(tm).expect("in empty context")
  }
}

type TermTranslator<'a, 'b, 'c, S> = TypeTranslator<'c, (&'b mut TermArena<'a>, &'b S)>;
type TermInstTypeX<'a, 'b, 'c, S> = TermInstType<'c, (&'b mut TermArena<'a>, &'b S)>;

pub struct TermInstType<'b, S> {
  tytr: TypeTranslator<'b, S>,
  scope: Vec<(VarId, VarId)>,
}

pub struct TermImporter<'a, 'b, 'c, S> {
  tytr: TermTranslator<'a, 'b, 'c, S>,
  vars: &'c mut [Option<VarId>],
  tms: &'c mut [Option<TermId>],
}

impl<'a: 'b, 'b, S: TermArenaPair<'a>> InstType<'a, 'b> for TermInstType<'b, S> {
  type S = S;
  type Scope = ();
  #[inline] fn as_type(&self) -> &TypeTranslator<'b, S> { &self.tytr }
  #[inline] fn as_type_mut(&mut self) -> &mut TypeTranslator<'b, S> { &mut self.tytr }
  fn enter_scope(&mut self, from: VarId, to: VarId) { self.scope.push((from, to)) }
  fn leave_scope(&mut self, (): ()) { self.scope.pop(); }
  fn is_binder(&mut self, x: VarId) -> Option<VarId> {
    self.scope.iter().rev().find(|p| p.1 == x).map(|p| p.0)
  }
}

impl<'a, 'b, 'c, S: HasTermStore + 'a> InstType<'a, 'c> for TermImporter<'a, 'b, 'c, S> {
  type S = (&'b mut TermArena<'a>, &'b S);
  type Scope = ();
  #[inline] fn as_type(&self) -> &TypeTranslator<'c, Self::S> { &self.tytr }
  #[inline] fn as_type_mut(&mut self) -> &mut TypeTranslator<'c, Self::S> { &mut self.tytr }
  #[inline] fn var_mut(&mut self, i: VarId) -> Option<&mut Option<VarId>> {
    Some(&mut self.vars[i.into_usize()])
  }
  #[inline] fn tm_mut(&mut self, i: TermId) -> Option<&mut Option<TermId>> {
    Some(&mut self.tms[i.into_usize()])
  }
  #[inline] fn enter_scope(&mut self, _: VarId, _: VarId) {}
}

#[derive(Debug, Default)]
pub struct InstTerm {
  inst: HashMap<VarId, TermId>,
  fvars: HashSet<VarId>,
}

impl InstTerm {
  pub fn inst(&self) -> &HashMap<VarId, TermId> { &self.inst }
  pub fn fvars(&self) -> &HashSet<VarId> { &self.fvars }

  fn insert(&mut self, arena: &impl HasTermStore, v: VarId, t: TermId) {
    if let Entry::Vacant(e) = self.inst.entry(v) {
      e.insert(t);
      arena.frees(&mut self.fvars, &mut HashSet::new(), t)
    }
  }

  fn apply_simple(&mut self, arena: &mut TermArena<'_>, tm: TermId) -> TermId {
    match *arena[tm].clone() {
      Term::Var(x) => self.inst.get(&x).copied().unwrap_or(tm),
      Term::Const(_, _) => tm,
      Term::App(f, x) =>
        term!(arena, A {self.apply_simple(arena, f)} {self.apply_simple(arena, x)}),
      Term::Lam(x, e) => if self.fvars.contains(&x) {
        let (y, yt) = arena.mk_genvar_term(arena[x].ty);
        let old = self.inst.insert(x, yt);
        let r = term!(arena, L y {self.apply_simple(arena, e)});
        if let Some(old) = old { self.inst.insert(x, old); } else { self.inst.remove(&x); }
        r
      } else if let Some(old) = self.inst.remove(&x) {
        let r = term!(arena, L x {self.apply(arena, e)});
        self.inst.insert(x, old);
        r
      } else {
        term!(arena, L x {self.apply_simple(arena, e)})
      }
    }
  }

  fn apply(&mut self, arena: &mut TermArena<'_>, tm: TermId) -> TermId {
    if self.inst.is_empty() { tm } else { self.apply_simple(arena, tm) }
  }
}

struct CollectTyVarsType {
  vars: Vec<TyVarId>,
  visited: BitBox,
}

impl CollectTyVarsType {
  fn new(arena: &(impl HasTypeStore + ?Sized)) -> Self {
    Self { vars: vec![], visited: bitbox![0; arena.types().len()] }
  }

  fn collect(&mut self, arena: &(impl HasTypeStore + ?Sized), ty: TypeId) {
    if self.visited[ty.into_usize()] { return }
    match *arena[ty] {
      Type::TyVar(v) => self.vars.push(v),
      Type::Tyop(_, ref args) => for &ty in args { self.collect(arena, ty) }
    }
    self.visited.set(ty.into_usize(), true)
  }

  fn get(self) -> Box<[TyVarId]> { self.vars.into() }
}

struct CollectTyVarsTerm {
  pub c: CollectTyVarsType,
  visited: BitBox,
}

impl CollectTyVarsTerm {
  fn new(arena: &(impl HasTermStore + ?Sized)) -> Self {
    Self {
      c: CollectTyVarsType::new(arena),
      visited: bitbox![0; arena.terms().len()]
    }
  }

  fn collect(&mut self, arena: &(impl HasTermStore + ?Sized), tm: TermId) {
    if self.visited[tm.into_usize()] { return }
    let t = &arena.term_store()[tm];
    match *t.0 {
      Term::Var(_) | Term::Const(_, _) => self.c.collect(arena, t.1),
      Term::App(a, b) => { self.collect(arena, a); self.collect(arena, b) }
      Term::Lam(v, t) => {
        self.c.collect(arena, arena[v].ty);
        self.collect(arena, t)
      }
    }
    self.visited.set(tm.into_usize(), true)
  }
}

#[derive(Debug)]
pub enum ProofTrace {
  Fetch(ThmId, Box<[TypeId]>),
  AddAsm(TermId, ProofId),
  Alpha,
  AlphaLink(ProofId),
  Assume,
  Beta,
  CContr(ProofId),
  Choose(TermId, ProofId, ProofId),
  Conj(ProofId, ProofId),
  Conj1(ProofId),
  Conj2(ProofId),
  Contr(ProofId),
  DeductAntisym(ProofId, ProofId),
  Disch(ProofId),
  Disj1(ProofId),
  Disj2(ProofId),
  DisjCases(ProofId, ProofId, ProofId),
  EqfElim(ProofId),
  EqfIntro(ProofId),
  EqImp1(ProofId),
  EqImp2(ProofId),
  EqMp(ProofId, ProofId),
  EqtElim(ProofId),
  EqtIntro(ProofId),
  Eta,
  Exists(TermId, ProofId),
  Gen(ProofId),
  ImpAntisym(ProofId, ProofId),
  ImpTrans(ProofId, ProofId),
  Inst(InstTerm, ProofId),
  InstType(HashMap<TyVarId, TypeId>, ProofId),
  Mp(ProofId, ProofId),
  NotElim(ProofId),
  NotIntro(ProofId),
  ProveAsm(ProofId, ProofId),
  Refl,
  SelectRule(ProofId),
  Spec(TermId, ProofId),
  SubsConv(Box<[ProofId]>),
  Subs(Box<[ProofId]>, ProofId),
  SubstConv(Vec<(VarId, ProofId)>),
  Subst(Vec<(VarId, ProofId)>, ProofId),
  Sym(ProofId),
  SymConv,
  Trans(ProofId, ProofId),
  Undisch(ProofId),
  App(ProofId, ProofId),
  App1(ProofId),
  App2(ProofId),
  Bin(ProofId, ProofId),
  Bin1(ProofId),
  Lam(ProofId),
  Binder(ProofId),
  NumConv,
  NewTypeBij1(TyopId),
  NewTypeBij2(TyopId),
  NewBasicDef(ConstId),
  NewSimpleDef(ConstId),
  NewDef(ConstId),
  NewSpec(SpecId),
  Extern(mm0::ThmId),
}

#[derive(Default, Debug, Hash, PartialEq, Eq)]
pub struct Hyps(Box<[TermId]>);

impl Deref for Hyps {
  type Target = [TermId];
  fn deref(&self) -> &Self::Target { &*self.0 }
}

impl Hyps {
  fn contains(&self, arena: &impl HasTermStore, tm: TermId) -> bool {
    self.0.binary_search_by(|&a| arena.alpha_cmp(a, tm)).is_ok()
  }

  fn is_subset(&self, arena: &impl HasTermStore, other: &Self) -> bool {
    self.0.iter().all(|&a| other.contains(arena, a))
  }

  fn union(&self, arena: &impl HasTermStore, other: &Self) -> Self {
    let mut it1 = self.0.iter(); let mut peek1 = it1.next();
    let mut it2 = other.0.iter(); let mut peek2 = it2.next();
    let mut out = vec![];
    loop {
      let a = if let Some(&a) = peek1 { a } else {
        if let Some(&t) = peek2 { out.push(t) }
        out.extend_from_slice(it2.as_slice());
        break
      };
      let b = if let Some(&b) = peek2 { b } else {
        if let Some(&t) = peek1 { out.push(t) }
        out.extend_from_slice(it1.as_slice());
        break
      };
      match arena.alpha_cmp(a, b) {
        Ordering::Less => { out.push(a); peek1 = it1.next(); }
        Ordering::Equal => { out.push(a); peek1 = it1.next(); peek2 = it2.next(); }
        Ordering::Greater => { out.push(b); peek2 = it2.next(); }
      }
    }
    Self(out.into())
  }

  fn insert(&self, arena: &impl HasTermStore, tm: TermId) -> Option<Self> {
    let i = self.0.binary_search_by(|&a| arena.alpha_cmp(a, tm)).err()?;
    let mut out = Vec::with_capacity(self.0.len() + 1);
    out.extend_from_slice(&self.0[..i]);
    out.push(tm);
    out.extend_from_slice(&self.0[i..]);
    Some(Self(out.into()))
  }

  fn remove(&self, arena: &impl HasTermStore, tm: TermId) -> Option<Self> {
    let i = self.0.binary_search_by(|&a| arena.alpha_cmp(a, tm)).ok()?;
    let mut out = Vec::with_capacity(self.0.len() - 1);
    out.extend_from_slice(&self.0[..i]);
    out.extend_from_slice(&self.0[i+1..]);
    Some(Self(out.into()))
  }

  fn from_vec(arena: &impl HasTermStore, mut vec: Vec<TermId>) -> Self {
    vec.sort_unstable_by(|&a, &b| arena.alpha_cmp(a, b));
    vec.dedup_by(|&mut a, &mut b| arena.alpha_eq(a, b));
    Self(vec.into())
  }

  fn one(tm: TermId) -> Self { Self(Box::new([tm])) }
}

#[derive(Debug)]
struct UnionHyps(Arc<Hyps>);

impl UnionHyps {
  fn new(arena: &ProofArena<'_>) -> Self { Self(arena[HypsId::EMPTY].clone()) }

  fn insert(&mut self, arena: &impl HasProofStore, hyps: HypsId) {
    if hyps == HypsId::EMPTY { return }
    let other = &arena[hyps];
    if self.0 .0.is_empty() { return self.0 = other.clone() }
    if other.is_subset(arena, &self.0) { return }
    if self.0.is_subset(arena, other) { return self.0 = other.clone() }
    self.0 = Arc::new(self.0.union(arena, other));
  }

  fn finish(self, arena: &mut ProofArena<'_>) -> HypsId { arena.hyps.add_inner(self.0, ()).0 }
}

#[derive(Debug, Default, Hash, PartialEq, Eq)]
pub struct Proof {
  hyps: HypsId,
  concl: TermId,
}

impl Proof {
  #[inline] pub fn hyps(&self) -> HypsId { self.hyps }
  #[inline] pub fn concl(&self) -> TermId { self.concl }
}

pub struct ProofStore {
  pub tms: TermStore,
  pub hyps: Store<Hyps>,
  pub pfs: Store<Proof, ProofTrace>,
}

pub trait HasProofStore:
  HasTermStore +
  Index<HypsId, Output=Arc<Hyps>> +
  Index<ProofId, Output=Arc<Proof>>
{
  fn hyps_store(&self) -> &Store<Hyps>;
  fn proof_store(&self) -> &Store<Proof, ProofTrace>;

  fn hyps(&self) -> &[(Arc<Hyps>, ())] { &self.hyps_store().0 }

  fn proofs(&self) -> &[(Arc<Proof>, ProofTrace)] { &self.proof_store().0 }

  fn trace_of(&self, th: ProofId) -> &ProofTrace { &self.proof_store()[th].1 }
}

impl_index!(ProofStore: Type => type_store, Var => var_store, Term => term_store,
  Hyps => hyps_store, Proof => proof_store);

impl HasTypeStore for ProofStore {
  fn type_store(&self) -> &Store<Type> { self.tms.type_store() }
}

impl HasTermStore for ProofStore {
  fn var_store(&self) -> &Store<Var> { self.tms.var_store() }

  fn term_store(&self) -> &Store<Term, TypeId> { self.tms.term_store() }
}

impl HasProofStore for ProofStore {
  fn hyps_store(&self) -> &Store<Hyps> { &self.hyps }

  fn proof_store(&self) -> &Store<Proof, ProofTrace> { &self.pfs }
}

#[derive(Debug)]
pub struct ProofArena<'a> {
  pub tms: TermArena<'a>,
  hyps: Dedup<Hyps>,
  pfs: Dedup<Proof, ProofTrace>,
}

impl<'a> Deref for ProofArena<'a> {
  type Target = TermArena<'a>;
  fn deref(&self) -> &Self::Target { &self.tms }
}

impl DerefMut for ProofArena<'_> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.tms }
}

impl_index!(ProofArena<'_>: Type => type_store, Var => var_store, Term => term_store,
  Hyps => hyps_store, Proof => proof_store);

impl HasTypeStore for ProofArena<'_> {
  fn type_store(&self) -> &Store<Type> { self.tms.type_store() }
}

impl HasTermStore for ProofArena<'_> {
  fn var_store(&self) -> &Store<Var> { self.tms.var_store() }

  fn term_store(&self) -> &Store<Term, TypeId> { self.tms.term_store() }
}

impl HasProofStore for ProofArena<'_> {
  fn hyps_store(&self) -> &Store<Hyps> { &self.hyps.store }

  fn proof_store(&self) -> &Store<Proof, ProofTrace> { &self.pfs.store }
}

impl HypsId { const EMPTY: Self = Self(0); }

impl<'a> ProofArena<'a> {
  pub fn into_store(self) -> ProofStore {
    ProofStore { tms: self.tms.into_store(), hyps: self.hyps.store, pfs: self.pfs.store }
  }

  fn add(&mut self, hyps: HypsId, concl: TermId, src: ProofTrace) -> ProofId {
    self.pfs.add_val(Proof {hyps, concl}, src)
  }

  fn add0(&mut self, concl: TermId, src: ProofTrace) -> ProofId {
    self.add(HypsId::EMPTY, concl, src)
  }

  pub fn new(env: &'a Environment) -> Self {
    let mut hyps = Dedup::default();
    hyps.add(Hyps::default());
    Self { tms: TermArena::new(env), pfs: Dedup::default(), hyps }
  }

  fn union_hyps(&mut self, a: HypsId, b: HypsId) -> HypsId {
    if a == b || b == HypsId::EMPTY { return a }
    if a == HypsId::EMPTY { return b }
    let hyps1 = &self[a];
    let hyps2 = &self[b];
    if hyps1.is_subset(&self.tms, hyps2) { return b }
    if hyps2.is_subset(&self.tms, hyps1) { return a }
    let hyps = hyps1.union(&self.tms, hyps2);
    self.hyps.add(hyps)
  }

  fn insert_hyp(&mut self, a: HypsId, tm: TermId) -> HypsId {
    if let Some(hyps) = self[a].insert(&self.tms, tm) { self.hyps.add(hyps) } else { a }
  }

  fn remove_hyp(&mut self, a: HypsId, tm: TermId) -> HypsId {
    if let Some(hyps) = self[a].remove(&self.tms, tm) { self.hyps.add(hyps) } else { a }
  }

  fn hyps_from_vec(&mut self, vec: Vec<TermId>) -> HypsId {
    self.hyps.add(Hyps::from_vec(&self.tms, vec))
  }

  pub fn pp<'b, T>(&'b self, env: &'b EnvRef<'b>, t: T) -> Print<'b, Self, T> {
    self.print_with_env(Some(env), t)
  }

  pub fn extern_axiom(&mut self, hyps: Vec<TermId>, concl: TermId, src: mm0::ThmId) -> ProofId {
    let hyps = self.hyps_from_vec(hyps);
    self.add(hyps, concl, ProofTrace::Extern(src))
  }

  pub fn fetch(&mut self, th: ThmId, tys: Vec<TypeId>) -> ProofId {
    let d = &self.env.read()[th].clone();
    let (inst, tys) = if tys.is_empty() {
      (Default::default(), d.tyvars.iter().map(|&n| self.mk_tyvar(n)).collect())
    } else {
      assert_eq!(d.tyvars.len(), tys.len());
      (d.tyvars.iter().copied().zip(tys.iter().copied()).collect(), tys.into())
    };
    let (hyps, concl) = self.tms.inst_type(&d.arena, &inst, |mut tr| (
      d.hyps.iter().map(|&tm| tr.tr_term(tm)).collect(),
      tr.tr_term(d.concl)
    ));
    let hyps = self.hyps_from_vec(hyps);
    thm!(self, add(Fetch(th, tys), hyps, concl))
  }

  pub fn add_asm(&mut self, tm: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    if let Some(hyps) = self[hyps].insert(&self.tms, tm) {
      thm!(self, add(AddAsm(tm, th), self.hyps.add(hyps), concl))
    } else { th }
  }

  pub fn alpha(&mut self, tm1: TermId, tm2: TermId) -> ProofId {
    assert!(self.alpha_eq(tm1, tm2));
    thm!(self, add0(Alpha, tm1 = tm2))
  }

  pub fn alpha_link0(&mut self, th: ProofId, concl2: TermId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    if !self.alpha_eq(concl, concl2) {
      self.env.print_always(&self.tms, |p| {
        panic!("alpha_link0: mismatch\n  have: {}\n  want: {}", p.pp(concl), p.pp(concl2));
      })
    }
    assert_eq!(hyps, HypsId::EMPTY);
    thm!(self, add0(AlphaLink(th), concl2))
  }

  pub fn alpha_conv(&mut self, tm1: TermId, tm2: TermId) -> ProofId {
    let y = self.dest_var(tm1);
    let (x, t) = self.dest_lam(tm2);
    let t2 = self.inst_term_from(&[(x, tm1)], t);
    thm!(self, add0(Alpha, tm2 = (L y t2)))
  }

  pub fn assume(&mut self, tm: TermId) -> ProofId {
    assert!(self.is_boolean(tm));
    let hyps = self.hyps.add(Hyps::one(tm));
    thm!(self, add(Assume, hyps, tm))
  }

  pub fn beta(&mut self, tm: TermId) -> ProofId {
    let (t, s) = self.dest_app(tm);
    let (x, t) = self.dest_lam(t);
    let t2 = self.inst_term_from(&[(x, s)], t);
    thm!(self, add0(Beta, tm = t2))
  }

  pub fn ccontr(&mut self, tm: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    self.dest_const(ConstId::FALSE, concl);
    let neg = self.mk_not(tm);
    thm!(self, add(CContr(th), self.remove_hyp(hyps, neg), tm))
  }

  pub fn choose(&mut self, tm: TermId, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: concl1} = *self[th1];
    let Proof {hyps: h2, concl: concl2} = *self[th2];
    let (x, p) = self.dest_exists(concl1);
    let p2 = self.inst_term_from(&[(x, tm)], p);
    let h2 = self.remove_hyp(h2, p2);
    thm!(self, add(Choose(tm, th1, th2), self.union_hyps(h1, h2), concl2))
  }

  pub fn conj(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: concl1} = *self[th1];
    let Proof {hyps: h2, concl: concl2} = *self[th2];
    thm!(self, add(Conj(th1, th2), self.union_hyps(h1, h2), {self.mk_conj(concl1, concl2)}))
  }

  pub fn conj1(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (a, _) = self.dest_conj(concl);
    thm!(self, add(Conj1(th), hyps, a))
  }

  pub fn conj2(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (_, b) = self.dest_conj(concl);
    thm!(self, add(Conj2(th), hyps, b))
  }

  pub fn contr(&mut self, tm: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    self.dest_const(ConstId::FALSE, concl);
    assert!(self.is_boolean(tm));
    thm!(self, add(Contr(th), hyps, tm))
  }

  pub fn deduct_antisym(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: p} = *self[th1];
    let Proof {hyps: h2, concl: q} = *self[th2];
    let h1 = self.remove_hyp(h1, q);
    let h2 = self.remove_hyp(h2, p);
    thm!(self, add(DeductAntisym(th1, th2), self.union_hyps(h1, h2), p = q))
  }

  pub fn disch(&mut self, p: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl: q} = *self[th];
    thm!(self, add(Disch(th), self.remove_hyp(hyps, p), p => q))
  }

  pub fn disj1(&mut self, th: ProofId, q: TermId) -> ProofId {
    let Proof {hyps, concl: p} = *self[th];
    thm!(self, add(Disj1(th), hyps, {self.mk_disj(p, q)}))
  }

  pub fn disj2(&mut self, p: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl: q} = *self[th];
    thm!(self, add(Disj2(th), hyps, {self.mk_disj(p, q)}))
  }

  pub fn disj_cases(&mut self, th1: ProofId, th2: ProofId, th3: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th1];
    let (p, q) = self.dest_disj(concl);
    let Proof {hyps: h1, concl: r1} = *self[th2];
    let Proof {hyps: h2, concl: r2} = *self[th3];
    if !self.alpha_eq(r1, r2) {
      self.env.print_always(&self.tms, |p| {
        panic!("disj_cases: mismatch\n  left: {}\n right: {}", p.pp(r1), p.pp(r2));
      })
    }
    let h1 = self.remove_hyp(h1, p);
    let h2 = self.remove_hyp(h2, q);
    let h12 = self.union_hyps(h1, h2);
    thm!(self, add(DisjCases(th1, th2, th3), self.union_hyps(hyps, h12), r1))
  }

  pub fn eqf_elim(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, fal) = self.dest_eq(concl);
    self.dest_const(ConstId::FALSE, fal);
    thm!(self, add(EqfElim(th), hyps, {self.mk_not(p)}))
  }

  pub fn eqf_intro(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    thm!(self, add(EqfIntro(th), hyps, {self.dest_not(concl)} = {self.mk_false()}))
  }

  pub fn eq_imp1(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, q) = self.dest_eq(concl);
    thm!(self, add(EqImp1(th), hyps, p => q))
  }

  pub fn eq_imp2(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, q) = self.dest_eq(concl);
    thm!(self, add(EqImp2(th), hyps, q => p))
  }

  pub fn eq_mp(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: concl1} = *self[th1];
    let Proof {hyps: h2, concl: concl2} = *self[th2];
    let (p, q) = self.dest_eq(concl1);
    if !self.alpha_eq(p, concl2) {
      self.env.print_always(&self.tms, |pp| {
        panic!("eq_mp: mismatch\n  left: {}\n right: {}", pp.pp(p), pp.pp(concl2))
      })
    }
    thm!(self, add(EqMp(th1, th2), self.union_hyps(h1, h2), q))
  }

  pub fn eqt_elim(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, tru) = self.dest_eq(concl);
    self.dest_const(ConstId::TRUE, tru);
    thm!(self, add(EqtElim(th), hyps, p))
  }

  pub fn eqt_intro(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    thm!(self, add(EqtIntro(th), hyps, concl = {self.mk_true()}))
  }

  pub fn eta(&mut self, tm: TermId) -> ProofId {
    let (x, f) = self.dest_lam(tm);
    let (f, x2) = self.dest_app(f);
    assert_eq!(x, self.dest_var(x2));
    thm!(self, add0(Eta, tm = f))
  }

  pub fn exists(&mut self, tm: TermId, t: TermId, th: ProofId) -> ProofId {
    let (x, p) = self.dest_exists(tm);
    let Proof {hyps, concl} = *self[th];
    let p2 = self.inst_term_from(&[(x, t)], p);
    if !self.alpha_eq(p2, concl) {
      self.env.print_always(&self.tms, |pp| {
        panic!("exists: mismatch\n  left: {}\n right: {}", pp.pp(p2), pp.pp(concl))
      })
    }
    thm!(self, add(Exists(t, th), hyps, tm))
  }

  pub fn gen(&mut self, x: VarId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    thm!(self, add(Gen(th), hyps, {self.mk_forall(x, concl)}))
  }

  pub fn imp_antisym(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: concl1} = *self[th1];
    let Proof {hyps: h2, concl: concl2} = *self[th2];
    let (p, q) = self.dest_imp(concl1);
    let (q2, p2) = self.dest_imp(concl2);
    if !self.alpha_eq(p, p2) || !self.alpha_eq(q, q2) {
      self.env.print_always(&self.tms, |pp| {
        panic!("imp_antisymm: mismatch\n  left: {}\n right: {}",
          pp.pp(concl1), pp.pp(concl2))
      })
    }
    thm!(self, add(ImpAntisym(th1, th2), self.union_hyps(h1, h2), p = q))
  }

  pub fn imp_trans(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: concl1} = *self[th1];
    let Proof {hyps: h2, concl: concl2} = *self[th2];
    let (p, q) = self.dest_imp(concl1);
    let (q2, r) = self.dest_imp(concl2);
    if !self.alpha_eq(q, q2) {
      self.env.print_always(&self.tms, |pp| {
        panic!("imp_trans: mismatch\n  left: {}\n right: {}",
          pp.pp(concl1), pp.pp(concl2))
      })
    }
    thm!(self, add(ImpTrans(th1, th2), self.union_hyps(h1, h2), p => r))
  }

  pub fn inst(&mut self, inst: &[(VarId, TermId)], th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let mut map = InstTerm::default();
    for &(v, t) in inst { map.insert(self, v, t) }
    let hyps = if hyps == HypsId::EMPTY { hyps } else {
      let hyps = self[hyps].clone().0.iter().map(|&h| map.apply(self, h)).collect();
      self.hyps_from_vec(hyps)
    };
    let concl = map.apply(self, concl);
    thm!(self, add(Inst(map, th), hyps, concl))
  }

  pub fn inst_type_from(&mut self, inst: &[(TyVarId, TypeId)], th: ProofId) -> ProofId {
    let mut map = HashMap::new();
    for &(v, t) in inst { map.entry(v).or_insert(t); }
    self.inst_type(map, th)
  }

  pub fn inst_type(&mut self, inst: HashMap<TyVarId, TypeId>, th: ProofId) -> ProofId {
    // self.env.print_always(self, |p| println!("inst_type {} {}", p.pp(&inst), p.pp(th)));
    let Proof {hyps, concl} = *self[th];
    let (hyps, concl) = TermArenaPair::term_inst_type(self, &inst, |mut tr| (
      tr.tytr.arena.hyps_store()[hyps].0.clone().iter().map(|&h| tr.tr_term(h)).collect(),
      tr.tr_term(concl)
    ));
    thm!(self, add(InstType(inst, th), self.hyps_from_vec(hyps), concl))
  }

  pub fn mp(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: concl1} = *self[th1];
    let Proof {hyps: h2, concl: concl2} = *self[th2];
    let (p, q) = self.dest_imp(concl1);
    if !self.alpha_eq(p, concl2) {
      self.env.print_always(&self.tms, |pp| {
        panic!("mp: mismatch\n  left: {}\n right: {}", pp.pp(p), pp.pp(concl2));
      })
    }
    thm!(self, add(Mp(th1, th2), self.union_hyps(h1, h2), q))
  }

  pub fn not_elim(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    thm!(self, add(NotElim(th), hyps, {self.dest_not(concl)} => {self.mk_false()}))
  }

  pub fn not_intro(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, fal) = self.dest_imp(concl);
    self.dest_const(ConstId::FALSE, fal);
    thm!(self, add(NotIntro(th), hyps, {self.mk_not(p)}))
  }

  pub fn prove_asm(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: p} = *self[th1];
    let Proof {hyps: h2, concl: q} = *self[th2];
    let h2 = self.remove_hyp(h2, p);
    thm!(self, add(ProveAsm(th1, th2), self.union_hyps(h1, h2), q))
  }

  pub fn refl(&mut self, tm: TermId) -> ProofId {
    thm!(self, add0(Refl, tm = tm))
  }

  pub fn select_rule(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (x, p) = self.dest_exists(concl);
    let sel = self.mk_select(x, p);
    thm!(self, add(SelectRule(th), hyps, self.inst_term_from(&[(x, sel)], p)))
  }

  pub fn spec(&mut self, tm: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (x, p) = self.dest_forall(concl);
    thm!(self, add(Spec(tm, th), hyps, self.inst_term_from(&[(x, tm)], p)))
  }

  pub fn subs_conv(&mut self, inst: SubsInst, a: TermId) -> ProofId {
    let b = inst.apply(self, a);
    if a == b { return self.refl(a) }
    thm!(self, add(SubsConv(inst.ths.into()), inst.hyps.finish(self), a = b))
  }

  pub fn subs(&mut self, inst: SubsInst, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let b = inst.apply(self, concl);
    if concl == b { return th }
    let hyps1 = inst.hyps.finish(self);
    thm!(self, add(Subs(inst.ths.into(), th), self.union_hyps(hyps1, hyps), b))
  }

  fn subst_core(&mut self, vths: &[(VarId, ProofId)], tm: TermId) -> (UnionHyps, TermId, TermId) {
    let (mut map1, mut map2) = (InstTerm::default(), InstTerm::default());
    let mut hyps = UnionHyps::new(self);
    for &(v, th) in vths {
      let Proof {hyps: h, concl} = *self[th];
      let (a, b) = self.dest_eq(concl);
      map1.insert(self, v, a);
      map2.insert(self, v, b);
      hyps.insert(self, h)
    }
    (hyps, map1.apply(self, tm), map2.apply(self, tm))
  }

  pub fn subst_conv(&mut self, vths: Vec<(VarId, ProofId)>, tmp: TermId, tm: TermId) -> ProofId {
    let (hyps, lhs, rhs) = self.subst_core(&vths, tmp);
    assert!(self.alpha_eq(lhs, tm));
    thm!(self, add(SubstConv(vths), hyps.finish(self), tm = rhs))
  }

  pub fn subst(&mut self, vths: Vec<(VarId, ProofId)>, tmp: TermId, th: ProofId) -> ProofId {
    let (mut u, lhs, rhs) = self.subst_core(&vths, tmp);
    let Proof {hyps, concl} = *self[th];
    u.insert(self, hyps);
    assert!(self.alpha_eq(lhs, concl));
    thm!(self, add(Subst(vths, th), u.finish(self), rhs))
  }

  pub fn sym(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (t1, t2) = self.dest_eq(concl);
    thm!(self, add(Sym(th), hyps, t2 = t1))
  }

  pub fn sym_conv(&mut self, tm: TermId) -> ProofId {
    let (t1, t2) = self.dest_eq(tm);
    thm!(self, add0(SymConv, (t1 = t2) = (t2 = t1)))
  }

  pub fn trans(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: concl1} = *self[th1];
    let Proof {hyps: h2, concl: concl2} = *self[th2];
    let (a, b) = self.dest_eq(concl1);
    let (b2, c) = self.dest_eq(concl2);
    if !self.alpha_eq(b, b2) {
      self.env.print_always(&self.tms, |p| {
        panic!("trans: mismatch\n  left: {}\n right: {}", p.pp(concl1), p.pp(concl2))
      })
    }
    thm!(self, add(Trans(th1, th2), self.union_hyps(h1, h2), a = c))
  }

  pub fn undisch(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, q) = self.dest_imp(concl);
    thm!(self, add(Undisch(th), self.insert_hyp(hyps, p), q))
  }

  #[inline] fn mk_eq_fn1(&mut self, src: ProofTrace, th: ProofId,
    mut f: impl FnMut(&mut Self, TermId) -> TermId
  ) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (l, r) = self.dest_eq(concl);
    thm!(self, add(src, hyps, {f(self, l)} = {f(self, r)}))
  }

  #[inline] fn mk_eq_fn2(&mut self, src: ProofTrace, th1: ProofId, th2: ProofId,
    mut f: impl FnMut(&mut Self, TermId, TermId) -> TermId
  ) -> ProofId {
    let Proof {hyps: h1, concl: th1} = *self[th1];
    let Proof {hyps: h2, concl: th2} = *self[th2];
    let (l1, r1) = self.dest_eq(th1);
    let (l2, r2) = self.dest_eq(th2);
    thm!(self, add(src, self.union_hyps(h1, h2), {f(self, l1, l2)} = {f(self, r1, r2)}))
  }

  pub fn eq_lam(&mut self, x: VarId, th: ProofId) -> ProofId {
    self.mk_eq_fn1(ProofTrace::Lam(th), th, |this, t| this.mk_lam(x, t))
  }

  pub fn eq_binder(&mut self, b: ConstId, x: VarId, th: ProofId) -> ProofId {
    self.mk_eq_fn1(ProofTrace::Binder(th), th, |this, t| this.mk_binder(b, x, t))
  }

  pub fn eq_forall(&mut self, x: VarId, th: ProofId) -> ProofId { self.eq_binder(ConstId::FORALL, x, th) }

  pub fn eq_exists(&mut self, x: VarId, th: ProofId) -> ProofId { self.eq_binder(ConstId::EXISTS, x, th) }

  pub fn eq_uexists(&mut self, x: VarId, th: ProofId) -> ProofId { self.eq_binder(ConstId::UEXISTS, x, th) }

  pub fn eq_select(&mut self, x: VarId, th: ProofId) -> ProofId { self.eq_binder(ConstId::SELECT, x, th) }

  pub fn eq_quant(&mut self, q: Quant, x: VarId, th: ProofId) -> ProofId {

    match q {
      Quant::Lambda => self.eq_lam(x, th),
      Quant::Forall => self.eq_forall(x, th),
      Quant::Exists => self.eq_exists(x, th),
      Quant::UExists => self.eq_uexists(x, th),
      Quant::Select => self.eq_select(x, th),
    }
  }

  pub fn eq_app(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.mk_eq_fn2(ProofTrace::App(th1, th2), th1, th2, |this, t1, t2| this.mk_app(t1, t2))
  }

  pub fn eq_app1(&mut self, th: ProofId, tm: TermId) -> ProofId {
    self.mk_eq_fn1(ProofTrace::App1(th), th, |this, t| this.mk_app(t, tm))
  }

  pub fn eq_app2(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.mk_eq_fn1(ProofTrace::App2(th), th, |this, t| this.mk_app(tm, t))
  }

  pub fn eq_binary(&mut self, b: Binary, x: ProofId, y: ProofId) -> ProofId {
    self.mk_eq_fn2(ProofTrace::Bin(x, y), x, y, |this, x, y| this.mk_binary(b, x, y))
  }

  pub fn eq_binary1(&mut self, b: Binary, x: ProofId, y: TermId) -> ProofId {
    self.mk_eq_fn1(ProofTrace::Bin1(x), x, |this, x| this.mk_binary(b, x, y))
  }

  pub fn eq_binary2(&mut self, b: Binary, x: TermId, y: ProofId) -> ProofId {
    self.mk_eq_fn1(ProofTrace::App2(y), y, |this, y| this.mk_binary(b, x, y))
  }

  pub fn eq_not(&mut self, th: ProofId) -> ProofId {
    self.mk_eq_fn1(ProofTrace::App2(th), th, |this, x| this.mk_not(x))
  }

  pub fn eval_suc_conv(&mut self, tm: TermId) -> ProofId {
    let n = self.try_dest_unop(ConstId::SUC, tm).expect("eval_suc_conv: expected a SUC");
    let mut n = self.dest_int(false, n);
    n += 1u32;
    thm!(self, add0(NumConv, tm = {self.mk_int(n)}))
  }

  pub fn eval_pre_conv(&mut self, tm: TermId) -> ProofId {
    let n = self.try_dest_unop(ConstId::PRE, tm).expect("eval_pre_conv: expected a PRE");
    let mut n = self.dest_int(false, n);
    if !n.is_zero() { n -= 1u32 }
    thm!(self, add0(NumConv, tm = {self.mk_int(n)}))
  }

  pub fn eval_add_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::ADD, tm).expect("eval_add_conv: expected a +");
    let mut a = self.dest_int(false, a);
    let b = self.dest_int(false, b);
    a += b;
    thm!(self, add0(NumConv, tm = {self.mk_int(a)}))
  }

  pub fn eval_sub_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::SUB, tm).expect("eval_sub_conv: expected a -");
    let a = self.dest_int(false, a);
    let b = self.dest_int(false, b);
    let c = a.checked_sub(&b).unwrap_or_else(BigUint::zero);
    thm!(self, add0(NumConv, tm = {self.mk_int(c)}))
  }

  pub fn eval_mult_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::MULT, tm).expect("eval_mult_conv: expected a *");
    let mut a = self.dest_int(false, a);
    let b = self.dest_int(false, b);
    a *= b;
    thm!(self, add0(NumConv, tm = {self.mk_int(a)}))
  }

  pub fn eval_exp_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::EXP, tm).expect("eval_exp_conv: expected an EXP");
    let a = self.dest_int(false, a);
    let b = self.dest_int(false, b);
    let c = a.pow(b.try_into().expect("eval_exp_conv: too big"));
    thm!(self, add0(NumConv, tm = {self.mk_int(c)}))
  }

  pub fn eval_even_conv(&mut self, tm: TermId) -> ProofId {
    let n = self.try_dest_unop(ConstId::EVEN, tm).expect("eval_even_conv: expected an EVEN");
    let n = self.dest_int(false, n);
    thm!(self, add0(NumConv, tm = {self.mk_bool_lit(!n.bit(0))}))
  }

  pub fn eval_odd_conv(&mut self, tm: TermId) -> ProofId {
    let n = self.try_dest_unop(ConstId::ODD, tm).expect("eval_odd_conv: expected an ODD");
    let n = self.dest_int(false, n);
    thm!(self, add0(NumConv, tm = {self.mk_bool_lit(n.bit(0))}))
  }

  pub fn eval_eq_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.dest_eq(tm);
    let a = self.dest_int(false, a);
    let b = self.dest_int(false, b);
    thm!(self, add0(NumConv, tm = {self.mk_bool_lit(a == b)}))
  }

  pub fn eval_lt_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::LT, tm).expect("eval_lt_conv: expected a <");
    let a = self.dest_int(false, a);
    let b = self.dest_int(false, b);
    thm!(self, add0(NumConv, tm = {self.mk_bool_lit(a < b)}))
  }

  pub fn eval_le_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::LE, tm).expect("eval_le_conv: expected a <=");
    let a = self.dest_int(false, a);
    let b = self.dest_int(false, b);
    thm!(self, add0(NumConv, tm = {self.mk_bool_lit(a <= b)}))
  }

  pub fn eval_gt_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::GT, tm).expect("eval_gt_conv: expected a >");
    let a = self.dest_int(false, a);
    let b = self.dest_int(false, b);
    thm!(self, add0(NumConv, tm = {self.mk_bool_lit(a > b)}))
  }

  pub fn eval_ge_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::GE, tm).expect("eval_ge_conv: expected a >=");
    let a = self.dest_int(false, a);
    let b = self.dest_int(false, b);
    thm!(self, add0(NumConv, tm = {self.mk_bool_lit(a >= b)}))
  }
}

#[derive(Debug)]
pub struct SubsInst {
  map: Vec<(TermId, TermId)>,
  ths: Vec<ProofId>,
  hyps: UnionHyps,
  vars: HashSet<VarId>,
}

impl SubsInst {
  pub fn map(&self) -> &[(TermId, TermId)] { &self.map }
  pub fn hyps(&self) -> &[TermId] { &self.hyps.0 }
  pub fn vars(&self) -> &HashSet<VarId> { &self.vars }

  pub fn new(arena: &ProofArena<'_>) -> Self {
    Self { map: vec![], ths: vec![], hyps: UnionHyps::new(arena), vars: HashSet::new() }
  }

  pub fn push(&mut self, arena: &impl HasProofStore, th: ProofId) {
    let Proof {hyps, concl} = *arena[th];
    let (a, b) = arena.dest_eq(concl);
    if a != b {
      if let Err(i) = self.map.binary_search_by(|x| arena.alpha_cmp(a, x.0)) {
        self.map.insert(i, (a, b));
        self.ths.push(th)
      }
      let temp = &mut Default::default();
      arena.frees(&mut self.vars, temp, a);
      arena.frees(&mut self.vars, temp, b);
      self.hyps.insert(arena, hyps)
    }
  }

  fn apply(&self, arena: &mut ProofArena<'_>, a: TermId) -> TermId {
    if let Ok(i) = self.map.binary_search_by(|x| arena.alpha_cmp(a, x.0)) {
      return self.map[i].1
    }
    match *arena[a] {
      Term::App(a1, a2) => {
        let b1 = self.apply(arena, a1);
        let b2 = self.apply(arena, a2);
        if a1 == b1 && a2 == b2 { return a }
        arena.mk_app(b1, b2)
      }
      Term::Lam(x, a1) => if self.vars.contains(&x) {
        let ty = arena[x].ty;
        let (y, yt) = arena.mk_genvar_term(ty);
        let a2 = arena.inst_term_from(&[(x, yt)], a1);
        let b2 = self.apply(arena, a2);
        arena.mk_lam(y, b2)
      } else {
        let b1 = self.apply(arena, a1);
        if a1 == b1 { return a }
        arena.mk_lam(x, b1)
      }
      _ => a
    }
  }
}

#[derive(Debug, Clone)]
#[derive(Default)] // FIXME
pub struct OwnedType {
  pub arena: TypeStore,
  pub tyvars: Box<[TyVarId]>,
  pub ty: TypeId,
}

#[derive(Debug, Clone)]
pub struct OwnedTerm {
  pub arena: TermStore,
  pub tyvars: Box<[TyVarId]>,
  pub term: TermId
}

impl OwnedType {
  pub fn with<'a>(env: &'a Environment, f: impl FnOnce(&mut TypeArena<'a>) -> TypeId) -> OwnedType {
    let mut a = TypeArena::new(env);
    let ty = f(&mut a);
    let tyvars = a.tyvars_in_type(ty);
    let arena = a.into_store();
    OwnedType {arena, tyvars, ty}
  }
}

impl OwnedTerm {
  pub fn with_and<'a, R>(env: &'a Environment,
    f: impl FnOnce(&mut TermArena<'a>) -> (TermId, R)
  ) -> (OwnedTerm, R) {
    let mut a = TermArena::new(env);
    let (term, r) = f(&mut a);
    let tyvars = a.tyvars_in_term(term);
    let arena = a.into_store();
    (OwnedTerm {arena, tyvars, term}, r)
  }

  pub fn with<'a>(env: &'a Environment, f: impl FnOnce(&mut TermArena<'a>) -> TermId) -> OwnedTerm {
    Self::with_and(env, |a| (f(a), ())).0
  }
}

impl ThmDef {
  pub fn with_and<'a, R, S>(env: &'a Environment,
    f: impl FnOnce(&mut ProofArena<'a>) -> (ProofId, R),
    tr_r: impl FnOnce(TermImporter<'_, '_, '_, TermStore>, R) -> S,
  ) -> (ThmDef, S) {
    let mut a = ProofArena::new(env);
    let (n, r) = f(&mut a);
    let Proof {hyps, concl} = *a[n];
    let store = a.into_store();
    let mut a = TermArena::new(env);
    let (hyps, concl, r) = a.import(&store.tms, |mut tr| (
      store[hyps].0.iter().map(|&t| tr.tr_term(t)).collect::<Box<[_]>>(),
      tr.tr_term(concl),
      tr_r(tr, r)
    ));
    let mut c = CollectTyVarsTerm::new(&a);
    c.collect(&a, concl);
    for &h in &*hyps { c.collect(&a, h) }
    (ThmDef::new(a.into_store(), c.c.get(), hyps, concl), r)
  }

  pub fn with<'a>(env: &'a Environment, f: impl FnOnce(&mut ProofArena<'a>) -> ProofId) -> ThmDef {
    Self::with_and(env, |a| (f(a), ()), |_, _| ()).0
  }
}

// #[derive(Debug)]
// pub enum Object {
//   TypeDecl(String, u32),
//   ConstDecl(String, OwnedType),
//   Axiom(String, OwnedTerm),
//   BasicDef(String, OwnedTerm),
//   Def(String, OwnedTerm),
//   Spec(Box<[String]>, OwnedProof),
//   BasicTypedef(String, OwnedProof),
//   Thm(String, OwnedProof),
//   OpenThm(String, OwnedProof),
//   NumThm(u32, OwnedProof),
//   TypeBij([String; 3]),
// }

#[derive(Debug)]
pub struct EnvironmentInner {
  tyvars: Dedup<TyVar>,
  pub tyops: Vec<TyopDef>,
  pub consts: Vec<ConstDef>,
  pub specs: Arc<Mutex<Vec<SpecDef>>>,
  pub thms: Vec<Arc<ThmDef>>,
  pub trans: TransTable,
  pub mm0: Option<mm0::Mm0Env>,
}

impl Index<TyVarId> for EnvironmentInner {
  type Output = Arc<str>;
  fn index(&self, n: TyVarId) -> &Arc<str> { &self.tyvars[n].0 }
}
impl Index<TyopId> for EnvironmentInner {
  type Output = TyopDef;
  fn index(&self, n: TyopId) -> &Self::Output { &self.tyops[n.into_usize()] }
}
impl Index<ConstId> for EnvironmentInner {
  type Output = ConstDef;
  fn index(&self, n: ConstId) -> &Self::Output { &self.consts[n.into_usize()] }
}
impl Index<ThmId> for EnvironmentInner {
  type Output = Arc<ThmDef>;
  fn index(&self, n: ThmId) -> &Self::Output { &self.thms[n.into_usize()] }
}

impl EnvironmentInner {
  pub fn new(mm0: &mut Option<mm0::Mm0Writer>) -> Self {
    Self {
      tyvars: Default::default(),
      tyops: Default::default(),
      consts: Default::default(),
      specs: Default::default(),
      thms: Default::default(),
      trans: Default::default(),
      mm0: mm0.take().map(mm0::Mm0Env::new),
    }
  }

  pub fn mk_tyvar(&mut self, x: Arc<TyVar>) -> TyVarId { self.tyvars.add_inner(x, ()).0 }

  pub fn add_tyop<'a>(&mut self, orig: Option<mm0::TermId>, mut td: TyopDef) -> TyopId {
    let name = td.name.clone();
    let n = Idx::from(self.tyops.len() as u32);
    if let Some(mm0) = &mut self.mm0 {
      let (mm0t, mm0td) = mm0.add_tyop(&name, n, &td, orig);
      td.mm0 = mm0t;
      if let Some((_, r)) = &mut td.tydef { *r = mm0td }
    }
    self.tyops.push(td);
    assert!(self.trans.tyops.insert(name, n).is_none());
    n
  }

  pub fn add_const<'a>(&mut self, name: String,
    orig: Option<(mm0::TermId, mm0::ThmId)>,
    reason: ConstReason<'_>,
    ty: OwnedType,
  ) -> ConstId {
    let n = Idx::from(self.consts.len() as u32);
    let mm0 = if let Some(mm0) = &mut self.mm0 {
      mm0.add_const(&name, n, &ty, orig, reason)
    } else { Default::default() };
    self.consts.push(ConstDef { name: name.clone(), ty, mm0 });
    assert!(self.trans.consts.insert(name, n).is_none());
    n
  }

  pub fn add_anon_thm<'a>(&mut self, name: Option<&str>,
    orig: Option<mm0::ThmId>, mut d: ThmDef,
  ) -> ThmId {
    let n = Idx::from(self.thms.len() as u32);
    if let Some(mm0) = &mut self.mm0 {
      d.mm0 = mm0.add_thm(name, n, &d, orig)
    }
    self.thms.push(Arc::new(d));
    n
  }

  pub fn add_thm_alias<'a>(&mut self, k: FetchKind, name: String, th: ThmId) {
    match self.trans.fetches[k].entry(name) {
      Entry::Vacant(e) => { e.insert(th); }
      Entry::Occupied(e) => panic!("{:?} {:?} already exists", k, e.key())
    }
  }

  pub fn add_thm<'a>(&mut self, k: FetchKind, name: String,
    orig: Option<mm0::ThmId>, d: ThmDef
  ) -> ThmId {
    let n = self.add_anon_thm(Some(&name), orig, d);
    self.add_thm_alias(k, name, n);
    n
  }
}

#[derive(Debug)]
pub struct Environment(RwLock<EnvironmentInner>);

pub struct EnvRef<'a>(RwLockReadGuard<'a, EnvironmentInner>);
pub struct EnvRefMut<'a>(RwLockWriteGuard<'a, EnvironmentInner>);

impl Deref for EnvRef<'_> {
  type Target = EnvironmentInner;
  fn deref(&self) -> &Self::Target { &*self.0 }
}
impl Deref for EnvRefMut<'_> {
  type Target = EnvironmentInner;
  fn deref(&self) -> &Self::Target { &*self.0 }
}
impl DerefMut for EnvRefMut<'_> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut *self.0 }
}

impl EnvRef<'_> {
  pub fn print<S: ?Sized>(&self, arena: &S, f: impl FnOnce(EnvPrint<'_, S>)) {
    if get_print() { self.print_always(arena, f) }
  }

  pub fn print_always<S: ?Sized, R>(&self, arena: &S, f: impl FnOnce(EnvPrint<'_, S>) -> R) -> R {
    f(EnvPrint { env: self, arena })
  }
}

impl Environment {
  pub fn new(mm0: &mut Option<mm0::Mm0Writer>) -> Self {
    Self(RwLock::new(EnvironmentInner::new(mm0)))
  }

  pub fn read(&self) -> EnvRef<'_> { EnvRef(self.0.read().unwrap()) }
  pub fn write(&self) -> EnvRefMut<'_> { EnvRefMut(self.0.write().unwrap()) }
  pub fn mk_tyvar(&self, x: Arc<TyVar>) -> TyVarId { self.write().mk_tyvar(x) }

  pub fn print<S: ?Sized>(&self, arena: &S, f: impl FnOnce(EnvPrint<'_, S>)) {
    self.read().print(arena, f)
  }

  pub fn print_always<S: ?Sized, R>(&self, arena: &S, f: impl FnOnce(EnvPrint<'_, S>) -> R) -> R {
    self.read().print_always(arena, f)
  }

  pub fn add_tyop<'a>(&self,
    name: impl Into<Cow<'a, str>>,
    orig: Option<mm0::TermId>,
    arity: u32, tydef: Option<(ThmId, mm0::TydefId)>
  ) -> TyopId {
    self.write().add_tyop(orig, TyopDef {
      name: name.into().into_owned(),
      arity,
      mm0: Default::default(),
      tydef
    })
  }

  pub fn add_const<'a>(&self, name: impl Into<Cow<'a, str>>,
    orig: Option<(mm0::TermId, mm0::ThmId)>,
    reason: ConstReason<'_>,
    ty: OwnedType,
  ) -> ConstId {
    self.write().add_const(name.into().into_owned(), orig, reason, ty)
  }

  pub fn add_anon_thm<'a>(&self, name: Option<&str>,
    orig: Option<mm0::ThmId>, d: ThmDef
  ) -> ThmId {
    self.write().add_anon_thm(name, orig, d)
  }

  pub fn add_thm_alias<'a>(&self, k: FetchKind, name: impl Into<Cow<'a, str>>, th: ThmId) {
    self.write().add_thm_alias(k, name.into().into_owned(), th)
  }

  pub fn add_thm<'a>(&self, k: FetchKind, name: impl Into<Cow<'a, str>>,
    orig: Option<mm0::ThmId>, d: ThmDef
  ) -> ThmId {
    self.write().add_thm(k, name.into().into_owned(), orig, d)
  }

  pub fn add_type_bijs<'a>(&self, c: TyopId, cname: &str,
    abs: impl Into<Cow<'a, str>>, rep: impl Into<Cow<'a, str>>,
    orig: Option<([(mm0::TermId, mm0::ThmId); 2], [mm0::ThmId; 2])>,
  ) -> (ConstId, ConstId, ThmId, ThmId) {
    let abs = abs.into(); let rep = rep.into();
    let env = self.read();
    let (exists_p, mm0td) = *env[c].tydef
      .as_ref().expect("add_type_bijs: not a type operator");
    let ThmDef {arena: ref store, concl, ..} = *env[exists_p].clone();
    drop(env);
    let (p, v) = store.dest_app(store.dest_exists(concl).1);
    let ty = store.type_of(v);
    let mut tyargs = store.tyvars_in_term(p);
    match &self.read().tyvars {
      tyvars => tyargs.sort_by_key(|&v| &*tyvars[v].0)
    }
    let absc = OwnedType::with(self, |a| {
      // abs[v0..vn]: A -> C[v0..vn]
      let aty = a.import(&store.tys, |mut tr| tr.tr(ty));
      let args = tyargs.iter().map(|&v| a.mk_tyvar(v)).collect();
      let cty = a.mk_tyop(c, args);
      ty!(a, aty -> cty)
    });
    let absc = self.add_const(&*abs, orig.as_ref().map(|p| p.0[0]),
      ConstReason::Abs(mm0td), absc);
    let repc = OwnedType::with(self, |a| {
      // rep[v0..vn]: C[v0..vn] -> A
      let aty = a.import(&store.tys, |mut tr| tr.tr(ty));
      let args = tyargs.iter().map(|&v| a.mk_tyvar(v)).collect();
      let cty = a.mk_tyop(c, args);
      ty!(a, cty -> aty)
    });
    let repc = self.add_const(&*rep, orig.as_ref().map(|p| p.0[1]),
      ConstReason::Rep(mm0td), repc);
    let abs_rep = ThmDef::with(self, |a| {
      let t = &mut a.tms;
      let abs = t.mk_const_natural(absc);
      let rep = t.mk_const_natural(repc);
      let (v, va) = t.mk_var_term("a".into(), t.dest_fun(t.type_of(abs)).1);
      // |- !a: C. abs (rep a) = a
      let concl = term!(t, !v. (A abs (A rep va)) = va);
      a.add0(concl, ProofTrace::NewTypeBij1(c))
    });
    let abs_rep = self.add_thm(FetchKind::TypeBij1, cname, orig.as_ref().map(|p| p.1[0]), abs_rep);
    let rep_abs = ThmDef::with(self, |a| {
      let t = &mut a.tms;
      let abs = t.mk_const_natural(absc);
      let rep = t.mk_const_natural(repc);
      let p = t.import(store, |mut tr| tr.tr_term(p));
      let (v, vr) = t.mk_var_term("r".into(), t.dest_fun(t.type_of(abs)).0);
      // |- !r: A. P r <=> rep (abs r) = r
      let concl = term!(t, !v. (A p vr) = ((A rep (A abs vr)) = vr));
      a.add0(concl, ProofTrace::NewTypeBij2(c))
    });
    let rep_abs = self.add_thm(FetchKind::TypeBij2, cname, orig.as_ref().map(|p| p.1[1]), rep_abs);
    (absc, repc, abs_rep, rep_abs)
  }

  pub fn add_basic_def<'a>(&self, x: impl Into<Cow<'a, str>>,
    orig: Option<((mm0::TermId, mm0::ThmId), mm0::ThmId)>,
    tm: OwnedTerm
  ) -> (ConstId, ThmId) {
    let x = x.into();
    let ty = OwnedType::with(self, |a| {
      a.import(&tm.arena, |mut tr| tr.tr(tm.arena.type_of(tm.term)))
    });
    let c = self.add_const(&*x, orig.as_ref().map(|p| p.0),
      ConstReason::Def(&tm), ty);
    let th = ThmDef::with(self, |a| {
      let rhs = a.tms.import(&tm.arena, |mut tr| tr.tr_term(tm.term));
      let lhs = a.mk_const_natural(c);
      thm!(a, add0(NewBasicDef(c), lhs = rhs))
    });
    (c, self.add_thm(FetchKind::BasicDef, x, orig.as_ref().map(|p| p.1), th))
  }

  pub fn add_simple_def<'a>(&self, x: impl Into<Cow<'a, str>>,
    arity: u32,
    orig: Option<(((mm0::TermId, mm0::ThmId), mm0::ThmId), mm0::ThmId)>,
    tm: OwnedTerm,
  ) -> (ConstId, ThmId) {
    let x = x.into();
    let (c, th) = self.add_basic_def(&*x, orig.as_ref().map(|p| p.0), tm);
    if arity == 0 {
      self.add_thm_alias(FetchKind::Def, x, th);
      (c, th)
    } else {
      let ThmDef {ref arena, concl, ..} = *self.read()[th].clone();
      let th = ThmDef::with(self, |a| {
        let concl = a.tms.import(arena, |mut tr| {
          let (lhs, mut rhs) = arena.dest_eq(concl);
          let mut lhs = tr.tr_term(lhs);
          let mut stk = vec![];
          for _ in 0..arity {
            let (x, e) = arena.dest_lam(rhs);
            let x = tr.tr_var(x);
            lhs = term!(tr.dest(), A lhs (V(x)));
            stk.push(x);
            rhs = e;
          }
          let mut concl = term!(tr.dest(), lhs = {tr.tr_term(rhs)});
          for x in stk.into_iter().rev() {
            concl = tr.dest().mk_forall(x, concl)
          }
          concl
        });
        a.add0(concl, ProofTrace::NewSimpleDef(c))
      });
      (c, self.add_thm(FetchKind::Def, x, orig.as_ref().map(|p| p.1), th))
    }
  }

  pub fn add_def<'a>(&self, x: impl Into<Cow<'a, str>>,
    orig: Option<(((mm0::TermId, mm0::ThmId), mm0::ThmId), mm0::ThmId)>,
    OwnedTerm {arena: old, term, ..}: OwnedTerm,
  ) -> (ConstId, ThmId) {
    fn untuple(e: TermId, old: &TermStore, gv: TermId,
      tr: &mut TermImporter<'_, '_, '_, TermStore>,
      visit: &mut impl FnMut(VarId, VarId, TermId, &mut TermArena<'_>),
    ) {
      if let Some((e1, e2)) = old.try_dest_pair(e) {
        untuple(e1, old, tr.dest().mk_fst(gv), tr, visit);
        untuple(e2, old, tr.dest().mk_snd(gv), tr, visit);
      } else {
        let v = old.dest_var(e);
        visit(v, tr.tr_var(v), gv, tr.dest())
      }
    }
    let x = x.into();
    let (vs2, body) = old.strip_forall(term);
    let (lhs, rhs) = old.dest_eq(body);
    let (head, args) = old.strip_app(lhs);
    assert!(matches!(old[old.dest_var(head)].name, VarName::Str(ref n) if **n == *x));
    let mut vs1 = vec![];
    let tm = OwnedTerm::with(self, |a| a.import(&old, |mut tr| {
      let mut subst = InstTerm::default();
      let gvs = args.iter().map(|&e| {
        let ty = tr.tr_type(old.type_of(e));
        let (gv, gt) = tr.dest().mk_genvar_term(ty);
        untuple(e, &old, gt, &mut tr, &mut |oldv, v, tm, a| {
          subst.insert(a, v, tm);
          if !vs2.contains(&oldv) { vs1.push(oldv) }
        });
        gv
      }).collect::<Vec<_>>();
      let rhs = tr.tr_term(rhs);
      let mut lam = subst.apply(tr.dest(), rhs);
      for gv in gvs.into_iter().rev() { lam = tr.dest().mk_lam(gv, lam) }
      lam
    }));
    let (c, th) = self.add_basic_def(&*x, orig.as_ref().map(|p| p.0), tm);
    if vs2.is_empty() && args.is_empty() {
      self.add_thm_alias(FetchKind::Def, x, th);
      (c, th)
    } else {
      let th = ThmDef::with(self, |a| {
        let concl = a.tms.import(&old, |mut tr| {
          let mut lhs = tr.dest().mk_const_natural(c);
          for e in args { lhs = term!(tr.dest(), A lhs {tr.tr_term(e)}) }
          let mut concl = term!(tr.dest(), lhs = {tr.tr_term(rhs)});
          for x in vs2.into_iter().rev().chain(vs1.into_iter().rev()) {
            let x = tr.tr_var(x);
            concl = tr.dest().mk_forall(x, concl)
          }
          concl
        });
        a.add0(concl, ProofTrace::NewDef(c))
      });
      (c, self.add_thm(FetchKind::Def, x, orig.as_ref().map(|p| p.1), th))
    }
  }

  pub fn add_basic_typedef<'a>(&self, x: impl Into<Cow<'a, str>>,
    orig: Option<(mm0::ThmId, mm0::TermId, mm0::TydefId)>,
    th: ThmDef
  ) -> TyopId {
    let x = x.into();
    let arity = th.tyvars.len() as u32;
    let exists_p = self.add_anon_thm(Some(&x), orig.as_ref().map(|p| p.0), th);
    self.add_tyop(&*x, orig.as_ref().map(|p| p.1), arity,
      Some((exists_p, orig.as_ref().map_or(Default::default(), |p| p.2))))
  }

  pub fn add_spec<'a>(&self, xs: &[impl Borrow<str>],
    orig: &[((mm0::TermId, mm0::ThmId), mm0::ThmId)],
    orig_spec: Option<mm0::ThmId>,
    td: ThmDef,
  ) -> (Vec<ConstId>, ThmId) {
    assert!(td.hyps.is_empty());
    let mut term = td.concl;
    let mut subst: Vec<(VarId, ConstId)> = vec![];
    for (i, x) in xs.iter().enumerate() {
      let x = x.borrow();
      let (v, body) = td.arena.dest_exists(term);
      let tm = OwnedTerm::with(self, |a| {
        let (v, body) = a.import(&td.arena, |mut tr| (tr.tr_var(v), tr.tr_term(body)));
        let t = a.mk_select(v, body);
        let mut inst = InstTerm::default();
        for &(v, c) in &subst {
          let ct = a.mk_const_natural(c); inst.insert(a, v, ct)
        }
        inst.apply(a, t)
      });
      let (c, th) = self.add_basic_def(&*x, orig.get(i).copied(), tm);
      self.add_thm_alias(FetchKind::Def, x, th);
      subst.push((v, c));
      term = body;
    }
    let specs = self.read().specs.clone();
    let mut specs = specs.lock().unwrap();
    let spec = Idx::from(specs.len() as u32);
    let n = self.add_anon_thm(None, orig_spec, ThmDef::with(self, |a| {
      let concl = a.tms.import(&td.arena, |mut tr| {
        let t = tr.tr_term(term);
        let mut inst = InstTerm::default();
        for &(v, c) in &subst {
          let v = tr.tr_var(v);
          let ct = tr.dest().mk_const_natural(c);
          inst.insert(tr.dest(), v, ct);
        }
        inst.apply(tr.dest(), t)
      });
      a.add0(concl, ProofTrace::NewSpec(spec))
    }));
    for x in xs { self.add_thm_alias(FetchKind::Spec, x.borrow().to_owned(), n) }
    let consts: Vec<_> = subst.into_iter().map(|p| p.1).collect();
    specs.push(SpecDef {orig: td, consts: (&*consts).into()});
    (consts, n)
  }

  pub fn add_axiom(&self, x: String,
    orig: Option<mm0::ThmId>, OwnedTerm {arena, tyvars, term}: OwnedTerm) -> ThmId {
    assert!(arena.is_boolean(term));
    self.add_thm(FetchKind::Axiom, x, orig, ThmDef::new(arena, tyvars, Box::new([]), term))
  }
}
