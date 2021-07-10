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
use std::rc::Rc;
use std::borrow::Cow;
use bitvec::{bitbox, prelude::BitBox};
use num::{BigUint, Zero, CheckedSub};

use crate::print::Print;
use crate::types::*;

pub trait Node: Hash + Eq { type Idx: Idx; }
impl Node for TyVar { type Idx = TyVarId; }
impl Node for Type { type Idx = TypeId; }
impl Node for Var { type Idx = VarId; }
impl Node for Term { type Idx = TermId; }
impl Node for Proof { type Idx = ProofId; }
impl Node for Hyps { type Idx = HypsId; }

#[derive(Debug)]
pub struct Store<H, A = ()>(Vec<(Rc<H>, A)>);

impl<H, A: Clone> Clone for Store<H, A> {
  fn clone(&self) -> Self { Self(self.0.clone()) }
}
impl<H: Node, A> Index<H::Idx> for Store<H, A> {
  type Output = (Rc<H>, A);
  fn index(&self, n: H::Idx) -> &Self::Output {
    &self.0[n.into_usize()]
  }
}
impl<H: Node, A> IndexMut<H::Idx> for Store<H, A> {
  fn index_mut(&mut self, n: H::Idx) -> &mut Self::Output {
    &mut self.0[n.into_usize()]
  }
}

impl<H, A> Default for Store<H, A> {
  fn default() -> Self { Self(vec![]) }
}

#[derive(Debug)]
struct Dedup<H, A = ()> {
  map: HashMap<Rc<H>, u32>,
  store: Store<H, A>,
}

impl<H, A> Default for Dedup<H, A> {
  fn default() -> Self { Self { map: Default::default(), store: Default::default() } }
}

impl<H: Node, A> Index<H::Idx> for Dedup<H, A> {
  type Output = (Rc<H>, A);
  fn index(&self, n: H::Idx) -> &Self::Output { &self.store[n] }
}

impl<H: Node, A> IndexMut<H::Idx> for Dedup<H, A> {
  fn index_mut(&mut self, n: H::Idx) -> &mut Self::Output { &mut self.store[n] }
}

impl<H: Node, A> Dedup<H, A> {
  fn add_inner(&mut self, v: Rc<H>, a: A) -> (H::Idx, bool) {
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
  #[inline] fn add_val(&mut self, v: H, a: A) -> H::Idx { self.add_inner(Rc::new(v), a).0 }
  #[inline] fn add_default(&mut self, v: H) -> (H::Idx, bool) where A: Default {
    self.add_inner(Rc::new(v), A::default())
  }
}
impl<H: Node> Dedup<H> {
  #[inline] fn add(&mut self, v: H) -> H::Idx { self.add_val(v, ()) }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct TyVar(String);

#[derive(Debug, Clone, Default)]
pub struct TypeStore(pub Store<Type>);

pub trait HasTypeStore: Index<TypeId, Output=Rc<Type>> {
  fn type_store(&self) -> &Store<Type>;

  fn dest_tyvar(&self, a: TypeId) -> TyVarId {
    if let Type::Var(v) = *self[a] { v }
    else { panic!("dest_tyvar: not a variable") }
  }

  fn dest_fun(&self, a: TypeId) -> (TypeId, TypeId) {
    if let Type::Const(TyopId::FUN, ref args) = *self[a] { (args[0], args[1]) }
    else { panic!("dest_fun: not a function type") }
  }

  fn dest_prod(&self, a: TypeId) -> (TypeId, TypeId) {
    if let Type::Const(TyopId::PROD, ref args) = *self[a] { (args[0], args[1]) }
    else { panic!("dest_prod: not a product type") }
  }

  fn is_bool(&self, ty: TypeId) -> bool {
    matches!(*self[ty], Type::Const(TyopId::BOOL, _))
  }

  fn types(&self) -> &[(Rc<Type>, ())] { &self.type_store().0 }

  fn print_with_env<'a, T>(&'a self, env: Option<&'a Environment>, t: T) -> Print<'a, Self, T> {
    Print {env, arena: self, t}
  }
}

macro_rules! impl_index { ($ty:ty: $($tgt:ty => $f:ident),*) => {$(
  impl Index<<$tgt as Node>::Idx> for $ty {
    type Output = Rc<$tgt>;
    fn index(&self, n: <$tgt as Node>::Idx) -> &Rc<$tgt> { &self.$f()[n].0 }
  }
)*}}

impl_index!(TypeStore: Type => type_store);
impl HasTypeStore for TypeStore {
  fn type_store(&self) -> &Store<Type> { &self.0 }
}

#[derive(Debug)]
pub struct TypeArena<'a> {
  pub env: &'a Environment,
  tyvars: Dedup<TyVar>,
  tys: Dedup<Type>,
  bool: Option<TypeId>,
  bool_unop: Option<TypeId>,
  bool_binop: Option<TypeId>,
}

impl_index!(TypeArena<'_>: Type => type_store);
impl HasTypeStore for TypeArena<'_> {
  fn type_store(&self) -> &Store<Type> { &self.tys.store }
}

macro_rules! ty {
  ($self:expr, {$($e:tt)*}) => { {$($e)*} };
  ($self:expr, ($($e:tt)*)) => { ty!($self, $($e)*) };
  ($self:expr, bool) => {{ $self.mk_bool() }};
  ($self:expr, $e:tt -> $($e2:tt)*) => {{
    let e = ty!($self, $e); let e2 = ty!($self, $($e2)*); $self.mk_fun(e, e2)
  }};
  ($self:expr, $e:tt * $($e2:tt)*) => {{
    let e = ty!($self, $e); let e2 = ty!($self, $($e2)*); $self.mk_prod(e, e2)
  }};
  ($self:expr, $($e:tt)*) => {{$($e)*}};
}

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
  ($self:expr, add($hyps:expr, $($t:tt)*)) => {{
    let hyps = $hyps; let concl = term!($self, $($t)*); $self.add(hyps, concl)
  }};
  ($self:expr, add0($($t:tt)*)) => {{
    let concl = term!($self, $($t)*); $self.add0(concl)
  }};
  ($self:expr, $($e:tt)*) => {{$($e)*}};
}

impl<'a> TypeArena<'a> {
  pub fn into_store(self) -> TypeStore { TypeStore(self.tys.store) }
  pub fn new(env: &'a Environment) -> Self {

    Self {
      env,
      tyvars: Dedup::default(), tys: Dedup::default(),
      bool: None, bool_unop: None, bool_binop: None,
    }
  }

  pub fn mk_var_name(&mut self, x: String) -> TyVarId {
    self.tyvars.add(TyVar(x))
  }

  pub fn mk_var(&mut self, x: TyVarId) -> TypeId {
    self.tys.add(Type::Var(x))
  }

  pub fn mk_vars_upto(&mut self, n: u32) -> Vec<TypeId> {
    (0..n).map(|i| self.mk_var(TyVarId(i))).collect()
  }

  pub fn mk_fun(&mut self, a: TypeId, b: TypeId) -> TypeId {
    self.tys.add(Type::Const(TyopId::FUN, vec![a, b]))
  }

  pub fn mk_prod(&mut self, ty1: TypeId, ty2: TypeId) -> TypeId {
    self.tys.add(Type::Const(TyopId::PROD, vec![ty1, ty2]))
  }

  pub fn mk_const(&mut self, c: TyopId, tys: Vec<TypeId>) -> TypeId {
    assert_eq!(self.env[c].arity as usize, tys.len());
    self.tys.add(Type::Const(c, tys))
  }

  pub fn mk_const_upto(&mut self, c: TyopId) -> TypeId {
    let tys = self.mk_vars_upto(self.env[c].arity);
    self.tys.add(Type::Const(c, tys))
  }

  fn inst_extern(&mut self, inst: &[TypeId], tr: &[TypeId], ty: &Type) -> TypeId {
    match *ty {
      Type::Var(n) => inst.get(n.into_usize()).copied().unwrap_or_else(|| self.mk_var(n)),
      Type::Const(c, ref tys) =>
        self.mk_const(c, tys.iter().map(|&ty| tr[ty.into_usize()]).collect())
    }
  }

  fn inst_store(&mut self, inst: &[TypeId], tys: &TypeStore) -> Vec<TypeId> {
    let mut tr = vec![];
    for ty in tys.types() { tr.push(self.inst_extern(inst, &tr, &*ty.0)) }
    tr
  }

  fn inst_owned(&mut self, inst: &[TypeId], ty: &OwnedType) -> TypeId {
    self.inst_store(inst, &ty.arena)[ty.ty.into_usize()]
  }

  fn inst<R, S: HasTypeStore>(&mut self, store: &S, inst: &[TypeId],
    f: impl FnOnce(TypeTranslator<'a, '_, S>) -> R
  ) -> R {
    let mut vec = vec![None; store.types().len()];
    f(TypeTranslator { arena: self, store, inst, imported: &mut vec })
  }

  fn import<R, S: HasTypeStore>(&mut self, store: &S,
    f: impl FnOnce(TypeTranslator<'a, '_, S>) -> R
  ) -> R { self.inst(store, &[], f) }

  fn mk_bool(&mut self) -> TypeId {
    if let Some(t) = self.bool { t } else {
      let bool = self.mk_const(TyopId::BOOL, vec![]);
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

  pub fn pp<T>(&self, t: T) -> Print<'_, Self, T> {
    self.print_with_env(Some(self.env), t)
  }
}

pub struct TypeTranslator<'a, 'b, S> {
  arena: &'b mut TypeArena<'a>,
  store: &'b S,
  inst: &'b [TypeId],
  imported: &'b mut [Option<TypeId>],
}

impl<'a, 'b, S: HasTypeStore> TypeTranslator<'a, 'b, S> {
  fn tr(&mut self, ty: TypeId) -> TypeId {
    if let Some(i) = self.imported[ty.into_usize()] { return i }
    let n = match *self.store[ty] {
      Type::Var(n) =>
        self.inst.get(n.into_usize()).copied().unwrap_or_else(|| self.arena.mk_var(n)),
      Type::Const(c, ref tys) => {
        let tys = tys.clone().iter().map(|&ty| self.tr(ty)).collect();
        self.arena.mk_const(c, tys)
      }
    };
    self.imported[ty.into_usize()] = Some(n);
    n
  }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum VarName {
  Str(String),
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
  Index<VarId, Output=Rc<Var>> +
  Index<TermId, Output=Rc<Term>>
{
  fn var_store(&self) -> &Store<Var>;
  fn term_store(&self) -> &Store<Term, TypeId>;

  fn vars(&self) -> &[(Rc<Var>, ())] { &self.var_store().0 }

  fn terms(&self) -> &[(Rc<Term>, TypeId)] { &self.term_store().0 }

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

  fn dest_int(&mut self, t: TermId) -> BigUint {
    let mut t = self.try_dest_unop(ConstId::NUMERAL, t).expect("dest_int: not a numeral");
    let mut out = BigUint::zero();
    loop {
      match *self[t] {
        Term::Const(ConstId::ZERO, _) => return out,
        Term::App(f, e) => {
          match *self[f] {
            Term::Const(ConstId::BIT0, _) => { out <<= 1 }
            Term::Const(ConstId::BIT1, _) => { out <<= 1; out += 1u32 }
            _ => panic!("dest_int: unexpected term"),
          }
          t = e;
        }
        _ => panic!("dest_int: unexpected term"),
      }
    }
  }

  fn alpha_cmp(&self, a: TermId, b: TermId) -> Ordering {
    fn rec<T: HasTermStore + ?Sized>(this: &T,
      ctx: &mut Vec<(VarId, VarId)>, a: TermId, b: TermId
    ) -> Ordering {
      if a == b && ctx.iter().all(|&(x, y)| x == y) { return Ordering::Equal }
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
    match *self[t] {
      Term::Var(v) => if !bound.contains(&v) { free.insert(v); }
      Term::Const(_, _) => {}
      Term::App(f, x) => { self.frees(free, bound, f); self.frees(free, bound, x) }
      Term::Lam(v, t) => {
        let old = bound.insert(v);
        self.frees(free, bound, t);
        if !old { bound.remove(&v); }
      }
    }
  }

  fn alpha_eq(&self, a: TermId, b: TermId) -> bool { a == b || self.alpha_cmp(a, b).is_eq() }
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

  pub fn mk_var_id(&mut self, name: String, ty: TypeId) -> VarId {
    self.vars.add(Var {name: VarName::Str(name), ty})
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

  pub fn mk_var_term(&mut self, x: String, ty: TypeId) -> (VarId, TermId) {
    let v = self.mk_var_id(x, ty);
    (v, self.tms.add_val(Term::Var(v), ty))
  }

  pub fn mk_var(&mut self, x: VarId) -> TermId {
    self.tms.add_val(Term::Var(x), self[x].ty)
  }

  pub fn mk_const(&mut self, c: ConstId, tys: Vec<TypeId>) -> TermId {
    assert_eq!(tys.len(), self.tys.env[c].ty.tyvars as usize);
    self.add_self(Term::Const(c, tys), |this, n| {
      let tys = if let Term::Const(_, tys) = &*this.tms[n].0 { tys } else { unreachable!() };
      this.tys.inst_owned(tys, &this.tys.env[c].ty)
    })
  }

  pub fn mk_const_upto(&mut self, c: ConstId) -> TermId {
    let arity = self.env[c].ty.tyvars;
    let tys = self.mk_vars_upto(arity);
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
      panic!("mk_app: type mismatch:\n{}\nis applied to\n{}",
        self.pp_type(f), self.pp_type(x));
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

  pub fn get_conj(&mut self) -> TermId { get_term_cache!(self, conj, CONJ, get_bool_binop) }

  pub fn get_disj(&mut self) -> TermId { get_term_cache!(self, disj, DISJ, get_bool_binop) }

  pub fn get_imp(&mut self) -> TermId { get_term_cache!(self, imp, IMP, get_bool_binop) }

  pub fn get_not(&mut self) -> TermId { get_term_cache!(self, not, NOT, get_bool_unop) }

  pub fn mk_true(&mut self) -> TermId { get_term_cache!(self, tru, TRUE, mk_bool) }

  pub fn mk_false(&mut self) -> TermId { get_term_cache!(self, fal, FALSE, mk_bool) }

  pub fn mk_bool_lit(&mut self, b: bool) -> TermId {
    if b { self.mk_true() } else { self.mk_false() }
  }

  pub fn mk_conj(&mut self, x: TermId, y: TermId) -> TermId { term!(self, A (self.get_conj()) x y) }

  pub fn mk_disj(&mut self, x: TermId, y: TermId) -> TermId { term!(self, A (self.get_disj()) x y) }

  pub fn mk_imp(&mut self, x: TermId, y: TermId) -> TermId { term!(self, A (self.get_imp()) x y) }

  pub fn mk_not(&mut self, x: TermId) -> TermId { term!(self, A (self.get_not()) x) }

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

  fn subst_term_once(&mut self,
    trtys: &[TypeId], trvars: &[VarId], trtms: &[TermId], tm: &Term
  ) -> TermId {
    match *tm {
      Term::Var(x) => self.mk_var(trvars[x.into_usize()]),
      Term::Const(c, ref tyargs) =>
        self.mk_const(c, tyargs.iter().map(|ty| trtys[ty.into_usize()]).collect()),
      Term::App(f, x) => self.mk_app(trtms[f.into_usize()], trtms[x.into_usize()]),
      Term::Lam(x, e) => self.mk_lam(trvars[x.into_usize()], trtms[e.into_usize()]),
    }
  }

  fn mk_var_avoiding(&mut self, name: &VarName, ty: TypeId, mut f: impl FnMut(VarId) -> bool) -> VarId {
    if let VarName::Str(name) = name {
      let new = Var {name: VarName::Str(name.clone()), ty};
      if !self.vars.map.get(&new).map_or(false, |&v| f(VarId(v))) {
        return self.vars.add(new)
      }
    }
    self.mk_genvar(ty)
  }

  fn inst_type_store(&mut self, inst: &[TypeId], s: &TermStore) -> (Vec<TypeId>, Vec<VarId>, Vec<TermId>) {
    let trtys = self.tys.inst_store(inst, &s.tys);
    let mut trvars = vec![];
    for (v, _) in s.vars() {
      trvars.push(self.mk_var_avoiding(&v.name,
        trtys[v.ty.into_usize()], |v| trvars.contains(&v)))
    }
    let mut trtms = vec![];
    for tm in s.terms() { trtms.push(self.subst_term_once(&trtys, &trvars, &trtms, &tm.0)) }
    (trtys, trvars, trtms)
  }

  // fn inst_type_owned(&mut self, inst: &[TypeId], tm: &OwnedTerm) -> TermId {
  //   self.inst_type_store(inst, &tm.arena).2[tm.term.into_usize()]
  // }

  fn inst_type<R, S: HasTermStore>(&mut self, store: &S,
    inst: &[TypeId], f: impl FnOnce(TermInstType<'a, '_, S>) -> R
  ) -> R {
    let tys = &mut vec![None; store.types().len()];
    let vars = &mut vec![None; store.vars().len()];
    let tms = &mut vec![None; store.terms().len()];
    f(TermInstType { arena: self, store, inst, tys, tms, vars })
  }

  fn import<R, S: HasTermStore>(&mut self, store: &S,
    f: impl FnOnce(TermInstType<'a, '_, S>) -> R) -> R {
    self.inst_type(store, &[], f)
  }

  fn inst_term_simple(&mut self, inst: &mut HashMap<VarId, TermId>, tm: TermId) -> TermId {
    match *self[tm].clone() {
      Term::Var(x) => inst.get(&x).cloned().unwrap_or(tm),
      Term::Const(_, _) => tm,
      Term::App(f, x) =>
        term!(self, A (self.inst_term_simple(inst, f)) (self.inst_term_simple(inst, x))),
      Term::Lam(x, e) => {
        if let Some(old) = inst.remove(&x) {
          let r = term!(self, L x (self.inst_term(inst, e)));
          inst.insert(x, old);
          r
        } else { term!(self, L x (self.inst_term_simple(inst, e))) }
      }
    }
  }

  fn inst_term(&mut self, inst: &mut HashMap<VarId, TermId>, tm: TermId) -> TermId {
    if inst.is_empty() { tm } else { self.inst_term_simple(inst, tm) }
  }

  fn inst_term_from(&mut self, inst: &[(VarId, TermId)], tm: TermId) -> TermId {
    let mut map = HashMap::new();
    for &(v, t) in inst { assert!(map.insert(v, t).is_none()) }
    self.inst_term(&mut map, tm)
  }

  pub fn pp<T>(&self, t: T) -> Print<'_, Self, T> {
    self.print_with_env(Some(self.env), t)
  }

  pub fn pp_type(&self, t: TermId) -> impl std::fmt::Display + '_ {
    struct PP<'a, 'b>(&'b TermArena<'a>, TermId);
    impl std::fmt::Display for PP<'_, '_> {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.0.pp(self.1), self.0.pp(self.0.type_of(self.1)))
      }
    }
    PP(self, t)
  }
}

pub struct TermInstType<'a, 'b, S> {
  pub arena: &'b mut TermArena<'a>,
  store: &'b S,
  inst: &'b [TypeId],
  tys: &'b mut [Option<TypeId>],
  vars: &'b mut [Option<VarId>],
  tms: &'b mut [Option<TermId>],
}

impl<'a, 'b, S: HasTermStore> TermInstType<'a, 'b, S> {
  fn as_type(&mut self) -> TypeTranslator<'a, '_, S> {
    TypeTranslator {
      arena: self.arena,
      store: self.store,
      inst: self.inst,
      imported: self.tys,
    }
  }

  fn tr_type(&mut self, ty: TypeId) -> TypeId { self.as_type().tr(ty) }

  fn tr_var(&mut self, v: VarId) -> VarId {
    if let Some(i) = self.vars[v.into_usize()] { return i }
    let vd = &*self.store[v];
    let ty = self.tr_type(vd.ty);
    let n = if self.inst.is_empty() {
      if let VarName::Str(name) = &vd.name {
        self.arena.mk_var_id(name.clone(), ty)
      } else {
        self.arena.mk_genvar(ty)
      }
    } else {
      let vars = &*self.vars;
      self.arena.mk_var_avoiding(&vd.name, ty, |v| vars.contains(&Some(v)))
    };
    self.vars[v.into_usize()] = Some(n);
    n
  }

  fn tr_term(&mut self, tm: TermId) -> TermId {
    if let Some(i) = self.tms[tm.into_usize()] { return i }
    let n = match *self.store[tm].clone() {
      Term::Var(x) => term!(self.arena, V(self.tr_var(x))),
      Term::Const(c, ref tyargs) => {
        let mut trty = self.as_type();
        term!(self.arena, K(c, tyargs.iter().map(|&ty| trty.tr(ty)).collect()))
      }
      Term::App(f, x) => term!(self.arena, A (self.tr_term(f)) (self.tr_term(x))),
      Term::Lam(x, e) => term!(self.arena, L {self.tr_var(x)} (self.tr_term(e))),
    };
    self.tms[tm.into_usize()] = Some(n);
    n
  }
}

struct CollectTyVarsType {
  vars: Vec<TypeId>,
  visited: BitBox,
}

impl CollectTyVarsType {
  fn new(arena: &TypeArena) -> Self {
    Self { vars: vec![], visited: bitbox![0; arena.types().len()] }
  }

  fn collect(&mut self, arena: &TypeArena, ty: TypeId) {
    if self.visited[ty.into_usize()] { return }
    match *arena[ty] {
      Type::Var(_) => self.vars.push(ty),
      Type::Const(_, ref args) => for &ty in args { self.collect(arena, ty) }
    }
    self.visited.set(ty.into_usize(), true)
  }

  fn apply(&self, store: &mut TypeStore) -> Vec<TyVarId> {
    self.vars.iter().enumerate().map(|(i, &v)| {
      let r = std::mem::replace(
        &mut store.0 .0[v.into_usize()].0,
        Rc::new(Type::Var(TyVarId(i as u32))));
      if let Type::Var(v) = *r { v } else { unreachable!() }
    }).collect()
  }
}

struct CollectTyVarsTerm {
  pub c: CollectTyVarsType,
  visited: BitBox,
}

impl CollectTyVarsTerm {
  fn new(arena: &TermArena) -> Self {
    Self {
      c: CollectTyVarsType::new(&arena.tys),
      visited: bitbox![0; arena.terms().len()]
    }
  }

  fn collect(&mut self,  arena: &TermArena, tm: TermId) {
    if self.visited[tm.into_usize()] { return }
    let t = &arena.tms[tm];
    match *t.0 {
      Term::Var(_) | Term::Const(_, _) => self.c.collect(&arena.tys, t.1),
      Term::App(a, b) => { self.collect(arena, a); self.collect(arena, b) }
      Term::Lam(v, t) => {
        self.c.collect(&arena.tys, arena[v].ty);
        self.collect(arena, t)
      }
    }
    self.visited.set(tm.into_usize(), true)
  }
}

// #[derive(Debug, Hash, PartialEq, Eq)]
// pub enum Proof {
//   Fetch(ThmId, Vec<TypeId>),
//   AddAsm(TermId, ProofId),
//   Alpha(TermId, TermId),
//   AlphaLink(ProofId, TermId),
//   AlphaConv(TermId, TermId),
//   Assume(TermId),
//   Beta(TermId),
//   CContr(TermId, ProofId),
//   Choose(TermId, ProofId, ProofId),
//   Conj(ProofId, ProofId),
//   Conj1(ProofId),
//   Conj2(ProofId),
//   Contr(TermId, ProofId),
//   DeductAntiSym(ProofId, ProofId),
//   Disch(TermId, ProofId),
//   Disj1(ProofId, TermId),
//   Disj2(TermId, ProofId),
//   DisjCases(ProofId, ProofId, ProofId),
//   EqfElim(ProofId),
//   EqfIntro(ProofId),
//   EqImp1(ProofId),
//   EqImp2(ProofId),
//   EqMp(ProofId, ProofId),
//   EqtElim(ProofId),
//   EqtIntro(ProofId),
//   Eta(TermId),
//   Exists(TermId, TermId, ProofId),
//   Gen(TermId, ProofId),
//   ImpAntiSym(ProofId, ProofId),
//   ImpTrans(ProofId, ProofId),
//   Inst(Vec<(TermId, TermId)>, ProofId),
//   InstType(Vec<(TypeId, TypeId)>, ProofId),
//   Mp(ProofId, ProofId),
//   NotElim(ProofId),
//   NotIntro(ProofId),
//   ProveAsm(ProofId, ProofId),
//   Refl(TermId),
//   SelectRule(ProofId),
//   Spec(TermId, ProofId),
//   Subs(Vec<ProofId>, ProofId),
//   SubsConv(Vec<ProofId>, TermId),
//   Subst(Vec<(TermId, ProofId)>, TermId, ProofId),
//   SubstConv(Vec<(TermId, ProofId)>, TermId, TermId),
//   Sym(ProofId),
//   SymConv(TermId),
//   Trans(ProofId, ProofId),
//   Undisch(ProofId),
//   Quant(Quant, TermId, ProofId),
//   App(ProofId, ProofId),
//   App1(ProofId, TermId),
//   App2(TermId, ProofId),
//   Bin(Binary, ProofId, ProofId),
//   Bin1(Binary, ProofId, TermId),
//   Bin2(Binary, TermId, ProofId),
//   Not(ProofId),
//   NumConv(NumOp, TermId),
// }

#[derive(Debug)]
pub struct ProofTrace;

#[derive(Default, Debug, Hash, PartialEq, Eq)]
pub struct Hyps(Box<[TermId]>);

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
struct UnionHyps(Rc<Hyps>);

impl UnionHyps {
  fn new(arena: &ProofArena<'_>) -> Self { Self(arena[HypsId::EMPTY].clone()) }

  fn insert(&mut self, arena: &impl HasProofStore, hyps: HypsId) {
    if hyps == HypsId::EMPTY { return }
    let other = &arena[hyps];
    if self.0 .0.is_empty() { return self.0 = other.clone() }
    if other.is_subset(arena, &self.0) { return }
    if self.0.is_subset(arena, other) { return self.0 = other.clone() }
    self.0 = Rc::new(self.0.union(arena, other));
  }

  fn finish(self, arena: &mut ProofArena<'_>) -> HypsId { arena.hyps.add_inner(self.0, ()).0 }
}

#[derive(Debug, Default, Hash, PartialEq, Eq)]
pub struct Proof {
  hyps: HypsId,
  concl: TermId,
}

pub struct ProofStore {
  pub tms: TermStore,
  pub hyps: Store<Hyps>,
  pub pfs: Store<Proof, ProofTrace>,
}

pub trait HasProofStore:
  HasTermStore +
  Index<HypsId, Output=Rc<Hyps>> +
  Index<ProofId, Output=Rc<Proof>>
{
  fn hyps_store(&self) -> &Store<Hyps>;
  fn proof_store(&self) -> &Store<Proof, ProofTrace>;

  fn hyps(&self) -> &[(Rc<Hyps>, ())] { &self.hyps_store().0 }

  fn proofs(&self) -> &[(Rc<Proof>, ProofTrace)] { &self.proof_store().0 }

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

  fn add(&mut self, hyps: HypsId, concl: TermId) -> ProofId {
    self.pfs.add_val(Proof {hyps, concl}, ProofTrace)
  }

  fn add0(&mut self, concl: TermId) -> ProofId {
    self.add(HypsId::EMPTY, concl)
  }

  pub fn new(env: &'a Environment) -> Self {
    let mut hyps = Dedup::default();
    hyps.add(Hyps::default());
    Self { tms: TermArena::new(env), pfs: Dedup::default(), hyps }
  }

  pub fn pp(&self, th: ProofId) -> impl std::fmt::Display + '_ {
    struct PP<'a, 'b>(&'b TermArena<'a>, &'b [TermId], TermId);
    impl std::fmt::Display for PP<'_, '_> {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for &hyp in self.1 {
          write!(f, "{},\n", self.0.pp(hyp))?
        }
        write!(f, "|- {}", self.0.pp(self.2))
      }
    }
    let Proof {hyps, concl} = *self[th];
    PP(self, &*self[hyps].0, concl)
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

  pub fn axiom(&mut self, hyps: Vec<TermId>, concl: TermId) -> ProofId {
    let hyps = self.hyps_from_vec(hyps);
    self.add(hyps, concl)
  }

  pub fn fetch(&mut self, th: ThmId, tys: Vec<TypeId>) -> ProofId {
    let d = &self.env[th];
    assert_eq!(d.tyvars as usize, tys.len());
    let (trtys, trvars, trtms) = self.inst_type_store(&tys, &d.arena);
    let hyps = d.hyps.iter().map(|&tm| {
      self.tms.subst_term_once(&trtys, &trvars, &trtms, &*d.arena[tm])
    }).collect();
    let hyps = self.hyps_from_vec(hyps);
    let concl = self.tms.subst_term_once(&trtys, &trvars, &trtms, &*d.arena[d.concl]);
    self.add(hyps, concl)
  }

  pub fn add_asm(&mut self, tm: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    if let Some(hyps) = self[hyps].insert(&self.tms, tm) {
      thm!(self, add(self.hyps.add(hyps), concl))
    } else { th }
  }

  pub fn alpha(&mut self, tm1: TermId, tm2: TermId) -> ProofId {
    assert!(self.alpha_eq(tm1, tm2));
    thm!(self, add0(tm1 = tm2))
  }

  pub fn alpha_link0(&mut self, th: ProofId, concl2: TermId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    assert!(self.alpha_eq(concl, concl2));
    assert_eq!(hyps, HypsId::EMPTY);
    self.add0(concl2)
  }

  pub fn alpha_conv(&mut self, tm1: TermId, tm2: TermId) -> ProofId {
    let y = self.dest_var(tm1);
    let (x, t) = self.dest_lam(tm2);
    let t2 = self.inst_term_from(&[(x, tm1)], t);
    thm!(self, add0(tm2 = (L y t2)))
  }

  pub fn assume(&mut self, tm: TermId) -> ProofId {
    assert!(self.is_boolean(tm));
    let hyps = self.hyps.add(Hyps::one(tm));
    self.add(hyps, tm)
  }

  pub fn beta(&mut self, tm: TermId) -> ProofId {
    let (t, s) = self.dest_app(tm);
    let (x, t) = self.dest_lam(t);
    let t2 = self.inst_term_from(&[(x, s)], t);
    let th = term!(self, tm = t2); self.add0(th)
  }

  pub fn ccontr(&mut self, tm: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    self.dest_const(ConstId::FALSE, concl);
    let neg = self.mk_not(tm);
    thm!(self, add(self.remove_hyp(hyps, neg), tm))
  }

  pub fn choose(&mut self, tm: TermId, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: th1} = *self[th1];
    let Proof {hyps: h2, concl: th2} = *self[th2];
    let (x, p) = self.dest_exists(th1);
    let p2 = self.inst_term_from(&[(x, tm)], p);
    let h2 = self.remove_hyp(h2, p2);
    thm!(self, add(self.union_hyps(h1, h2), th2))
  }

  pub fn conj(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: th1} = *self[th1];
    let Proof {hyps: h2, concl: th2} = *self[th2];
    thm!(self, add(self.union_hyps(h1, h2), {self.mk_conj(th1, th2)}))
  }

  pub fn conj1(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (a, _) = self.dest_conj(concl);
    thm!(self, add(hyps, a))
  }

  pub fn conj2(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (_, b) = self.dest_conj(concl);
    thm!(self, add(hyps, b))
  }

  pub fn contr(&mut self, tm: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    self.dest_const(ConstId::FALSE, concl);
    assert!(self.is_boolean(tm));
    thm!(self, add(hyps, tm))
  }

  pub fn deduct_antisym(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: p} = *self[th1];
    let Proof {hyps: h2, concl: q} = *self[th2];
    let h1 = self.remove_hyp(h1, q);
    let h2 = self.remove_hyp(h2, p);
    thm!(self, add(self.union_hyps(h1, h2), p = q))
  }

  pub fn disch(&mut self, p: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl: q} = *self[th];
    thm!(self, add(self.remove_hyp(hyps, p), p => q))
  }

  pub fn disj1(&mut self, th: ProofId, q: TermId) -> ProofId {
    let Proof {hyps, concl: p} = *self[th];
    thm!(self, add(hyps, {self.mk_disj(p, q)}))
  }

  pub fn disj2(&mut self, p: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl: q} = *self[th];
    thm!(self, add(hyps, {self.mk_disj(p, q)}))
  }

  pub fn disj_cases(&mut self, th1: ProofId, th2: ProofId, th3: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th1];
    let (p, q) = self.dest_disj(concl);
    let Proof {hyps: h1, concl: r1} = *self[th2];
    let Proof {hyps: h2, concl: r2} = *self[th3];
    assert_eq!(r1, r2);
    let h1 = self.remove_hyp(h1, p);
    let h2 = self.remove_hyp(h2, q);
    let h12 = self.union_hyps(h1, h2);
    thm!(self, add(self.union_hyps(hyps, h12), r1))
  }

  pub fn eqf_elim(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, fal) = self.dest_eq(concl);
    self.dest_const(ConstId::FALSE, fal);
    thm!(self, add(hyps, {self.mk_not(p)}))
  }

  pub fn eqf_intro(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    thm!(self, add(hyps, {self.dest_not(concl)} = {self.mk_false()}))
  }

  pub fn eq_imp1(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, q) = self.dest_eq(concl);
    thm!(self, add(hyps, p => q))
  }

  pub fn eq_imp2(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, q) = self.dest_eq(concl);
    thm!(self, add(hyps, q => p))
  }

  pub fn eq_mp(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: th1} = *self[th1];
    let Proof {hyps: h2, concl: th2} = *self[th2];
    let (p, q) = self.dest_eq(th1);
    if !self.alpha_eq(p, th2) {
      panic!("eq_mp: mismatch\n  left: {}\n right: {}", self.tms.pp(p), self.tms.pp(th2));
    }
    thm!(self, add(self.union_hyps(h1, h2), q))
  }

  pub fn eqt_elim(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, tru) = self.dest_eq(concl);
    self.dest_const(ConstId::TRUE, tru);
    thm!(self, add(hyps, p))
  }

  pub fn eqt_intro(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    thm!(self, add(hyps, concl = {self.mk_true()}))
  }

  pub fn eta(&mut self, tm: TermId) -> ProofId {
    let (x, f) = self.dest_lam(tm);
    let (f, x2) = self.dest_app(f);
    assert_eq!(x, self.dest_var(x2));
    thm!(self, add0(tm = f))
  }

  pub fn exists(&mut self, tm: TermId, t: TermId, th: ProofId) -> ProofId {
    let (x, p) = self.dest_exists(tm);
    let Proof {hyps, concl} = *self[th];
    assert_eq!(self.inst_term_from(&[(x, t)], p), concl);
    thm!(self, add(hyps, tm))
  }

  pub fn gen(&mut self, x: VarId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    thm!(self, add(hyps, {self.mk_forall(x, concl)}))
  }

  pub fn imp_antisym(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: th1} = *self[th1];
    let Proof {hyps: h2, concl: th2} = *self[th2];
    let (p, q) = self.dest_imp(th1);
    let (q2, p2) = self.dest_imp(th2);
    assert_eq!((p, q), (p2, q2));
    thm!(self, add(self.union_hyps(h1, h2), p = q))
  }

  pub fn imp_trans(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: th1} = *self[th1];
    let Proof {hyps: h2, concl: th2} = *self[th2];
    let (p, q) = self.dest_imp(th1);
    let (q2, r) = self.dest_imp(th2);
    assert_eq!(q, q2);
    thm!(self, add(self.union_hyps(h1, h2), p => r))
  }

  pub fn inst(&mut self, inst: &[(VarId, TermId)], th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let hyps = if hyps == HypsId::EMPTY { hyps } else {
      let hyps = self[hyps].clone().0.iter().map(|&h| self.inst_term_from(inst, h)).collect();
      self.hyps_from_vec(hyps)
    };
    thm!(self, add(hyps, self.inst_term_from(inst, concl)))
  }

  pub fn inst_type(&mut self, inst: &[(TyVarId, TypeId)], th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let mut a = ProofArena::new(self.env);
    let mut hyps = Vec::from(&*self[hyps].0);
    let concl = a.import(self, |mut tr| {
      for h in &mut hyps { *h = tr.tr_term(*h) }
      tr.tr_term(concl)
    });
    let a = a.into_store();
    let n = inst.iter().map(|p| p.0 .0).max().map_or(0, |n| n+1);
    let mut vec = (0..n).map(|v| self.tys.mk_var(TyVarId(v))).collect::<Vec<_>>();
    for &(v, ty) in inst { vec[v.0 as usize] = ty };
    let trtms = self.inst_type_store(&vec, &a.tms).2;
    for h in &mut hyps { *h = trtms[h.into_usize()] }
    thm!(self, add(self.hyps_from_vec(hyps), trtms[concl.into_usize()]))
  }

  pub fn mp(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: th1} = *self[th1];
    let Proof {hyps: h2, concl: th2} = *self[th2];
    let (p, q) = self.dest_imp(th1);
    assert_eq!(p, th2);
    thm!(self, add(self.union_hyps(h1, h2), q))
  }

  pub fn not_elim(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    thm!(self, add(hyps, {self.dest_not(concl)} => {self.mk_false()}))
  }

  pub fn not_intro(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, fal) = self.dest_imp(concl);
    self.dest_const(ConstId::FALSE, fal);
    thm!(self, add(hyps, {self.mk_not(p)}))
  }

  pub fn prove_asm(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: p} = *self[th1];
    let Proof {hyps: h2, concl: q} = *self[th2];
    let h2 = self.remove_hyp(h2, p);
    thm!(self, add(self.union_hyps(h1, h2), q))
  }

  pub fn refl(&mut self, tm: TermId) -> ProofId {
    thm!(self, add0(tm = tm))
  }

  pub fn select_rule(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (x, p) = self.dest_exists(concl);
    let sel = self.mk_select(x, p);
    thm!(self, add(hyps, self.inst_term_from(&[(x, sel)], p)))
  }

  pub fn spec(&mut self, tm: TermId, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (x, p) = self.dest_forall(concl);
    thm!(self, add(hyps, self.inst_term_from(&[(x, tm)], p)))
  }

  pub fn subs_conv(&mut self, inst: SubsInst, a: TermId) -> ProofId {
    let b = inst.apply(self, a);
    if a == b { return self.refl(a) }
    thm!(self, add(inst.hyps.finish(self), a = b))
  }

  pub fn subs(&mut self, inst: SubsInst, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let b = inst.apply(self, concl);
    if concl == b { return th }
    let hyps1 = inst.hyps.finish(self);
    thm!(self, add(self.union_hyps(hyps1, hyps), b))
  }

  fn subst_core(&mut self, vths: &[(VarId, ProofId)], tm: TermId) -> (UnionHyps, TermId, TermId) {
    let (mut map1, mut map2) = (HashMap::new(), HashMap::new());
    let mut hyps = UnionHyps::new(self);
    for &(v, th) in vths {
      let Proof {hyps: h, concl} = *self[th];
      let (a, b) = self.dest_eq(concl);
      map1.insert(v, a);
      map2.insert(v, b);
      hyps.insert(self, h)
    }
    (hyps, self.inst_term(&mut map1, tm), self.inst_term(&mut map2, tm))
  }

  pub fn subst_conv(&mut self, vths: &[(VarId, ProofId)], tmp: TermId, tm: TermId) -> ProofId {
    let (hyps, lhs, rhs) = self.subst_core(vths, tmp);
    assert!(self.alpha_eq(lhs, tm));
    thm!(self, add(hyps.finish(self), tm = rhs))
  }

  pub fn subst(&mut self, vths: &[(VarId, ProofId)], tmp: TermId, th: ProofId) -> ProofId {
    let (mut u, lhs, rhs) = self.subst_core(vths, tmp);
    let Proof {hyps, concl} = *self[th];
    u.insert(self, hyps);
    assert!(self.alpha_eq(lhs, concl));
    thm!(self, add(u.finish(self), rhs))
  }

  pub fn sym(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (t1, t2) = self.dest_eq(concl);
    thm!(self, add(hyps, t2 = t1))
  }

  pub fn sym_conv(&mut self, tm: TermId) -> ProofId {
    let (t1, t2) = self.dest_eq(tm);
    thm!(self, add0((t1 = t2) = (t2 = t1)))
  }

  pub fn trans(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    let Proof {hyps: h1, concl: th1} = *self[th1];
    let Proof {hyps: h2, concl: th2} = *self[th2];
    let (a, b) = self.dest_eq(th1);
    let (b2, c) = self.dest_eq(th2);
    if !self.alpha_eq(b, b2) {
      panic!("trans: mismatch\n  left: {}\n right: {}", self.tms.pp(th1), self.tms.pp(th2));
    }
    thm!(self, add(self.union_hyps(h1, h2), a = c))
  }

  pub fn undisch(&mut self, th: ProofId) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (p, q) = self.dest_imp(concl);
    thm!(self, add(self.insert_hyp(hyps, p), q))
  }
  #[inline] fn mk_eq_fn1(&mut self, th: ProofId,
    mut f: impl FnMut(&mut Self, TermId) -> TermId
  ) -> ProofId {
    let Proof {hyps, concl} = *self[th];
    let (l, r) = self.dest_eq(concl);
    thm!(self, add(hyps, {f(self, l)} = {f(self, r)}))
  }
  #[inline] fn mk_eq_fn2(&mut self, th1: ProofId, th2: ProofId,
    mut f: impl FnMut(&mut Self, TermId, TermId) -> TermId
  ) -> ProofId {
    let Proof {hyps: h1, concl: th1} = *self[th1];
    let Proof {hyps: h2, concl: th2} = *self[th2];
    let (l1, r1) = self.dest_eq(th1);
    let (l2, r2) = self.dest_eq(th2);
    thm!(self, add(self.union_hyps(h1, h2), {f(self, l1, l2)} = {f(self, r1, r2)}))
  }

  pub fn eq_lam(&mut self, x: VarId, th: ProofId) -> ProofId {
    self.mk_eq_fn1(th, |this, t| this.mk_lam(x, t))
  }

  pub fn eq_binder(&mut self, b: ConstId, x: VarId, th: ProofId) -> ProofId {
    self.mk_eq_fn1(th, |this, t| this.mk_binder(b, x, t))
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
    self.mk_eq_fn2(th1, th2, |this, t1, t2| this.mk_app(t1, t2))
  }

  pub fn eq_app1(&mut self, th: ProofId, tm: TermId) -> ProofId {
    self.mk_eq_fn1(th, |this, t| this.mk_app(t, tm))
  }

  pub fn eq_app2(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.mk_eq_fn1(th, |this, t| this.mk_app(tm, t))
  }

  pub fn eq_bin(&mut self, f: TermId, th1: ProofId, th2: ProofId) -> ProofId {
    self.mk_eq_fn2(th1, th2, |this, t1, t2| this.mk_app2(f, t1, t2))
  }

  pub fn eq_bin1(&mut self, f: TermId, th: ProofId, tm: TermId) -> ProofId {
    self.mk_eq_fn1(th, |this, t| this.mk_app2(f, t, tm))
  }

  pub fn eq_bin2(&mut self, f: TermId, tm: TermId, th: ProofId) -> ProofId {
    self.mk_eq_fn1(th, |this, t| this.mk_app2(f, tm, t))
  }

  pub fn eq_binary(&mut self, b: Binary, x: ProofId, y: ProofId) -> ProofId {
    self.mk_eq_fn2(x, y, |this, x, y| this.mk_binary(b, x, y))
  }

  pub fn eq_binary1(&mut self, b: Binary, x: ProofId, y: TermId) -> ProofId {
    self.mk_eq_fn1(x, |this, x| this.mk_binary(b, x, y))
  }

  pub fn eq_binary2(&mut self, b: Binary, x: TermId, y: ProofId) -> ProofId {
    self.mk_eq_fn1(y, |this, y| this.mk_binary(b, x, y))
  }

  pub fn eq_not(&mut self, th: ProofId) -> ProofId {
    self.mk_eq_fn1(th, |this, x| this.mk_not(x))
  }

  pub fn eval_suc_conv(&mut self, tm: TermId) -> ProofId {
    let n = self.try_dest_unop(ConstId::SUC, tm).expect("eval_suc_conv: expected a SUC");
    let mut n = self.dest_int(n);
    n += 1u32;
    thm!(self, add0(tm = {self.mk_int(n)}))
  }

  pub fn eval_pre_conv(&mut self, tm: TermId) -> ProofId {
    let n = self.try_dest_unop(ConstId::PRE, tm).expect("eval_pre_conv: expected a PRE");
    let mut n = self.dest_int(n);
    if !n.is_zero() { n -= 1u32 }
    thm!(self, add0(tm = {self.mk_int(n)}))
  }

  pub fn eval_add_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::ADD, tm).expect("eval_add_conv: expected a +");
    let mut a = self.dest_int(a);
    let b = self.dest_int(b);
    a += b;
    thm!(self, add0(tm = {self.mk_int(a)}))
  }

  pub fn eval_sub_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::SUB, tm).expect("eval_sub_conv: expected a -");
    let a = self.dest_int(a);
    let b = self.dest_int(b);
    let c = a.checked_sub(&b).unwrap_or_else(BigUint::zero);
    thm!(self, add0(tm = {self.mk_int(c)}))
  }

  pub fn eval_mult_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::MULT, tm).expect("eval_mult_conv: expected a *");
    let mut a = self.dest_int(a);
    let b = self.dest_int(b);
    a *= b;
    thm!(self, add0(tm = {self.mk_int(a)}))
  }

  pub fn eval_exp_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::EXP, tm).expect("eval_exp_conv: expected an EXP");
    let a = self.dest_int(a);
    let b = self.dest_int(b);
    let c = a.pow(b.try_into().expect("eval_exp_conv: too big"));
    thm!(self, add0(tm = {self.mk_int(c)}))
  }

  pub fn eval_even_conv(&mut self, tm: TermId) -> ProofId {
    let n = self.try_dest_unop(ConstId::EVEN, tm).expect("eval_even_conv: expected an EVEN");
    let n = self.dest_int(n);
    thm!(self, add0(tm = {self.mk_bool_lit(!n.bit(0))}))
  }

  pub fn eval_odd_conv(&mut self, tm: TermId) -> ProofId {
    let n = self.try_dest_unop(ConstId::ODD, tm).expect("eval_odd_conv: expected an ODD");
    let n = self.dest_int(n);
    thm!(self, add0(tm = {self.mk_bool_lit(n.bit(0))}))
  }

  pub fn eval_eq_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.dest_eq(tm);
    let a = self.dest_int(a);
    let b = self.dest_int(b);
    thm!(self, add0(tm = {self.mk_bool_lit(a == b)}))
  }

  pub fn eval_lt_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::LT, tm).expect("eval_lt_conv: expected a <");
    let a = self.dest_int(a);
    let b = self.dest_int(b);
    thm!(self, add0(tm = {self.mk_bool_lit(a < b)}))
  }

  pub fn eval_le_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::LE, tm).expect("eval_le_conv: expected a <=");
    let a = self.dest_int(a);
    let b = self.dest_int(b);
    thm!(self, add0(tm = {self.mk_bool_lit(a <= b)}))
  }

  pub fn eval_gt_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::GT, tm).expect("eval_gt_conv: expected a >");
    let a = self.dest_int(a);
    let b = self.dest_int(b);
    thm!(self, add0(tm = {self.mk_bool_lit(a > b)}))
  }

  pub fn eval_ge_conv(&mut self, tm: TermId) -> ProofId {
    let (a, b) = self.try_dest_bin(ConstId::GE, tm).expect("eval_ge_conv: expected a >=");
    let a = self.dest_int(a);
    let b = self.dest_int(b);
    thm!(self, add0(tm = {self.mk_bool_lit(a >= b)}))
  }
}

#[derive(Debug)]
pub struct SubsInst {
  map: HashMap<TermId, TermId>,
  hyps: UnionHyps,
  vars: HashSet<VarId>,
}

impl SubsInst {
  pub fn new(arena: &ProofArena<'_>) -> Self {
    Self { map: HashMap::new(), hyps: UnionHyps::new(arena), vars: HashSet::new() }
  }

  pub fn push(&mut self, arena: &impl HasProofStore, th: ProofId) {
    let Proof {hyps, concl} = *arena[th];
    let (a, b) = arena.dest_eq(concl);
    if a != b {
      self.map.entry(a).or_insert(b);
      let temp = &mut Default::default();
      arena.frees(&mut self.vars, temp, a);
      arena.frees(&mut self.vars, temp, b);
      self.hyps.insert(arena, hyps)
    }
  }

  fn apply(&self, arena: &mut ProofArena<'_>, a: TermId) -> TermId {
    if let Some(&b) = self.map.get(&a) { return b }
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
  pub tyvars: u32,
  pub ty: TypeId,
}

#[derive(Debug, Clone)]
pub struct OwnedTerm {
  pub arena: TermStore,
  pub tyvars: u32,
  pub term: TermId
}

impl OwnedType {
  pub fn with<'a>(env: &'a Environment, f: impl FnOnce(&mut TypeArena<'a>) -> TypeId) -> (OwnedType, Vec<TyVarId>) {
    let mut a = TypeArena::new(env);
    let ty = f(&mut a);
    let mut c = CollectTyVarsType::new(&a);
    c.collect(&a, ty);
    let mut arena = a.into_store();
    let vec = c.apply(&mut arena);
    (OwnedType {arena, tyvars: vec.len() as u32, ty}, vec)
  }
}

impl OwnedTerm {
  pub fn with_and<'a, R>(env: &'a Environment,
    f: impl FnOnce(&mut TermArena<'a>) -> (TermId, R)
  ) -> ((OwnedTerm, Vec<TyVarId>), R) {
    let mut a = TermArena::new(env);
    let (term, r) = f(&mut a);
    let mut c = CollectTyVarsTerm::new(&a);
    c.collect(&a, term);
    let mut arena = a.into_store();
    let vec = c.c.apply(&mut arena.tys);
    ((OwnedTerm {arena, tyvars: vec.len() as u32, term}, vec), r)
  }

  pub fn with<'a>(env: &'a Environment, f: impl FnOnce(&mut TermArena<'a>) -> TermId) -> (OwnedTerm, Vec<TyVarId>) {
    Self::with_and(env, |a| (f(a), ())).0
  }
}

impl ThmDef {
  pub fn with_and<'a, R, S>(env: &'a Environment,
    f: impl FnOnce(&mut ProofArena<'a>) -> (ProofId, R),
    tr_r: impl FnOnce(TermInstType<TermStore>, R) -> S,
  ) -> ((ThmDef, Vec<TyVarId>), S) {
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
    let mut arena = a.into_store();
    let vec = c.c.apply(&mut arena.tys);
    let tyvars = vec.len() as u32;
    ((ThmDef { arena, tyvars, hyps, concl }, vec), r)
  }

  pub fn with<'a>(env: &'a Environment, f: impl FnOnce(&mut ProofArena<'a>) -> ProofId) -> (ThmDef, Vec<TyVarId>) {
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

#[derive(Debug, Default)]
pub struct Environment {
  pub tyops: Vec<TyopDef>,
  pub consts: Vec<ConstDef>,
  pub thms: Vec<ThmDef>,
  pub trans: TransTable,
  pub counts: HashMap<&'static str, (u32, u32)>,
}

impl Index<TyopId> for Environment {
  type Output = TyopDef;
  fn index(&self, n: TyopId) -> &Self::Output { &self.tyops[n.into_usize()] }
}
impl Index<ConstId> for Environment {
  type Output = ConstDef;
  fn index(&self, n: ConstId) -> &Self::Output { &self.consts[n.into_usize()] }
}
impl Index<ThmId> for Environment {
  type Output = ThmDef;
  fn index(&self, n: ThmId) -> &Self::Output { &self.thms[n.into_usize()] }
}

impl Environment {
  pub fn add_tyop<'a>(&mut self,
    name: impl Into<Cow<'a, str>>, arity: u32, tydef: Option<ThmId>
  ) -> TyopId {
    let n = Idx::from(self.tyops.len() as u32);
    let name = name.into().into_owned();
    self.tyops.push(TyopDef {name: name.clone(), arity, tydef});
    assert!(self.trans.tyops.insert(name, n).is_none());
    n
  }

  pub fn add_const<'a>(&mut self, name: impl Into<Cow<'a, str>>, ty: OwnedType) -> ConstId {
    let n = Idx::from(self.consts.len() as u32);
    let name = name.into().into_owned();
    self.consts.push(ConstDef {name: name.clone(), ty});
    assert!(self.trans.consts.insert(name, n).is_none());
    n
  }

  pub fn add_anon_thm<'a>(&mut self, d: ThmDef) -> ThmId {
    let n = Idx::from(self.thms.len() as u32);
    self.thms.push(d);
    n
  }

  pub fn add_thm_alias<'a>(&mut self, k: FetchKind, name: impl Into<Cow<'a, str>>, th: ThmId) {
    assert!(self.trans.fetches[k].insert(name.into().into_owned(), th).is_none());
  }

  pub fn add_thm<'a>(&mut self, k: FetchKind, name: impl Into<Cow<'a, str>>, d: ThmDef) -> ThmId {
    let n = self.add_anon_thm(d);
    self.add_thm_alias(k, name, n);
    n
  }

  pub fn add_type_bijs<'a>(&mut self, c: TyopId, cname: &str,
    abs: impl Into<Cow<'a, str>>, rep: impl Into<Cow<'a, str>>
  ) -> (ConstId, ConstId, ThmId, ThmId) {
    let abs = abs.into(); let rep = rep.into();
    let exists_p = *self.tyops[c.into_usize()].tydef
      .as_ref().expect("add_type_bijs: not a type operator");
    let ThmDef {arena: ref store, concl, ..} = self.thms[exists_p.into_usize()];
    let (p, v) = store.dest_app(store.dest_exists(concl).1);
    let ty = store.type_of(v);
    let (absc, _) = OwnedType::with(self, |a| {
      // abs[v0..vn]: A -> C[v0..vn]
      let aty = a.import(&store.tys, |mut tr| tr.tr(ty));
      let cty = a.mk_const_upto(c);
      ty!(a, aty -> cty)
    });
    let absc = self.add_const(&*abs, absc);
    let store = &self.thms[exists_p.into_usize()].arena;
    let (repc, _) = OwnedType::with(self, |a| {
      // rep[v0..vn]: C[v0..vn] -> A
      let aty = a.import(&store.tys, |mut tr| tr.tr(ty));
      let cty = a.mk_const_upto(c);
      ty!(a, cty -> aty)
    });
    let repc = self.add_const(&*rep, repc);
    let (abs_rep, _) = ThmDef::with(self, |a| {
      let t = &mut a.tms;
      let abs = t.mk_const_upto(absc);
      let rep = t.mk_const_upto(repc);
      let (v, va) = t.mk_var_term("a".into(), t.dest_fun(t.type_of(abs)).1);
      // |- !a: C. abs (rep a) = a
      let concl = term!(t, !v. (A abs (A rep va)) = va);
      a.add0(concl)
    });
    let abs_rep = self.add_thm(FetchKind::TypeBij1, cname, abs_rep);
    let store = &self.thms[exists_p.into_usize()].arena;
    let (rep_abs, _) = ThmDef::with(self, |a| {
      let t = &mut a.tms;
      let abs = t.mk_const_upto(absc);
      let rep = t.mk_const_upto(repc);
      let p = t.import(store, |mut tr| tr.tr_term(p));
      let (v, vr) = t.mk_var_term("r".into(), t.dest_fun(t.type_of(abs)).0);
      // |- !r: A. P r <=> rep (abs r) = r
      let concl = term!(t, !v. (A p vr) = ((A rep (A abs vr)) = vr));
      a.add0(concl)
    });
    let rep_abs = self.add_thm(FetchKind::TypeBij2, cname, rep_abs);
    (absc, repc, abs_rep, rep_abs)
  }

  pub fn add_basic_def<'a>(&mut self, x: impl Into<Cow<'a, str>>, tm: OwnedTerm
  ) -> (ConstId, ThmId) {
    let x = x.into();
    let (ty, args) = OwnedType::with(self, |a| {
      a.import(&tm.arena, |mut tr| tr.tr(tm.arena.type_of(tm.term)))
    });
    let c = self.add_const(&*x, ty);
    let (th, _) = ThmDef::with(self, |a| {
      let args = args.into_iter().map(|v| a.tys.mk_var(v)).collect();
      thm!(a, add0({a.mk_const(c, args)} = {a.import(&tm.arena, |mut tr| tr.tr_term(tm.term))}))
    });
    (c, self.add_thm(FetchKind::BasicDef, x, th))
  }

  pub fn add_simple_def<'a>(&mut self, x: impl Into<Cow<'a, str>>, arity: u32, tm: OwnedTerm
  ) -> (ConstId, ThmId) {
    let x = x.into();
    let (c, th) = self.add_basic_def(&*x, tm);
    if arity == 0 {
      self.add_thm_alias(FetchKind::Def, x, th);
      (c, th)
    } else {
      let ThmDef {ref arena, concl, ..} = self[th];
      let (th, _) = ThmDef::with(self, |a| {
        let concl = a.import(arena, |mut tr| {
          let (lhs, mut rhs) = arena.dest_eq(concl);
          let mut lhs = tr.tr_term(lhs);
          let mut stk = vec![];
          for _ in 0..arity {
            let (x, e) = arena.dest_lam(rhs);
            let x = tr.tr_var(x);
            lhs = term!(tr.arena, A lhs (V(x)));
            stk.push(x);
            rhs = e;
          }
          let mut concl = term!(tr.arena, lhs = {tr.tr_term(rhs)});
          for x in stk.into_iter().rev() {
            concl = tr.arena.mk_forall(x, concl)
          }
          concl
        });
        a.add0(concl)
      });
      (c, self.add_thm(FetchKind::Def, x, th))
    }
  }

  pub fn add_def<'a>(&mut self, x: impl Into<Cow<'a, str>>,
    OwnedTerm {arena: old, term, ..}: OwnedTerm) -> (ConstId, ThmId) {
    fn untuple(e: TermId, old: &TermStore, gv: TermId,
      tr: &mut TermInstType<'_, '_, TermStore>,
      visit: &mut impl FnMut(VarId, VarId, TermId),
    ) {
      if let Some((e1, e2)) = old.try_dest_pair(e) {
        untuple(e1, old, tr.arena.mk_fst(gv), tr, visit);
        untuple(e2, old, tr.arena.mk_snd(gv), tr, visit);
      } else {
        let v = old.dest_var(e);
        visit(v, tr.tr_var(v), gv)
      }
    }
    let x = x.into();
    let (vs2, body) = old.strip_forall(term);
    let (lhs, rhs) = old.dest_eq(body);
    let (head, args) = old.strip_app(lhs);
    assert!(matches!(old[old.dest_var(head)].name, VarName::Str(ref n) if **n == *x));
    let mut vs1 = vec![];
    let (tm, tys) = OwnedTerm::with(self, |a| a.import(&old, |mut tr| {
      let mut subst = HashMap::new();
      let gvs = args.iter().map(|&e| {
        let ty = tr.tr_type(old.type_of(e));
        let (gv, gt) = tr.arena.mk_genvar_term(ty);
        untuple(e, &old, gt, &mut tr, &mut |oldv, v, tm| {
          assert!(subst.insert(v, tm).is_none());
          if !vs2.contains(&oldv) { vs1.push(oldv) }
        });
        gv
      }).collect::<Vec<_>>();
      let rhs = tr.tr_term(rhs);
      let mut lam = tr.arena.inst_term(&mut subst, rhs);
      for gv in gvs.into_iter().rev() { lam = tr.arena.mk_lam(gv, lam) }
      lam
    }));
    let (c, th) = self.add_basic_def(&*x, tm);
    if vs2.is_empty() && args.is_empty() {
      self.add_thm_alias(FetchKind::Def, x, th);
      (c, th)
    } else {
      let (th, _) = ThmDef::with(self, |a| {
        let tys = tys.into_iter().map(|v| a.tys.mk_var(v)).collect();
        let concl = a.import(&old, |mut tr| {
          let mut lhs = tr.arena.mk_const(c, tys);
          for e in args { lhs = term!(tr.arena, A lhs {tr.tr_term(e)}) }
          let mut concl = term!(tr.arena, lhs = {tr.tr_term(rhs)});
          for x in vs2.into_iter().rev() { concl = tr.arena.mk_forall(x, concl) }
          for x in vs1.into_iter().rev() { concl = tr.arena.mk_forall(x, concl) }
          concl
        });
        a.add0(concl)
      });
      (c, self.add_thm(FetchKind::Def, x, th))
    }
  }

  pub fn add_basic_typedef<'a>(&mut self, x: impl Into<Cow<'a, str>>, th: ThmDef) -> TyopId {
    let x = x.into();
    let arity = th.tyvars;
    let exists_p = self.add_anon_thm(th);
    self.add_tyop(&*x, arity, Some(exists_p))
  }

  pub fn add_spec<'a, T: Borrow<str>>(&mut self,
    xs: &[T], ThmDef {arena, hyps, concl, ..}: ThmDef) -> (Vec<ConstId>, ThmId) {
    assert!(hyps.is_empty());
    let mut term = concl;
    let mut subst: Vec<(VarId, ConstId, Vec<TyVarId>)> = vec![];
    for x in xs {
      let x = x.borrow();
      let (v, body) = arena.dest_exists(term);
      let (tm, args) = OwnedTerm::with(self, |a| {
        let (v, body) = a.import(&arena, |mut tr| (tr.tr_var(v), tr.tr_term(body)));
        let t = a.mk_select(v, body);
        let mut inst = subst.iter().map(|&(v, c, ref args)| {
          let args = args.iter().map(|&v| a.tys.mk_var(v)).collect();
          (v, a.mk_const(c, args))
        }).collect();
        a.inst_term(&mut inst, t)
      });
      let (c, th) = self.add_basic_def(&*x, tm);
      self.add_thm_alias(FetchKind::Def, x, th);
      subst.push((v, c, args));
      term = body;
    }
    let n = self.add_anon_thm(ThmDef::with(self, |a| {
      let t = a.import(&arena, |mut tr| tr.tr_term(term));
      let mut inst = subst.iter().map(|&(v, c, ref args)| {
        let args = args.iter().map(|&v| a.tys.mk_var(v)).collect();
        (v, a.mk_const(c, args))
      }).collect();
      let concl = a.inst_term(&mut inst, t);
      a.axiom(vec![], concl)
    }).0);
    for x in xs { self.add_thm_alias(FetchKind::Spec, x.borrow(), n) }
    (subst.into_iter().map(|p| p.1).collect(), n)
  }

  pub fn add_axiom(&mut self, x: String, OwnedTerm {arena, tyvars, term}: OwnedTerm) -> ThmId {
    assert!(arena.is_boolean(term));
    self.add_thm(FetchKind::Axiom, x, ThmDef {arena, tyvars, hyps: Box::new([]), concl: term})
  }
}
