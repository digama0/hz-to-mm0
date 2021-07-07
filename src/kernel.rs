use std::borrow::Borrow;
use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Index;
use std::ops::IndexMut;
use std::rc::Rc;
use std::borrow::Cow;
use bitvec::prelude::BitBox;
use num::{BigUint, Zero};

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
  fn add_inner(&mut self, v: H, a: A) -> (H::Idx, bool) {
    match self.map.entry(Rc::new(v)) {
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
  #[inline] fn add_val(&mut self, v: H, a: A) -> H::Idx { self.add_inner(v, a).0 }
  #[inline] fn add_default(&mut self, v: H) -> (H::Idx, bool) where A: Default {
    self.add_inner(v, A::default())
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

  fn dest_fun(&self, a: TypeId) -> (TypeId, TypeId) {
    if let Type::Const(TyopId::FUN, ref args) = *self[a] { (args[0], args[1]) }
    else { panic!("dest_fun: not a function type") }
  }

  fn types(&self) -> &[(Rc<Type>, ())] { &self.type_store().0 }
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
    let x = term!($self, $x); let t = term!($self, $t); $self.mk_lam(x, t)
  }};
  ($self:expr, $e:tt => $($e2:tt)*) => {{
    let e = term!($self, $e); let e2 = term!($self, $($e2)*); $self.mk_imp(e, e2)
  }};
  ($self:expr, $e:tt = $e2:tt) => {{
    let e = term!($self, $e); let e2 = term!($self, $e2); $self.mk_eq(e, e2)
  }};
  ($self:expr, $($e:tt)*) => { ty!($self, $($e)*) };
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

  fn inst<R>(&mut self, store: &TypeStore, inst: &[TypeId],
    f: impl FnOnce(TypeTranslator<'a, '_>) -> R
  ) -> R {
    let mut vec = vec![None; store.types().len()];
    f(TypeTranslator { arena: self, store, inst, imported: &mut vec })
  }

  fn import<R>(&mut self, store: &TypeStore,
    f: impl FnOnce(TypeTranslator<'a, '_>) -> R
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
}

pub struct TypeTranslator<'a, 'b> {
  arena: &'b mut TypeArena<'a>,
  store: &'b TypeStore,
  inst: &'b [TypeId],
  imported: &'b mut [Option<TypeId>],
}

impl<'a, 'b> TypeTranslator<'a, 'b> {
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
pub struct Var { pub name: String, pub ty: TypeId }

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
  fn dest_var(&self, x: TermId) -> VarId {
    if let Term::Var(v) = *self[x] { v } else { panic!("dest_var: not a variable") }
  }
  fn dest_app(&self, a: TermId) -> (TermId, TermId) {
    if let Term::App(a, b) = *self[a] { (a, b) }
    else { panic!("dest_app: not an application") }
  }
  fn dest_lam(&self, a: TermId) -> (VarId, TermId) {
    if let Term::Lam(a, b) = *self[a] { (a, b) }
    else { panic!("dest_lam: not a lambda") }
  }
  fn dest_binder(&self, c: ConstId, a: TermId) -> (VarId, TermId) {
    let (e, f) = self.dest_app(a);
    assert!(matches!(*self[e], Term::Const(c2, _) if c == c2), "dest_binder: not the right binder");
    self.dest_lam(f)
  }
  fn dest_forall(&self, a: TermId) -> (VarId, TermId) { self.dest_binder(ConstId::FORALL, a) }
  fn dest_exists(&self, a: TermId) -> (VarId, TermId) { self.dest_binder(ConstId::EXISTS, a) }
  fn dest_uexists(&self, a: TermId) -> (VarId, TermId) { self.dest_binder(ConstId::UEXISTS, a) }
  fn dest_select(&self, a: TermId) -> (VarId, TermId) { self.dest_binder(ConstId::SELECT, a) }

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
  conj: Option<TermId>,
  disj: Option<TermId>,
  imp: Option<TermId>,
  not: Option<TermId>,
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
      vars: Dedup::default(), tms: Dedup::default(),
      conj: None, disj: None, imp: None, not: None,
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
    self.vars.add(Var {name, ty})
  }
  pub fn mk_var_term(&mut self, x: impl Into<Cow<'a, str>>, ty: TypeId) -> (VarId, TermId) {
    let v = self.mk_var_id(x.into().into(), ty);
    (v, self.tms.add_val(Term::Var(v), ty))
  }
  pub fn mk_var(&mut self, x: VarId) -> TermId {
    self.tms.add_val(Term::Var(x), self[x].ty)
  }
  pub fn mk_const(&mut self, c: ConstId, tys: Vec<TypeId>) -> TermId {
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
    assert_eq!(a, a2, "mk_app: type mismatch");
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
  pub fn mk_eq(&mut self, x: TermId, y: TermId) -> TermId {
    let ty = self.type_of(x);
    term!(self, A (self.mk_eq_const(ty)) x y)
  }
  pub fn mk_pair(&mut self, x: TermId, y: TermId) -> TermId {
    let (tyx, tyy) = (self.type_of(x), self.type_of(y));
    term!(self, A (self.mk_pair_const(tyx, tyy)) x y)
  }
  pub fn mk_bin(&mut self, b: Binary, x: TermId, y: TermId) -> TermId {
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

  fn mk_var_avoiding(&mut self, name: String, ty: TypeId, mut f: impl FnMut(VarId) -> bool) -> VarId {
    let mut new = Var {name, ty};
    while self.vars.map.get(&new).map_or(false, |&v| f(VarId(v))) {
      new.name.push('\'');
    }
    self.mk_var_id(new.name, new.ty)
  }
  fn inst_type_store(&mut self, inst: &[TypeId], s: &TermStore) -> (Vec<TypeId>, Vec<VarId>, Vec<TermId>) {
    let trtys = self.tys.inst_store(inst, &s.tys);
    let mut trvars = vec![];
    for (v, _) in s.vars() {
      trvars.push(self.mk_var_avoiding(v.name.clone(),
        trtys[v.ty.into_usize()], |v| trvars.contains(&v)))
    }
    let mut trtms = vec![];
    for tm in s.terms() { trtms.push(self.subst_term_once(&trtys, &trvars, &trtms, &tm.0)) }
    (trtys, trvars, trtms)
  }

  fn inst_type_owned(&mut self, inst: &[TypeId], tm: &OwnedTerm) -> TermId {
    self.inst_type_store(inst, &tm.arena).2[tm.term.into_usize()]
  }

  fn inst_type<R>(&mut self, store: &TermStore,
    inst: &[TypeId], f: impl FnOnce(TermInstType<'a, '_>) -> R
  ) -> R {
    let tys = &mut vec![None; store.types().len()];
    let vars = &mut vec![None; store.vars().len()];
    let tms = &mut vec![None; store.terms().len()];
    f(TermInstType { arena: self, store, inst, tys, tms, vars })
  }

  fn import<R>(&mut self, store: &TermStore, f: impl FnOnce(TermInstType<'a, '_>) -> R) -> R {
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
}

pub struct TermInstType<'a, 'b> {
  arena: &'b mut TermArena<'a>,
  store: &'b TermStore,
  inst: &'b [TypeId],
  tys: &'b mut [Option<TypeId>],
  vars: &'b mut [Option<VarId>],
  tms: &'b mut [Option<TermId>],
}
impl<'a, 'b> TermInstType<'a, 'b> {
  fn as_type(&mut self) -> TypeTranslator<'a, '_> {
    TypeTranslator {
      arena: self.arena,
      store: &self.store.tys,
      inst: self.inst,
      imported: self.tys,
    }
  }
  fn tr_var(&mut self, v: VarId) -> VarId {
    if let Some(i) = self.vars[v.into_usize()] { return i }
    let vd = &*self.store[v];
    let name = vd.name.clone();
    let ty = self.as_type().tr(vd.ty);
    let n = if self.inst.is_empty() { self.arena.mk_var_id(name, ty) } else {
      let vars = &*self.vars;
      self.arena.mk_var_avoiding(name, ty, |v| vars.contains(&Some(v)))
    };
    self.vars[v.into_usize()] = Some(n);
    n
  }

  fn tr_term(&mut self, tm: TermId) -> TermId {
    if let Some(i) = self.tms[tm.into_usize()] { return i }
    let n = match *self.arena[tm].clone() {
      Term::Var(x) => term!(self.arena, V(self.tr_var(x))),
      Term::Const(c, ref tyargs) => {
        let mut trty = self.as_type();
        term!(self.arena, K(c, tyargs.iter().map(|&ty| trty.tr(ty)).collect()))
      }
      Term::App(f, x) => term!(self.arena, A (self.tr_term(f)) (self.tr_term(x))),
      Term::Lam(x, e) => term!(self.arena, L (self.tr_var(x)) (self.tr_term(e))),
    };
    self.tms[tm.into_usize()] = Some(n);
    n
  }
}

#[derive(Default)]
struct CollectTyVarsType {
  vars: Vec<TypeId>,
  visited: BitBox,
}

impl CollectTyVarsType {
  fn collect(&mut self, arena: &TypeArena, ty: TypeId) {
    if self.visited[ty.into_usize()] { return }
    match *arena[ty] {
      Type::Var(_) => self.vars.push(ty),
      Type::Const(_, ref args) => for &ty in args { self.collect(arena, ty) }
    }
    self.visited.set(ty.into_usize(), true)
  }
  fn get(self) -> Vec<TypeId> { self.vars }
  fn apply(&self, store: &mut TypeStore) {
    for (i, &v) in self.vars.iter().enumerate() {
      store.0 .0[v.into_usize()].0 = Rc::new(Type::Var(TyVarId(i as u32)));
    }
  }
}

#[derive(Default)]
struct CollectTyVarsTerm {
  pub c: CollectTyVarsType,
  visited: BitBox,
}

impl CollectTyVarsTerm {
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

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Hyps(Box<[TermId]>);

impl Hyps {
  fn contains(&self, arena: &TermArena<'_>, tm: TermId) -> bool {
    self.0.binary_search_by(|&a| arena.alpha_cmp(a, tm)).is_ok()
  }
  fn is_subset(&self, arena: &TermArena<'_>, other: &Self) -> bool {
    self.0.iter().all(|&a| other.contains(arena, a))
  }
  fn union(&self, arena: &TermArena<'_>, other: &Self) -> Self {
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

  fn remove(&self, arena: &TermArena<'_>, tm: TermId) -> Option<Self> {
    let i = self.0.binary_search_by(|&a| arena.alpha_cmp(a, tm)).ok()?;
    let mut out = Vec::with_capacity(self.0.len() - 1);
    out.extend_from_slice(&self.0[..i]);
    out.extend_from_slice(&self.0[i+1..]);
    Some(Self(out.into()))
  }

  fn from_vec(arena: &TermArena<'_>, mut vec: Vec<TermId>) -> Self {
    vec.sort_unstable_by(|&a, &b| arena.alpha_cmp(a, b));
    vec.dedup_by(|&mut a, &mut b| arena.alpha_cmp(a, b).is_eq());
    Self(vec.into())
  }
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
  fn add(&mut self, th: Proof) -> ProofId {
    self.pfs.add_val(th, ProofTrace)
  }

  pub fn new(env: &'a Environment) -> Self {
    let mut hyps = Dedup::default();
    hyps.add(Hyps(Box::new([])));
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

  fn hyps_from_vec(&mut self, vec: Vec<TermId>) -> HypsId {
    self.hyps.add(Hyps::from_vec(&self.tms, vec))
  }

  pub fn axiom(&mut self, hyps: Vec<TermId>, concl: TermId) -> ProofId {
    let hyps = self.hyps_from_vec(hyps);
    self.add(Proof { hyps, concl })
  }

  pub fn fetch(&mut self, th: ThmId, tys: Vec<TypeId>) -> ProofId {
    let d = &self.env[th];
    assert_eq!(d.tyvars as usize, tys.len());
    let (trtys, trvars, trtms) = self.inst_type_store(&tys, &d.arena);
    let hyps = d.hyps.iter().map(|&tm| {
      self.tms.subst_term_once(&trtys, &trvars, &trtms, &*d.arena[tm])
    }).collect();
    let pr = Proof {
      hyps: self.hyps_from_vec(hyps),
      concl: self.tms.subst_term_once(&trtys, &trvars, &trtms, &*d.arena[d.concl])
    };
    self.add(pr)
  }

  pub fn add_asm(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn alpha(&mut self, tm1: TermId, tm2: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn alpha_link(&mut self, th: ProofId, concl: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn alpha_conv(&mut self, tm1: TermId, tm2: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn assume(&mut self, tm: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn beta(&mut self, tm: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn ccontr(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn choose(&mut self, tm: TermId, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn conj(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn conj1(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn conj2(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn contr(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn deduct_antisym(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn disch(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn disj1(&mut self, th: ProofId, tm: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn disj2(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn disj_cases(&mut self, th1: ProofId, th2: ProofId, th3: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn eqf_elim(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn eqf_intro(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn eq_imp1(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn eq_imp2(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn eq_mp(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn eqt_elim(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn eqt_intro(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn eta(&mut self, tm: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn exists(&mut self, tm1: TermId, tm2: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn gen(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn imp_antisym(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn imp_trans(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn inst(&mut self, inst: Vec<(TermId, TermId)>, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn inst_type(&mut self, inst: Vec<(TypeId, TypeId)>, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn mp(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn not_elim(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn not_intro(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn prove_asm(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn refl(&mut self, tm: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn select_rule(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn spec(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn subs(&mut self, ths: Vec<ProofId>, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn subs_conv(&mut self, ths: Vec<ProofId>, th: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn subst(&mut self, tmths: Vec<(TermId, ProofId)>, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn subst_conv(&mut self, tmths: Vec<(TermId, ProofId)>, tm1: TermId, tm2: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn sym(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn sym_conv(&mut self, tm: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn trans(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn undisch(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn mk_quant(&mut self, q: Quant, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn mk_app(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn mk_app1(&mut self, th: ProofId, tm: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn mk_app2(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn mk_bin(&mut self, op: Binary, th1: ProofId, th2: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn mk_bin1(&mut self, op: Binary, th: ProofId, tm: TermId) -> ProofId {
    self.add(todo!())
  }
  pub fn mk_bin2(&mut self, op: Binary, tm: TermId, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn mk_not(&mut self, th: ProofId) -> ProofId {
    self.add(todo!())
  }
  pub fn mk_num_conv(&mut self, op: NumOp, tm: TermId) -> ProofId {
    self.add(todo!())
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
  pub fn with<'a>(env: &'a Environment, f: impl FnOnce(&mut TypeArena<'a>) -> TypeId) -> (OwnedType, Vec<TypeId>) {
    let mut a = TypeArena::new(env);
    let ty = f(&mut a);
    let mut c = CollectTyVarsType::default();
    c.collect(&a, ty);
    let mut arena = a.into_store();
    c.apply(&mut arena);
    let vec = c.get();
    (OwnedType {arena, tyvars: vec.len() as u32, ty}, vec)
  }
}

impl OwnedTerm {
  pub fn with<'a>(env: &'a Environment, f: impl FnOnce(&mut TermArena<'a>) -> TermId) -> (OwnedTerm, Vec<TypeId>) {
    let mut a = TermArena::new(env);
    let term = f(&mut a);
    let mut c = CollectTyVarsTerm::default();
    c.collect(&a, term);
    let mut arena = a.into_store();
    c.c.apply(&mut arena.tys);
    let vec = c.c.get();
    (OwnedTerm {arena, tyvars: vec.len() as u32, term}, vec)
  }
}

pub type TypedefInfo = (ThmDef, TypeId, TermId);

impl ThmDef {
  pub fn with_and<'a, R>(env: &'a Environment,
    f: impl FnOnce(&mut ProofArena<'a>) -> (ProofId, R)
  ) -> ((ThmDef, Vec<TypeId>), R) {
    let mut a = ProofArena::new(env);
    let (n, r) = f(&mut a);
    let Proof {hyps, concl} = *a[n];
    let store = a.into_store();
    let mut a = TermArena::new(env);
    let (hyps, concl) = a.import(&store.tms, |mut tr| (
      store[hyps].0.iter().map(|&t| tr.tr_term(t)).collect::<Box<[_]>>(),
      tr.tr_term(concl)
    ));
    let mut c = CollectTyVarsTerm::default();
    c.collect(&a, concl);
    for &h in &*hyps { c.collect(&a, h) }
    let mut arena = a.into_store();
    c.c.apply(&mut arena.tys);
    let vec = c.c.get();
    let tyvars = vec.len() as u32;
    ((ThmDef { arena, tyvars, hyps, concl }, vec), r)
  }

  pub fn with<'a>(env: &'a Environment, f: impl FnOnce(&mut ProofArena<'a>) -> ProofId) -> (ThmDef, Vec<TypeId>) {
    Self::with_and(env, |a| (f(a), ())).0
  }

  pub fn with_typedef_info<'a>(env: &'a Environment,
    f: impl FnOnce(&mut ProofArena<'a>) -> ProofId
  ) -> (TypedefInfo, Vec<TypeId>) {
    let ((pf, vec), (ty, p)) = Self::with_and(env, |a| {
      let pf = f(a);
      let Proof {hyps, concl} = *a[pf];
      assert!(hyps == HypsId::EMPTY, "hypotheses not allowed");
      let (v, pv) = a.dest_exists(concl);
      let (p, v1) = a.dest_app(pv);
      assert_eq!(v, a.dest_var(v1));
      let ty = (**a)[v].ty;
      (pf, (ty, p))
    });
    ((pf, ty, p), vec)
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
    name: impl Into<Cow<'a, str>>, arity: u32, tydef: Option<TydefData>
  ) -> TyopId {
    let n = Idx::from(self.tyops.len() as u32);
    self.tyops.push(TyopDef {arity, tydef});
    assert!(self.trans.tyops.insert(name.into().into_owned(), n).is_none());
    n
  }
  pub fn add_const<'a>(&mut self, name: impl Into<Cow<'a, str>>, ty: OwnedType) -> ConstId {
    let n = Idx::from(self.consts.len() as u32);
    self.consts.push(ConstDef {ty});
    assert!(self.trans.consts.insert(name.into().into_owned(), n).is_none());
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
    let TydefData {ty, p, exists_p} = *self.tyops[c.into_usize()].tydef
      .as_ref().expect("add_type_bijs: not a type operator");
    let store = &self.thms[exists_p.into_usize()].arena;
    let (absc, _) = OwnedType::with(self, |a| {
      // abs[v0..vn]: A -> C[v0..vn]
      ty!(a, (a.import(&store.tys, |mut tr| tr.tr(ty))) -> (a.mk_const_upto(c)))
    });
    let absc = self.add_const(&*abs, absc);
    let store = &self.thms[exists_p.into_usize()].arena;
    let (repc, _) = OwnedType::with(self, |a| {
      // rep[v0..vn]: C[v0..vn] -> A
      ty!(a, (a.mk_const_upto(c)) -> (a.import(&store.tys, |mut tr| tr.tr(ty))))
    });
    let repc = self.add_const(&*rep, repc);
    let (abs_rep, _) = ThmDef::with(self, |a| {
      let t = &mut a.tms;
      let abs = t.mk_const_upto(absc);
      let rep = t.mk_const_upto(repc);
      let (_, va) = t.mk_var_term("a", t.dest_fun(t.type_of(abs)).1);
      // a: C |- abs (rep a) = a
      let concl = term!(t, (A abs (A rep va)) = va);
      a.add(Proof { hyps: HypsId::EMPTY, concl })
    });
    let abs_rep = self.add_thm(FetchKind::TypeBij1, cname, abs_rep);
    let store = &self.thms[exists_p.into_usize()].arena;
    let (rep_abs, _) = ThmDef::with(self, |a| {
      let t = &mut a.tms;
      let abs = t.mk_const_upto(absc);
      let rep = t.mk_const_upto(repc);
      let p = t.import(store, |mut tr| tr.tr_term(p));
      let (_, vr) = t.mk_var_term("r", t.dest_fun(t.type_of(abs)).0);
      // r: A |- P r <=> rep (abs r) = r
      let concl = term!(t, (A p vr) = ((A rep (A abs vr)) = vr));
      a.add(Proof { hyps: HypsId::EMPTY, concl })
    });
    let rep_abs = self.add_thm(FetchKind::TypeBij2, cname, rep_abs);
    (absc, repc, abs_rep, rep_abs)
  }

  pub fn add_basic_def<'a>(&mut self, x: impl Into<Cow<'a, str>>, tm: OwnedTerm) -> (ConstId, ThmId) {
    let x = x.into();
    (self.add_const(&*x, OwnedType::default()), self.add_thm(FetchKind::BasicDef, x, ThmDef::default()))
  }

  pub fn add_def<'a>(&mut self, x: impl Into<Cow<'a, str>>) -> (ConstId, ThmId) {
    let x = x.into();
    (self.add_const(&*x, OwnedType::default()), self.add_thm(FetchKind::Def, x, ThmDef::default()))
  }

  pub fn add_basic_typedef<'a>(&mut self, x: impl Into<Cow<'a, str>>, (th, ty, p): TypedefInfo) -> TyopId {
    let x = x.into();
    let arity = th.tyvars;
    let exists_p = self.add_anon_thm(th);
    self.add_tyop(&*x, arity, Some(TydefData { exists_p, ty, p }))
  }

  pub fn add_spec<'a, T: Borrow<str>>(&mut self,
    xs: &[T], ThmDef {arena, hyps, concl, ..}: ThmDef) -> ThmId {
    assert!(hyps.is_empty());
    let mut term = concl;
    let mut subst = vec![];
    for x in xs {
      let x = x.borrow();
      let (v, body) = arena.dest_exists(term);
      let (tm, args) = OwnedTerm::with(self, |a| {
        let (v, body) = a.import(&arena, |mut tr| (tr.tr_var(v), tr.tr_term(body)));
        let t = a.mk_select(v, body);
        let mut inst = subst.iter()
          .map(|&(v, c, ref args)| (v, a.mk_const(c, Vec::clone(args)))).collect();
        a.inst_term(&mut inst, t)
      });
      let (c, th) = self.add_basic_def(&*x, tm);
      self.add_thm_alias(FetchKind::Def, x, th);
      subst.push((v, c, args));
      term = body;
    }
    let n = self.add_anon_thm(ThmDef::with(self, |a| {
      let t = a.import(&arena, |mut tr| tr.tr_term(term));
      let mut inst = subst.iter()
        .map(|&(v, c, ref args)| (v, a.mk_const(c, Vec::clone(args)))).collect();
      let concl = a.inst_term(&mut inst, t);
      a.axiom(vec![], concl)
    }).0);
    for x in xs { self.add_thm_alias(FetchKind::Spec, x.borrow(), n) }
    n
  }

  pub fn add_axiom(&mut self, x: String, OwnedTerm {arena, tyvars, term}: OwnedTerm) -> ThmId {
    assert!(matches!(*arena[arena.type_of(term)], Type::Const(TyopId::BOOL, _)));
    self.add_thm(FetchKind::Axiom, x, ThmDef {arena, tyvars, hyps: Box::new([]), concl: term})
  }
}
