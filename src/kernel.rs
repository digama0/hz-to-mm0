use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;
use std::borrow::Cow;
use num_bigint::BigUint;

use crate::types::*;

pub trait Node: Hash + Eq { type Idx: Idx; }
impl Node for Type { type Idx = TypeId; }
impl Node for Term { type Idx = TermId; }
impl Node for Proof { type Idx = ProofId; }

#[derive(Debug)]
struct Dedup<H> {
  map: HashMap<Rc<H>, u32>,
  objects: Vec<(Rc<H>, bool)>,
}

impl<H> Default for Dedup<H> {
  fn default() -> Self {
    Self { map: Default::default(), objects: vec![] }
  }
}

impl<H: Node> Dedup<H> {
  fn reuse(&mut self, n: H::Idx) -> H::Idx {
    self.objects[n.into_u32() as usize].1 = true;
    n
  }
}

impl<H: Node> Dedup<H> {
  fn add(&mut self, v: H) -> H::Idx {
    match self.map.entry(Rc::new(v)) {
      Entry::Vacant(e) => {
        let vec = &mut self.objects;
        let n = vec.len() as u32;
        vec.push((e.key().clone(), false));
        e.insert(n);
        Idx::from(n)
      }
      Entry::Occupied(e) => {
        let &n = e.get();
        self.reuse(Idx::from(n))
      }
    }
  }
}

#[derive(Debug, Default)]
pub struct TypeArena {
  tys: Dedup<Type>,
}

impl TypeArena {
  pub fn reuse(&mut self, id: TypeId) -> TypeId { self.tys.reuse(id) }
  pub fn mk_var(&mut self, x: String) -> TypeId {
    self.tys.add(Type::Var(x))
  }
  pub fn mk_fun(&mut self, a: TypeId, b: TypeId) -> TypeId {
    self.tys.add(Type::Fun(a, b))
  }
  pub fn mk_comp(&mut self, x: String, tys: Vec<TypeId>) -> TypeId {
    self.tys.add(Type::Comp(x, tys))
  }
}

#[derive(Debug)]
pub struct TermArena {
  pub tys: TypeArena,
  tms: Dedup<Term>,
}

impl TermArena {
  pub fn new(tys: TypeArena) -> Self { Self { tys, tms: Dedup::default() } }
  pub fn reuse(&mut self, id: TermId) -> TermId { self.tms.reuse(id) }
  pub fn mk_var(&mut self, x: String, ty: TypeId) -> TermId {
    self.tms.add(Term::Var(x, ty))
  }
  pub fn mk_const(&mut self, c: String, tys: Vec<TypeId>) -> TermId {
    self.tms.add(Term::OConst(c, tys))
  }
  pub fn mk_int(&mut self, n: BigUint) -> TermId {
    self.tms.add(Term::BigInt(n))
  }
  pub fn mk_app(&mut self, f: TermId, a: TermId) -> TermId {
    self.tms.add(Term::App(f, a))
  }
  pub fn mk_quant(&mut self, q: Quant, f: TermId, a: TermId) -> TermId {
    self.tms.add(Term::Quant(q, f, a))
  }
  pub fn mk_bin(&mut self, b: Binary, f: TermId, a: TermId) -> TermId {
    self.tms.add(Term::Binary(b, f, a))
  }
  pub fn mk_not(&mut self, x: TermId) -> TermId {
    self.tms.add(Term::Not(x))
  }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum Proof {
  Fetch(ThmId, Vec<TypeId>),
  AddAsm(TermId, ProofId),
  Alpha(TermId, TermId),
  AlphaLink(ProofId, TermId),
  AlphaConv(TermId, TermId),
  Assume(TermId),
  Beta(TermId),
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
  Eta(TermId),
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
  App(ProofId, ProofId),
  App1(ProofId, TermId),
  App2(TermId, ProofId),
  Bin(Binary, ProofId, ProofId),
  Bin1(Binary, ProofId, TermId),
  Bin2(Binary, TermId, ProofId),
  Not(ProofId),
  NumConv(NumOp, TermId),
}

#[derive(Debug)]
pub struct ProofArena {
  pub tms: TermArena,
  pfs: Dedup<Proof>,
}

impl ProofArena {
  pub fn new(tms: TermArena) -> Self { Self { tms, pfs: Dedup::default() } }
  pub fn reuse(&mut self, id: ProofId) -> ProofId { self.pfs.reuse(id) }
  pub fn fetch(&mut self, th: ThmId, tys: Vec<TypeId>) -> ProofId {
    self.pfs.add(Proof::Fetch(th, tys))
  }
  pub fn add_asm(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::AddAsm(tm, th))
  }
  pub fn alpha(&mut self, tm1: TermId, tm2: TermId) -> ProofId {
    self.pfs.add(Proof::Alpha(tm1, tm2))
  }
  pub fn alpha_link(&mut self, th: ProofId, concl: TermId) -> ProofId {
    self.pfs.add(Proof::AlphaLink(th, concl))
  }
  pub fn alpha_conv(&mut self, tm1: TermId, tm2: TermId) -> ProofId {
    self.pfs.add(Proof::AlphaConv(tm1, tm2))
  }
  pub fn assume(&mut self, tm: TermId) -> ProofId {
    self.pfs.add(Proof::Assume(tm))
  }
  pub fn beta(&mut self, tm: TermId) -> ProofId {
    self.pfs.add(Proof::Beta(tm))
  }
  pub fn ccontr(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::CContr(tm, th))
  }
  pub fn choose(&mut self, tm: TermId, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::Choose(tm, th1, th2))
  }
  pub fn conj(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::Conj(th1, th2))
  }
  pub fn conj1(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Conj1(th))
  }
  pub fn conj2(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Conj2(th))
  }
  pub fn contr(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Contr(tm, th))
  }
  pub fn deduct_antisym(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::DeductAntiSym(th1, th2))
  }
  pub fn disch(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Disch(tm, th))
  }
  pub fn disj1(&mut self, th: ProofId, tm: TermId) -> ProofId {
    self.pfs.add(Proof::Disj1(th, tm))
  }
  pub fn disj2(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Disj2(tm, th))
  }
  pub fn disj_cases(&mut self, th1: ProofId, th2: ProofId, th3: ProofId) -> ProofId {
    self.pfs.add(Proof::DisjCases(th1, th2, th3))
  }
  pub fn eqf_elim(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::EqfElim(th))
  }
  pub fn eqf_intro(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::EqfIntro(th))
  }
  pub fn eq_imp1(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::EqImp1(th))
  }
  pub fn eq_imp2(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::EqImp2(th))
  }
  pub fn eq_mp(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::EqMp(th1, th2))
  }
  pub fn eqt_elim(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::EqtElim(th))
  }
  pub fn eqt_intro(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::EqtIntro(th))
  }
  pub fn eta(&mut self, tm: TermId) -> ProofId {
    self.pfs.add(Proof::Eta(tm))
  }
  pub fn exists(&mut self, tm1: TermId, tm2: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Exists(tm1, tm2, th))
  }
  pub fn gen(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Gen(tm, th))
  }
  pub fn imp_antisym(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::ImpAntiSym(th1, th2))
  }
  pub fn imp_trans(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::ImpTrans(th1, th2))
  }
  pub fn inst(&mut self, inst: Vec<(TermId, TermId)>, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Inst(inst, th))
  }
  pub fn inst_type(&mut self, inst: Vec<(TypeId, TypeId)>, th: ProofId) -> ProofId {
    self.pfs.add(Proof::InstType(inst, th))
  }
  pub fn mp(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::Mp(th1, th2))
  }
  pub fn not_elim(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::NotElim(th))
  }
  pub fn not_intro(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::NotIntro(th))
  }
  pub fn prove_asm(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::ProveAsm(th1, th2))
  }
  pub fn refl(&mut self, tm: TermId) -> ProofId {
    self.pfs.add(Proof::Refl(tm))
  }
  pub fn select_rule(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::SelectRule(th))
  }
  pub fn spec(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Spec(tm, th))
  }
  pub fn subs(&mut self, ths: Vec<ProofId>, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Subs(ths, th))
  }
  pub fn subs_conv(&mut self, ths: Vec<ProofId>, th: TermId) -> ProofId {
    self.pfs.add(Proof::SubsConv(ths, th))
  }
  pub fn subst(&mut self, tmths: Vec<(TermId, ProofId)>, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Subst(tmths, tm, th))
  }
  pub fn subst_conv(&mut self, tmths: Vec<(TermId, ProofId)>, tm1: TermId, tm2: TermId) -> ProofId {
    self.pfs.add(Proof::SubstConv(tmths, tm1, tm2))
  }
  pub fn sym(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Sym(th))
  }
  pub fn sym_conv(&mut self, tm: TermId) -> ProofId {
    self.pfs.add(Proof::SymConv(tm))
  }
  pub fn trans(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::Trans(th1, th2))
  }
  pub fn undisch(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Undisch(th))
  }
  pub fn mk_quant(&mut self, q: Quant, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Quant(q, tm, th))
  }
  pub fn mk_app(&mut self, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::App(th1, th2))
  }
  pub fn mk_app1(&mut self, th: ProofId, tm: TermId) -> ProofId {
    self.pfs.add(Proof::App1(th, tm))
  }
  pub fn mk_app2(&mut self, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::App2(tm, th))
  }
  pub fn mk_bin(&mut self, op: Binary, th1: ProofId, th2: ProofId) -> ProofId {
    self.pfs.add(Proof::Bin(op, th1, th2))
  }
  pub fn mk_bin1(&mut self, op: Binary, th: ProofId, tm: TermId) -> ProofId {
    self.pfs.add(Proof::Bin1(op, th, tm))
  }
  pub fn mk_bin2(&mut self, op: Binary, tm: TermId, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Bin2(op, tm, th))
  }
  pub fn mk_not(&mut self, th: ProofId) -> ProofId {
    self.pfs.add(Proof::Not(th))
  }
  pub fn mk_num_conv(&mut self, op: NumOp, tm: TermId) -> ProofId {
    self.pfs.add(Proof::NumConv(op, tm))
  }
}

#[derive(Debug)]
pub struct OwnedType(pub TypeArena, pub TypeId);
#[derive(Debug)]
pub struct OwnedTerm(pub TermArena, pub TermId);
#[derive(Debug)]
pub struct OwnedProof(pub ProofArena, pub ProofId);

#[derive(Debug)]
pub enum Object {
  TypeDecl(String, u32),
  ConstDecl(String, OwnedType),
  Axiom(String, OwnedTerm),
  BasicDef(String, OwnedTerm),
  Def(String, OwnedTerm),
  Spec(Box<[String]>, OwnedProof),
  BasicTypedef(String, OwnedProof),
  Thm(String, OwnedProof),
  OpenThm(String, OwnedProof),
  NumThm(u32, OwnedProof),
  TypeBij([String; 3]),
}

#[derive(Debug, Default)]
pub struct Environment {
  pub tyops: Vec<TyopDef>,
  pub consts: Vec<ConstDef>,
  pub thms: Vec<ThmDef>,
  pub trans: TransTable,
  pub counts: HashMap<&'static str, (u32, u32)>,
  pub objects: usize,
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
    self.add_const(x1, ConstDef {});
    self.add_const(x2, ConstDef {});
    let x = x.into();
    self.add_thm(FetchKind::TypeBij1, &*x, ThmDef {});
    self.add_thm(FetchKind::TypeBij2, x, ThmDef {});
  }

  pub fn add_basic_def<'a>(&mut self, x: impl Into<Cow<'a, str>>, _tm: OwnedTerm) {
    let x = x.into(); self.add_const(&*x, ConstDef {});
    self.add_thm(FetchKind::BasicDef, x, ThmDef {});
  }

  pub fn add_def<'a>(&mut self, x: impl Into<Cow<'a, str>>) {
    let x = x.into(); self.add_const(&*x, ConstDef {});
    self.add_thm(FetchKind::Def, x, ThmDef {});
  }

  pub fn add_basic_typedef<'a>(&mut self, x: impl Into<Cow<'a, str>>) {
    let x = x.into(); self.add_tyop(&*x, TyopDef {arity: 0}); // TODO
    self.add_thm(FetchKind::BasicTypedef, &*x, ThmDef {});
    self.add_thm(FetchKind::BasicTypedefInput, x, ThmDef {});
  }

  pub fn add_spec<'a, I: Into<Cow<'a, str>>>(&mut self, xs: impl IntoIterator<Item=I>) {
    for x in xs {
      let x = x.into(); self.add_const(&*x, ConstDef {});
      self.add_thm(FetchKind::Spec, x, ThmDef {})
    }
  }

  pub fn add(&mut self, o: Object) {
    self.objects += 1;
    match o {
      Object::TypeDecl(x, arity) => self.add_tyop(x, TyopDef {arity}),
      Object::ConstDecl(x, _) => self.add_const(x, ConstDef {}),
      Object::Axiom(x, _) => self.add_thm(FetchKind::Axiom, x, ThmDef {}),
      Object::BasicDef(x, tm) => self.add_basic_def(x, tm),
      Object::Def(x, _) => self.add_def(x),
      Object::Spec(xs, _) => self.add_spec(Vec::from(xs)),
      Object::BasicTypedef(x, _) => self.add_basic_typedef(x),
      Object::Thm(x, _) => self.add_thm(FetchKind::Thm, x, ThmDef {}),
      Object::OpenThm(x, _) => self.add_thm(FetchKind::OThm, x, ThmDef {}),
      Object::NumThm(x, _) => self.add_thm(FetchKind::NThm, x.to_string(), ThmDef {}),
      Object::TypeBij([x, x1, x2]) => self.add_type_bijs(&x, x1, x2),
    }
  }
}
