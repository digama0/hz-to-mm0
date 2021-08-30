use std::convert::TryInto;
use crate::mm0::{self, import::mm0_const as c};

use super::ConstReason;
use super::kernel::Environment;
use super::types::{ConstId, ThmId, FetchKind, TyopId};

impl TyopId {
  pub const BOOL:    Self = Self(0);
  pub const FUN:     Self = Self(1);
  pub const PROD:    Self = Self(2);
}

impl ConstId {
  pub const EQ:      Self = Self(0);
  pub const TRUE:    Self = Self(1);
  pub const CONJ:    Self = Self(2);
  pub const IMP:     Self = Self(3);
  pub const FORALL:  Self = Self(4);
  pub const EXISTS:  Self = Self(5);
  pub const DISJ:    Self = Self(6);
  pub const FALSE:   Self = Self(7);
  pub const NOT:     Self = Self(8);
  pub const UEXISTS: Self = Self(9);
  pub const SELECT:  Self = Self(10);
  pub const PAIR:    Self = Self(15);
  pub const FST:     Self = Self(16);
  pub const SND:     Self = Self(17);
  pub const ZERO:    Self = Self(25);
  pub const SUC:     Self = Self(26);
  pub const NUMERAL: Self = Self(27);
  pub const BIT0:    Self = Self(28);
  pub const BIT1:    Self = Self(29);
  pub const PRE:     Self = Self(30);
  pub const ADD:     Self = Self(31);
  pub const MULT:    Self = Self(32);
  pub const EXP:     Self = Self(33);
  pub const LE:      Self = Self(34);
  pub const LT:      Self = Self(35);
  pub const GE:      Self = Self(36);
  pub const GT:      Self = Self(37);
  pub const EVEN:    Self = Self(38);
  pub const ODD:     Self = Self(39);
  pub const SUB:     Self = Self(40);
}


impl Environment {
  fn parse_const(&mut self, x: &str, tm: mm0::TermId, tyth: mm0::ThmId,
    tys: &[&str], ty: &str) -> ConstId {
    let ty = self.parse_owned_type(tys, ty);
    self.add_const(x, Some((tm, tyth)), ConstReason::Axiom, ty)
  }

  fn parse_basic_def(&mut self, x: &str,
    c: mm0::TermId, tyth: mm0::ThmId, eqth: mm0::ThmId,
    tys: &[&str], tms: &[&str], tm: &str
  ) -> (ConstId, ThmId) {
    let tm = self.parse_owned_term(tys, tms, tm);
    self.add_basic_def(x, Some(((c, tyth), eqth)), tm)
  }

  fn parse_def(&mut self, x: &str, arity: u32,
    c: mm0::TermId, tyth: mm0::ThmId, eqth: mm0::ThmId, eqth2: mm0::ThmId,
    tys: &[&str], tms: &[&str], tm: &str
  ) -> (ConstId, ThmId) {
    let tm = self.parse_owned_term(tys, tms, tm);
    self.add_simple_def(x, arity, Some((((c, tyth), eqth), eqth2)), tm)
  }

  fn parse_basic_typedef(&mut self, [x, abs, rep]: [&str; 3], tydef: mm0::TydefId,
    tys: &[&str], tms: &[&str], tm: &str
  ) -> TyopId {
    let (th, tyop, cs, ths) = mm0::import::TYDEFS[tydef.0 as usize];
    let td = self.parse_thm_def(th, tys, tms, &[], tm);
    let n = self.add_basic_typedef(x, Some((th, tyop, tydef)), td);
    self.add_type_bijs(n, x, abs, rep, Some((cs, ths)));
    n
  }

  fn parse_thm(&mut self, k: FetchKind, x: &str,
    ext: mm0::ThmId,
    tys: &[&str], tms: &[&str], concl: &str
  ) -> ThmId {
    let th = self.parse_thm_def(ext, tys, tms, &[], concl);
    self.add_thm(k, x, Some(ext), th)
  }

  fn parse_spec<const N: usize>(&mut self,
    xs: &[&str; N],
    exts: &[((mm0::TermId, mm0::ThmId), mm0::ThmId); N],
    ext: mm0::ThmId,
    tys: &[&str], tms: &[&str], tm: &str
  ) -> ([ConstId; N], ThmId) {
    let th = self.parse_thm_def(ext, tys, tms, &[], tm);
    let (cs, th) = self.add_spec(xs, exts, Some(ext), th);
    (cs.try_into().unwrap(), th)
  }

  pub fn init(&mut self) {
    use FetchKind::*;
    assert_eq!(TyopId::BOOL, self.add_tyop("bool", Some(c::BOOL), 0, None));
    assert_eq!(TyopId::FUN, self.add_tyop("fun", Some(c::FUN), 2, None));
    let bool_ty = "K \"bool\"";
    let ind_ty = "K \"ind\"";
    let num_ty = "K \"num\"";
    let p_tm = "V \"p\" z1";
    let q_tm = "V \"q\" z1";
    let r_tm = "V \"r\" z1";
    let a_ty = "V \"A\"";
    let b_ty = "V \"B\"";
    let vx = "V \"x\" z1";
    let vy = "V \"y\" z2";
    let vn = "V \"n\" z1";
    let suc = "K \"SUC\"";
    assert_eq!(ConstId::EQ, self.parse_const("=", c::EQ, c::EQ_T,
      &[a_ty], "F z1 (F z1 (K \"bool\"))"));
    // T = ((\p:bool. p) = (\p:bool. p))
    assert_eq!(ConstId::TRUE, self.parse_basic_def("T", c::TRUE, c::TRUE_T, c::TRUE_DEF,
      &[bool_ty], &[p_tm, "L t1 t1"], "E t2 t2").0);
    // (/\) = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)
    assert_eq!(ConstId::CONJ, self.parse_basic_def("/\\", c::AND, c::AND_T, c::AND_DEF,
      &[bool_ty, "F z1 (F z1 z1)"], &[p_tm, q_tm, "V \"f\" z2", "K \"T\""],
      "L t1 (L t2 (E (L t3 (B t3 t1 t2)) (L t3 (B t3 t4 t4))))").0);
    // (==>) = \p q. p /\ q <=> p
    assert_eq!(ConstId::IMP, self.parse_basic_def("==>", c::IMP, c::IMP_T, c::IMP_DEF,
      &[bool_ty], &[p_tm, q_tm], "L t1 (L t2 (E (C t1 t2) t1))").0);
    // (!) = \P:A->bool. P = \x. T
    assert_eq!(ConstId::FORALL, self.parse_basic_def("!", c::ALL, c::ALL_T, c::ALL_DEF,
      &[a_ty, "F z1 (K \"bool\")"], &["V \"P\" z2"],
      "L t1 (E t1 (L (V \"x\" z1) (K \"T\")))").0);
    // (?) = \P:A->bool. !q. (!x. P x ==> q) ==> q
    assert_eq!(ConstId::EXISTS, self.parse_basic_def("?", c::EX, c::EX_T, c::EX_DEF,
      &[bool_ty, a_ty, "F z2 z1"], &["V \"P\" z3", q_tm, "V \"x\" z2"],
      r#"L t1 (U t2 (I (U t3 (I (A t1 t3) t2)) t2))"#).0);
    // (\/) = \p q. !r. (p ==> r) ==> (q ==> r) ==> r
    assert_eq!(ConstId::DISJ, self.parse_basic_def("\\/", c::OR, c::OR_T, c::OR_DEF,
      &[bool_ty], &[p_tm, q_tm, r_tm],
      "L t1 (L t2 (U t3 (I (I t1 t3) (I (I t2 t3) t3))))").0);
    // F = !p:bool. p
    assert_eq!(ConstId::FALSE, self.parse_basic_def("F", c::FALSE, c::FALSE_T, c::FALSE_DEF,
      &[bool_ty], &[p_tm], "U t1 t1").0);
    // (~) = \p. p ==> F
    assert_eq!(ConstId::NOT, self.parse_basic_def("~", c::NOT, c::NOT_T, c::NOT_DEF,
      &[bool_ty], &[p_tm], "L t1 (I t1 (K \"F\"))").0);
    // (?!) = \P:A->bool. (?) P /\ (!x y. P x /\ P y ==> x = y)
    assert_eq!(ConstId::UEXISTS, self.parse_basic_def("?!", c::EU, c::EU_T, c::EU_DEF,
      &[a_ty, "F z1 (K \"bool\")"], &["V \"P\" z2", vx, "V \"y\" z1"],
      r#"L t1 (C (A (K "?" z1) t1) (U t2 (U t3 (I (C (A t1 t2) (A t1 t3)) (E t2 t3)))))"#).0);
    // !t:A->B. (\x. t x) = t
    self.parse_thm(Axiom, "ETA_AX", c::ETA_AX,
      &[a_ty, b_ty, "F z1 z2"], &["V \"t\" z3", "V \"x\" z1"],
      "U t1 (E (L t2 (A t1 t2)) t1)");
    assert_eq!(ConstId::SELECT, self.parse_const("@", c::SEL, c::SEL_T,
      &[a_ty], "F (F z1 (K \"bool\")) z1"));
    // !P (x:A). P x ==> P ((@) P)
    self.parse_thm(Axiom, "SELECT_AX", c::SELECT_AX,
      &[a_ty, bool_ty, "F z1 z2"], &["V \"P\" z3", "V \"x\" z1"],
      "U t1 (U t2 (I (A t1 t2) (A t1 (A (K \"@\" z1) t1))))");
    // COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ ((t <=> F) ==> (x = t2))
    self.parse_basic_def("COND", c::COND, c::COND_T, c::COND_DEF,
      &[bool_ty, a_ty],
      &["V \"t\" z1", "V \"t1\" z2", "V \"t2\" z2", "V \"x\" z2",
        "I (E t1 (K \"T\")) (E t4 t2)", "I (E t1 (K \"F\")) (E t4 t3)"],
      "L t1 (L t2 (L t3 (S t4 (C t5 t6))))");
    // mk_pair = \(x:A) (y:B) a b. (a = x) /\ (b = y)
    self.parse_basic_def("mk_pair", c::MK_PAIR, c::MK_PAIR_T, c::MK_PAIR_DEF,
      &[a_ty, b_ty], &[vx, vy, "V \"a\" z1", "V \"b\" z2"],
      "L t1 (L t2 (L t3 (L t4 (C (E t3 t1) (E t4 t2)))))");
    // prod = basic_typedef [?x. (\x. ?a b. x = mk_pair a b) x]
    assert_eq!(TyopId::PROD, self.parse_basic_typedef(
      ["prod", "ABS_prod", "REP_prod"], c::PROD_TYDEF,
      &[a_ty, b_ty, "F z1 (F z2 (K \"bool\"))"], &["V \"x\" z3", "V \"a\" z1", "V \"b\" z2"],
      "X t1 (A (L t1 (X t2 (X t3 (E t1 (B (K \"mk_pair\" z1 z2) t2 t3))))) t1)"));
    // (,) = \(x:A) (y:B). ABS_prod(mk_pair x y)
    assert_eq!(ConstId::PAIR, self.parse_basic_def(",", c::PAIR, c::PAIR_T, c::PAIR_DEF,
      &[a_ty, b_ty], &[vx, vy],
      r#"L t1 (L t2 (A (K "ABS_prod" z1 z2) (B (K "mk_pair" z1 z2) t1 t2)))"#).0);
    // FST = \p:A#B. @x. ?y. p = x,y
    assert_eq!(ConstId::FST, self.parse_basic_def("FST", c::FST, c::FST_T, c::FST_DEF,
      &[a_ty, b_ty, "K \"prod\" z1 z2"], &["V \"p\" z3", vx, vy],
      "L t1 (S t2 (X t3 (E t1 (P t2 t3))))").0);
    // SND = \p:A#B. @y. ?x. p = x,y`
    assert_eq!(ConstId::SND, self.parse_basic_def("SND", c::SND, c::SND_T, c::SND_DEF,
      &[a_ty, b_ty, "K \"prod\" z1 z2"], &["V \"p\" z3", vx, vy],
      "L t1 (S t3 (X t2 (E t1 (P t2 t3))))").0);
    self.add_tyop("ind", Some(c::IND), 0, None);
    // ONE_ONE = \f:A->B. !x1 x2. (f x1 = f x2) ==> (x1 = x2)
    self.parse_def("ONE_ONE", 1, c::ONE_ONE, c::ONE_ONE_T, c::ONE_ONE_BD, c::ONE_ONE_DEF,
      &[a_ty, b_ty, "F z1 z2"], &["V \"x1\" z1", "V \"x2\" z1", "V \"f\" z3"],
      "L t3 (U t1 (U t2 (I (E (A t3 t1) (A t3 t2)) (E t1 t2))))");
    // ONTO = \f:A->B. !y. ?x. y = f x
    self.parse_def("ONTO", 1, c::ONTO, c::ONTO_T, c::ONTO_BD, c::ONTO_DEF,
      &[a_ty, b_ty, "F z1 z2"], &[vx, vy, "V \"f\" z3"],
      "L t3 (U t2 (X t1 (E t2 (A t3 t1))))");
    // ?f:ind->ind. ONE_ONE f /\ ~ONTO f
    self.parse_thm(Axiom, "INFINITY_AX", c::INFINITY_AX,
      &[ind_ty, "F z1 z1"], &["V \"f\" z2"],
      "X t1 (C (A (K \"ONE_ONE\" z1 z1) t1) (N (A (K \"ONTO\" z1 z1) t1)))");
    // IND_SUC = (@f. ?z. (!x1 x2. f x1 = f x2 <=> x1 = x2) /\ (!x. ~(f x = z)))
    self.parse_def("IND_SUC", 0, c::IND_SUC, c::IND_SUC_T, c::IND_SUC_DEF, c::IND_SUC_DEF,
      &[ind_ty, "F z1 z1"],
      &["V \"z\" z1", "V \"x1\" z1", "V \"x2\" z1", "V \"x\" z1", "V \"f\" z2",
        "U t2 (U t3 (E (E (A t5 t2) (A t5 t3)) (E t2 t3)))"],
      "S t5 (X t1 (C t6 (U t4 (N (E (A t5 t4) t1)))))");
    // IND_0 = (@z. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\ (!x. ~(IND_SUC x = z)))
    self.parse_def("IND_0", 0, c::IND_0, c::IND_0_T, c::IND_0_DEF, c::IND_0_DEF,
      &[ind_ty],
      &["V \"z\" z1", "V \"x1\" z1", "V \"x2\" z1", "V \"x\" z1", "K \"IND_SUC\"",
        "U t2 (U t3 (E (E (A t5 t2) (A t5 t3)) (E t2 t3)))"],
      "S t1 (C t6 (U t4 (N (E (A t5 t4) t1))))");
    // NUM_REP = \k. !P. P IND_0 /\ (!j. P j ==> P (IND_SUC j)) ==> P i
    self.parse_basic_def("NUM_REP", c::NUM_REP, c::NUM_REP_T, c::NUM_REP_DEF,
      &[ind_ty, "F z1 (K \"bool\")"],
      &["V \"k\" z1", "V \"P\" z2", "V \"j\" z1", "V \"i\" z1",
        r#"(D (E t3 (K "IND_0")) (X t4 (C (E t3 (A (K "IND_SUC") t4)) (A t2 t4))))"#],
      "L t1 (U t2 (I (U t3 (I t5 (A t2 t3))) (A t2 t1)))");
    // num = basic_typedef [?k:ind. NUM_REP k]
    self.parse_basic_typedef(["num", "mk_num", "dest_num"], c::NUM_TYDEF,
      &[ind_ty], &["V \"k\" z1"], "X t1 (A (K \"NUM_REP\") t1)");
    // _0 = mk_num IND_0
    assert_eq!(ConstId::ZERO, self.parse_def("_0", 0, c::ZERO, c::ZERO_T, c::ZERO_DEF, c::ZERO_DEF,
      &[], &[], "A (K \"mk_num\") (K \"IND_0\")").0);
    // !n. SUC n = mk_num (IND_SUC (dest_num n))
    assert_eq!(ConstId::SUC, self.parse_def("SUC", 1, c::SUC, c::SUC_T, c::SUC_BD, c::SUC_DEF,
      &[num_ty], &[vn],
      r#"L t1 (A (K "mk_num") (A (K "IND_SUC") (A (K "dest_num") t1)))"#).0);
    // !n. NUMERAL n = n
    assert_eq!(ConstId::NUMERAL, self.parse_def("NUMERAL", 1,
      c::NUMERAL, c::NUMERAL_T, c::NUMERAL_BD, c::NUMERAL_DEF,
      &[num_ty], &[vn], "L t1 t1").0);
    // BIT0 = @fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC (fn n)))
    assert_eq!(ConstId::BIT0, self.parse_def("BIT0", 0,
      c::BIT0, c::BIT0_T, c::BIT0_DEF, c::BIT0_DEF,
      &[num_ty, "F z1 z1"], &["V \"fn\" z2", vn, suc, "M 0"],
      "S t1 (C (E (A t1 t4) t4) (U t2 (E (A t1 (A t3 t2)) (A t3 (A t3 (A t1 t2))))))").0);
    // !n. BIT1 n = SUC (BIT0 n)
    assert_eq!(ConstId::BIT1, self.parse_def("BIT1", 1,
      c::BIT1, c::BIT1_T, c::BIT1_BD, c::BIT1_DEF,
      &[num_ty], &[vn], "L t1 (A (K \"SUC\") (A (K \"BIT0\") t1))").0);
    // PRE 0 = 0 /\ (!n. PRE (SUC n) = n))
    let ([c], pre) = self.parse_spec(&["PRE"], &[((c::PRE, c::PRE_T), c::PRE_DEF)], c::PRE_SPEC,
      &[num_ty, "F z1 z1"],
      &["V \"PRE\" z2", "M 0", suc, "V \"n\" z1"],
      "X t1 (C (E (A t1 t2) t2) (U t4 (E (A t1 (A t3 t4)) t4)))");
    assert_eq!(c, ConstId::PRE);
    // (!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n))
    let ([c], add) = self.parse_spec(&["+"], &[((c::ADD, c::ADD_T), c::ADD_DEF)], c::ADD_SPEC,
      &[num_ty, "F z1 (F z1 z1)"],
      &["V \"+\" z2", "M 0", suc, "V \"m\" z1", "V \"n\" z1"],
      "X t1 (C (U t5 (E (B t1 t2 t5) t5)) \
               (U t4 (U t5 (E (B t1 (A t3 t4) t5) (A t3 (B t1 t4 t5))))))");
    assert_eq!(c, ConstId::ADD);
    // (!n. 0 * n = 0) /\ (!m n. SUC m * n = m * n + n)
    let ([c], _) = self.parse_spec(&["*"], &[((c::MUL, c::MUL_T), c::MUL_DEF)], c::MUL_SPEC,
      &[num_ty, "F z1 (F z1 z1)"],
      &["V \"*\" z2", "M 0", suc, "V \"m\" z1", "V \"n\" z1"],
      "X t1 (C (U t5 (E (B t1 t2 t5) t2)) \
               (U t4 (U t5 (E (B t1 (A t3 t4) t5) (B (K \"+\") (B t1 t4 t5) t5)))))");
    assert_eq!(c, ConstId::MULT);
    // (!m. m EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n)
    let ([c], exp) = self.parse_spec(&["EXP"], &[((c::EXP, c::EXP_T), c::EXP_DEF)], c::EXP_SPEC,
      &[num_ty, "F z1 (F z1 z1)"],
      &["V \"EXP\" z2", "M 0", suc, "V \"m\" z1", "V \"n\" z1"],
      "X t1 (C (U t4 (E (B t1 t4 t2) (M 1))) \
               (U t4 (U t5 (E (B t1 t4 (A t3 t5)) (B (K \"*\") t4 (B t1 t4 t5))))))");
    assert_eq!(c, ConstId::EXP);
    // (!m. m <= 0 <=> m = 0) /\ (!m n. m <= SUC n <=> m = SUC n \/ m <= n)
    let ([c], _) = self.parse_spec(&["<="], &[((c::LE, c::LE_T), c::LE_DEF)], c::LE_SPEC,
      &[num_ty, "F z1 (F z1 (K \"bool\"))"],
      &["V \"<=\" z2", "M 0", suc, "V \"m\" z1", "V \"n\" z1"],
      "X t1 (C (U t4 (E (B t1 t4 t2) (E t4 t2))) \
               (U t4 (U t5 (E (B t1 t4 (A t3 t5)) (D (E t4 (A t3 t4)) (B t1 t4 t5))))))");
    assert_eq!(c, ConstId::LE);
    // (!m. m < 0 <=> F) /\ (!m n. m < SUC n <=> m = n \/ m < n)
    let ([c], lt) = self.parse_spec(&["<"], &[((c::LT, c::LT_T), c::LT_DEF)], c::LT_SPEC,
      &[num_ty, "F z1 (F z1 (K \"bool\"))"],
      &["V \"<\" z2", "M 0", suc, "V \"m\" z1", "V \"n\" z1"],
      "X t1 (C (U t4 (E (B t1 t4 t2) (K \"F\"))) \
               (U t4 (U t5 (E (B t1 t4 (A t3 t5)) (D (E t4 t5) (B t1 t4 t5))))))");
    assert_eq!(c, ConstId::LT);
    // !m n. m >= n <=> n <= m
    assert_eq!(ConstId::GE, self.parse_def(">=", 2, c::GE, c::GE_T, c::GE_BD, c::GE_DEF,
      &[num_ty], &["V \"m\" z1", "V \"n\" z1"],
      "L t1 (L t2 (B (K \"<=\") t2 t1))").0);
    // !m n. m > n <=> n < m
    assert_eq!(ConstId::GT, self.parse_def(">", 2, c::GT, c::GT_T, c::GT_BD, c::GT_DEF,
      &[num_ty], &["V \"m\" z1", "V \"n\" z1"],
      "L t1 (L t2 (B (K \"<\") t2 t1))").0);
    // (EVEN 0 <=> T) /\ (!n. EVEN (SUC n) <=> ~EVEN n)
    let ([c], even) = self.parse_spec(&["EVEN"],
      &[((c::EVEN, c::EVEN_T), c::EVEN_DEF)], c::EVEN_SPEC,
      &[num_ty, "F z1 (K \"bool\")"], &["V \"EVEN\" z2", "M 0", suc, "V \"n\" z1"],
      "X t1 (C (E (A t1 t2) (K \"T\")) (U t4 (E (A t1 (A t3 t4)) (N (A t1 t4)))))");
    assert_eq!(c, ConstId::EVEN);
    // (ODD 0 <=> F) /\ (!n. ODD (SUC n) <=> ~ODD n)
    let ([c], _) = self.parse_spec(&["ODD"],
      &[((c::ODD, c::ODD_T), c::ODD_DEF)], c::ODD_SPEC,
      &[num_ty, "F z1 (K \"bool\")"], &["V \"ODD\" z2", "M 0", suc, "V \"n\" z1"],
      "X t1 (C (E (A t1 t2) (K \"F\")) (U t4 (E (A t1 (A t3 t4)) (N (A t1 t4)))))");
    assert_eq!(c, ConstId::ODD);
    // (!m. m - 0 = m) /\ (!m n. m - SUC n = PRE (m - n))
    let ([c], sub) = self.parse_spec(&["-"],
      &[((c::SUB, c::SUB_T), c::SUB_DEF)], c::SUB_SPEC,
      &[num_ty, "F z1 (F z1 z1)"],
      &["V \"-\" z2", "M 0", suc, "V \"m\" z1", "V \"n\" z1", "K \"PRE\""],
      "X t1 (C (U t4 (E (B t1 t4 t2) t4)) \
               (U t4 (U t5 (E (B t1 t4 (A t3 t5)) (A t6 (B t1 t4 t5))))))");
    assert_eq!(c, ConstId::SUB);
    // TYPE_DEFINITION = \(P:A->bool) (rep:B->A). ONE_ONE rep /\ (!x:A. P x <=> (?y:B. x = rep y))
    self.parse_basic_def("TYPE_DEFINITION", c::TYPEDEF, c::TYPEDEF_T, c::TYPEDEF_DEF,
      &[a_ty, b_ty, bool_ty, "F z1 z3", "F z2 z1"],
      &["V \"P\" z4", "V \"rep\" z5", "V \"x\" z1", "V \"y\" z2"],
      "L t1 (L t2 (C (A (K \"ONE_ONE\" z2 z1) t2) (U t3 (E (A t1 t3) (X t4 (E t3 (A t2 t4)))))))");
    // (/\) = (\p q. !t. (p ==> q ==> t) ==> t)
    self.parse_thm(Thm, "AND_DEF1", c::AND_DEF1,
      &[bool_ty], &["V \"p\" z1", "V \"q\" z1", "V \"t\" z1"],
      r#"E (K "/\\") (L t1 (L t2 (U t3 (I (I t1 (I t2 t3)) t3))))"#);
    // (?) = (\P:A->bool. P ((@) P))
    self.parse_thm(Thm, "EXISTS_THM", c::EXISTS_THM,
      &[a_ty, bool_ty, "F z1 z2"], &["V \"P\" z3"],
      "E (K \"?\" z1) (L t1 (A t1 (A (K \"@\" z1) t1)))");
    // (?!) = (\P. ?t. P t /\ (!x. P x ==> x = t))
    self.parse_thm(Thm, "EXISTS_UNIQUE_DEF1", c::EU_DEF1,
      &[a_ty, bool_ty, "F z1 z2"], &["V \"P\" z3", "V \"t\" z1", "V \"x\" z1"],
      "E (K \"?!\" z1) (L t1 (X t2 (C (A t1 t2) (U t3 (I (A t1 t3) (E t3 t2))))))");
    // !t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 <=> t2)
    self.parse_thm(Thm, "IMP_ANTISYM_AX", c::IMP_ANTISYM_AX,
      &[bool_ty], &["V \"t1\" z1", "V \"t2\" z1"],
      "U t1 (U t2 (I (I t1 t2) (I (I t2 t1) (E t1 t2))))");
    // !t. (t <=> T) \/ (t <=> F)
    self.parse_thm(Thm, "BOOL_CASES_AX", c::BOOL_CASES_AX,
      &[bool_ty], &["V \"t\" z1"],
      r#"U t1 (D (E t1 (K "T")) (E t1 (K "F")))"#);
    // T
    self.parse_thm(Thm, "TRUTH", c::TRUTH, &[], &[], "K \"T\"");
    // ~T <=> F
    self.parse_thm(Thm, "NOT_TRUE", c::NOT_TRUE, &[], &[], "E (N (K \"T\")) (K \"F\")");
    // !t. t \/ ~t
    self.parse_thm(Thm, "EXCLUDED_MIDDLE", c::EM,
      &[bool_ty], &["V \"t\" z1"], "U t1 (D t1 (N t1))");
    // !(x:A) (y:B) a b. x,y = a,b <=> x = a /\ y = b
    self.parse_thm(Thm, "PAIR_EQ", c::PAIR_EQ, &[a_ty, b_ty],
      &["V \"x\" z1", "V \"y\" z2", "V \"a\" z1", "V \"b\" z2"],
      "U t1 (U t2 (U t3 (U t4 (E (E (P t1 t2) (P t3 t4)) (C (E t1 t3) (E t2 t4))))))");
    // !p:A#B. ?x y. p = x,y
    self.parse_thm(Thm, "PAIR_SURJECTIVE", c::PAIR_SURJ,
      &[a_ty, b_ty, "K \"prod\" z1 z2"], &["V \"p\" z3", "V \"x\" z1", "V \"y\" z2"],
      "U t1 (X t2 (X t3 (E t1 (P t2 t3))))");
    // !x y. FST (x,y) = x
    self.parse_thm(Thm, "FST", c::FST_THM,
      &[a_ty, b_ty], &["V \"x\" z1", "V \"y\" z2"],
      "U t1 (U t2 (E (A (K \"FST\" z1 z2) (P t1 t2)) t1))");
    // !x y. SND (x,y) = y
    self.parse_thm(Thm, "SND", c::SND_THM,
      &[a_ty, b_ty], &["V \"x\" z1", "V \"y\" z2"],
      "U t1 (U t2 (E (A (K \"SND\" z1 z2) (P t1 t2)) t2))");
    // !x. ~(IND_SUC x = IND_0)
    self.parse_thm(Thm, "IND_SUC_0", c::IND_SUC_0,
      &[ind_ty], &["V \"x\" z1"],
      r#"U t1 (N (E (A (K "IND_SUC") t1) (K "IND_0")))"#);
    // !x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2
    self.parse_thm(Thm, "IND_SUC_INJ", c::IND_SUC_INJ,
      &[ind_ty], &["V \"x1\" z1", "V \"x2\" z1", "K \"IND_SUC\""],
      "U t1 (U t2 (E (E (A t3 t1) (A t3 t2)) (E t1 t2)))");
    // !n. ~(SUC n = 0)
    self.parse_thm(Thm, "NOT_SUC", c::NOT_SUC,
      &[num_ty], &["V \"n\" z1", "M 0", suc],
      r#"U t1 (N (E (A t3 t1) t2))"#);
    // !m n. SUC m = SUC n <=> m = n
    self.parse_thm(Thm, "SUC_INJ", c::SUC_INJ,
      &[num_ty], &["V \"m\" z1", "V \"n\" z1", suc],
      "U t1 (U t2 (E (E (A t3 t1) (A t3 t2)) (E t1 t2)))");
    // !m. m = 0 \/ (?n. m = SUC n)
    self.parse_thm(Thm, "num_CASES", c::NUM_CASES,
      &[num_ty], &["V \"m\" z1", "M 0", "V \"n\" z1", suc],
      "U t1 (D (E t1 t2) (X t3 (E t1 (A t4 t3))))");
    // !P. P 0 /\ (!n. P n ==> P (SUC n)) ==> (!n. P n)
    self.parse_thm(Thm, "num_INDUCTION", c::NUM_IND,
      &[num_ty, bool_ty, "F z1 z2"], &["V \"P\" z3", "V \"n\" z1", "M 0", suc],
      "U t1 (I (C (A t1 t3) (U t2 (I (A t1 t2) (A t1 (A t4 t2))))) (U t2 (A t1 t2)))");
    // !(e:A) (f:A->num->A). ?(fn:num->A). fn 0 = e /\ (!n. fn (SUC n) = f (fn n) n)
    self.parse_thm(Thm, "num_RECURSION", c::NUM_REC,
      &[a_ty, num_ty, "F z2 z1", "F z1 z3"],
      &["V \"e\" z1", "V \"f\" z4", "V \"fn\" z3", "M 0", "V \"n\" z2", suc],
      "U t1 (U t2 (X t3 (C (E (A t3 t4) t1) \
                           (U t5 (E (A t3 (A t6 t5)) (B t2 (A t3 t5) t5))))))");
    self.add_thm_alias(Thm, "PRE", pre);
    self.add_thm_alias(Thm, "ADD", add);
    self.add_thm_alias(Thm, "SUB", sub);
    // (!n. 0 * n = 0) /\ (!m n. SUC m * n = n + m * n)
    self.parse_thm(Thm, "MULT1", c::MUL1,
      &[num_ty], &["K \"*\"", "M 0", suc, "V \"m\" z1", "V \"n\" z1"],
      "C (U t5 (E (B t1 t2 t5) t2)) \
         (U t4 (U t5 (E (B t1 (A t3 t4) t5) (B (K \"+\") t5 (B t1 t4 t5)))))");
    self.add_thm_alias(Thm, "EXP", exp);
    self.add_thm_alias(Thm, "LT", lt);
    // !m n. m <= n <=> m < n \/ m = n
    self.parse_thm(Thm, "LE1", c::LE1, &[num_ty], &["V \"m\" z1", "V \"n\" z1"],
      r#"U t1 (U t2 (E (B (K "<=") t1 t2) (D (B (K "<") t1 t2) (E t1 t2))))"#);
    // !m n. m > n <=> n < m
    self.parse_thm(Thm, "GT1", c::GT1, &[num_ty], &["V \"m\" z1", "V \"n\" z1"],
      r#"U t1 (U t2 (E (B (K ">") t1 t2) (B (K "<") t2 t1)))"#);
    // !m n. m >= n <=> n <= m
    self.parse_thm(Thm, "GE1", c::GE1, &[num_ty], &["V \"m\" z1", "V \"n\" z1"],
      r#"U t1 (U t2 (E (B (K ">=") t1 t2) (B (K "<=") t2 t1)))"#);
    self.add_thm_alias(Thm, "EVEN", even);
    // !n. ODD n <=> ~EVEN n
    self.parse_thm(Thm, "ODD1", c::ODD1, &[num_ty], &["V \"n\" z1"],
      r#"U t1 (E (A (K "ODD") t1) (N (A (K "EVEN") t1))))"#);
  }
}

/*

This is the initial state of the HOL light proof kernel after the Common HOL prelude.
Any Common HOL files can reference these theorems and constants, so they have to be built
into the prover / prelude.

# types ();;
val it : (string * int) list =
  [("num", 0); ("ind", 0); ("prod", 2); ("bool", 0); ("fun", 2)]

# constants ();;
val it : (string * Platform.hol_type) list =
  [("TYPE_DEFINITION", `:(A->bool)->(B->A)->bool`); ("-", `:num->num->num`);
   ("ODD", `:num->bool`); ("EVEN", `:num->bool`); (">", `:num->num->bool`);
   (">=", `:num->num->bool`); ("<", `:num->num->bool`);
   ("<=", `:num->num->bool`); ("EXP", `:num->num->num`);
   ("*", `:num->num->num`); ("+", `:num->num->num`); ("PRE", `:num->num`);
   ("BIT1", `:num->num`); ("BIT0", `:num->num`); ("NUMERAL", `:num->num`);
   ("SUC", `:num->num`); ("_0", `:num`); ("dest_num", `:num->ind`);
   ("mk_num", `:ind->num`); ("NUM_REP", `:ind->bool`); ("IND_0", `:ind`);
   ("IND_SUC", `:ind->ind`); ("ONTO", `:(A->B)->bool`);
   ("ONE_ONE", `:(A->B)->bool`); ("SND", `:A#B->B`); ("FST", `:A#B->A`);
   (",", `:A->B->A#B`); ("REP_prod", `:A#B->A->B->bool`);
   ("ABS_prod", `:(A->B->bool)->A#B`); ("mk_pair", `:A->B->A->B->bool`);
   ("COND", `:bool->A->A->A`); ("@", `:(A->bool)->A`);
   ("?!", `:(A->bool)->bool`); ("~", `:bool->bool`); ("F", `:bool`);
   ("\\/", `:bool->bool->bool`); ("?", `:(A->bool)->bool`);
   ("!", `:(A->bool)->bool`); ("==>", `:bool->bool->bool`);
   ("/\\", `:bool->bool->bool`); ("T", `:bool`); ("=", `:A->A->bool`)]

# axioms1 ();;
val it : (string * Platform.thm) list =
  [("ETA_AX", |- !t. (\x. t x) = t);
   ("SELECT_AX", |- !P x. P x ==> P ((@) P));
   ("INFINITY_AX", |- ?f. ONE_ONE f /\ ~ONTO f)]

# basic_definitions ();;
val it : (string * Platform.thm) list =
  [("TYPE_DEFINITION",
    |- TYPE_DEFINITION =
       (\P rep. ONE_ONE rep /\ (!x. P x <=> (?y. x = rep y))));
   ("-", |- (-) = (@(-). (!m. m - 0 = m) /\ (!m n. m - SUC n = PRE (m - n))));
   ("ODD", |- ODD = (@ODD. (ODD 0 <=> F) /\ (!n. ODD (SUC n) <=> ~ODD n)));
   ("EVEN",
    |- EVEN = (@EVEN. (EVEN 0 <=> T) /\ (!n. EVEN (SUC n) <=> ~EVEN n)));
   (">", |- (>) = (\_82 _83. _83 < _82));
   (">=", |- (>=) = (\_70 _71. _71 <= _70));
   ("<",
    |- (<) =
       (@(<). (!m. m < 0 <=> F) /\ (!m n. m < SUC n <=> m = n \/ m < n)));
   ("<=",
    |- (<=) =
       (@(<=). (!m. m <= 0 <=> m = 0) /\
               (!m n. m <= SUC n <=> m = SUC n \/ m <= n)));
   ("EXP",
    |- (EXP) =
       (@(EXP). (!m. m EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n)));
   ("*", |- (*) = (@(*). (!n. 0 * n = 0) /\ (!m n. SUC m * n = m * n + n)));
   ("+", |- (+) = (@(+). (!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n))));
   ("PRE", |- PRE = (@PRE. PRE 0 = 0 /\ (!n. PRE (SUC n) = n)));
   ("BIT1", |- BIT1 = (\_32. SUC (BIT0 _32)));
   ("BIT0", |- BIT0 = (@fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC (fn n)))));
   ("NUMERAL", |- NUMERAL = (\_19. _19));
   ("SUC", |- SUC = (\_14. mk_num (IND_SUC (dest_num _14))));
   ("_0", |- _0 = mk_num IND_0);
   ("NUM_REP",
    |- NUM_REP =
       (\k. !P. (!j. j = IND_0 \/ (?i. j = IND_SUC i /\ P i) ==> P j) ==> P k));
   ("IND_0",
    |- IND_0 =
       (@z. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\
            (!x. ~(IND_SUC x = z))));
   ("IND_SUC",
    |- IND_SUC =
       (@f. ?z. (!x1 x2. f x1 = f x2 <=> x1 = x2) /\ (!x. ~(f x = z))));
   ("ONTO", |- ONTO = (\_5. !y. ?x. y = _5 x));
   ("ONE_ONE", |- ONE_ONE = (\_0. !x1 x2. _0 x1 = _0 x2 ==> x1 = x2));
   ("SND", |- SND = (\p. @y. ?x. p = x,y));
   ("FST", |- FST = (\p. @x. ?y. p = x,y));
   (",", |- (,) = (\x y. ABS_prod (mk_pair x y)));
   ("mk_pair", |- mk_pair = (\x y a b. a = x /\ b = y));
   ("COND",
    |- COND =
       (\t t1 t2. @x. ((t <=> T) ==> x = t1) /\ ((t <=> F) ==> x = t2)));
   ("?!", |- (?!) = (\P. (?) P /\ (!x y. P x /\ P y ==> x = y)));
   ("~", |- (~) = (\p. p ==> F)); ("F", |- F <=> (!p. p));
   ("\\/", |- (\/) = (\p q. !r. (p ==> r) ==> (q ==> r) ==> r));
   ("?", |- (?) = (\P. !q. (!x. P x ==> q) ==> q));
   ("!", |- (!) = (\P. P = (\x. T)));
   ("==>", |- (==>) = (\p q. p /\ q <=> p));
   ("/\\", |- (/\) = (\p q. (\f. f p q) = (\f. f T T)));
   ("T", |- T <=> (\p. p) = (\p. p))]

# basic_type_definitions1 ();;
val it : (string * Platform.thm) list =
  [("num", |- ?f. TYPE_DEFINITION NUM_REP f);
   ("prod", |- ?f. TYPE_DEFINITION (\x. ?a b. x = mk_pair a b) f)]

# definitions1 ();;
val it : (string * Platform.thm) list =
  [("-", |- (-) = (@(-). (!m. m - 0 = m) /\ (!m n. m - SUC n = PRE (m - n))));
   ("ODD", |- ODD = (@ODD. (ODD 0 <=> F) /\ (!n. ODD (SUC n) <=> ~ODD n)));
   ("EVEN",
    |- EVEN = (@EVEN. (EVEN 0 <=> T) /\ (!n. EVEN (SUC n) <=> ~EVEN n)));
   (">", |- !m n. m > n <=> n < m); (">=", |- !m n. m >= n <=> n <= m);
   ("<",
    |- (<) =
       (@(<). (!m. m < 0 <=> F) /\ (!m n. m < SUC n <=> m = n \/ m < n)));
   ("<=",
    |- (<=) =
       (@(<=). (!m. m <= 0 <=> m = 0) /\
               (!m n. m <= SUC n <=> m = SUC n \/ m <= n)));
   ("EXP",
    |- (EXP) =
       (@(EXP). (!m. m EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n)));
   ("*", |- (*) = (@(*). (!n. 0 * n = 0) /\ (!m n. SUC m * n = m * n + n)));
   ("+", |- (+) = (@(+). (!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n))));
   ("PRE", |- PRE = (@PRE. PRE 0 = 0 /\ (!n. PRE (SUC n) = n)));
   ("BIT1", |- !n. BIT1 n = SUC (BIT0 n));
   ("BIT0", |- BIT0 = (@fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC (fn n)))));
   ("NUMERAL", |- !n. NUMERAL n = n);
   ("SUC", |- !n. SUC n = mk_num (IND_SUC (dest_num n)));
   ("_0", |- _0 = mk_num IND_0);
   ("IND_0",
    |- IND_0 =
       (@z. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\
            (!x. ~(IND_SUC x = z))));
   ("IND_SUC",
    |- IND_SUC =
       (@f. ?z. (!x1 x2. f x1 = f x2 <=> x1 = x2) /\ (!x. ~(f x = z))));
   ("ONTO", |- !f. ONTO f <=> (!y. ?x. y = f x));
   ("ONE_ONE", |- !f. ONE_ONE f <=> (!x1 x2. f x1 = f x2 ==> x1 = x2))]

# specifications ();;
val it : (string list * Platform.thm) list =
  [(["-"], |- (!m. m - 0 = m) /\ (!m n. m - SUC n = PRE (m - n)));
   (["ODD"], |- (ODD 0 <=> F) /\ (!n. ODD (SUC n) <=> ~ODD n));
   (["EVEN"], |- (EVEN 0 <=> T) /\ (!n. EVEN (SUC n) <=> ~EVEN n));
   (["<"], |- (!m. m < 0 <=> F) /\ (!m n. m < SUC n <=> m = n \/ m < n));
   (["<="],
    |- (!m. m <= 0 <=> m = 0) /\ (!m n. m <= SUC n <=> m = SUC n \/ m <= n));
   (["EXP"], |- (!m. m EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n));
   (["*"], |- (!n. 0 * n = 0) /\ (!m n. SUC m * n = m * n + n));
   (["+"], |- (!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n)));
   (["PRE"], |- PRE 0 = 0 /\ (!n. PRE (SUC n) = n))]

# type_bijections_info ();;
val it : (string * ((string * string) * (Platform.thm * Platform.thm))) list =
  [("num",
    (("mk_num", "dest_num"),
     (|- !a. mk_num (dest_num a) = a,
      |- !r. NUM_REP r <=> dest_num (mk_num r) = r)));
   ("prod",
    (("ABS_prod", "REP_prod"),
     (|- !a. ABS_prod (REP_prod a) = a,
      |- !r. (\x. ?a b. x = mk_pair a b) r <=> REP_prod (ABS_prod r) = r)))]

# theorems1 ();;
val it : (string * Platform.thm) list =
  [("ADD", |- (!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n)));
   ("AND_DEF1", |- (/\) = (\p q. !t. (p ==> q ==> t) ==> t));
   ("BOOL_CASES_AX", |- !t. (t <=> T) \/ (t <=> F));
   ("EVEN", |- (EVEN 0 <=> T) /\ (!n. EVEN (SUC n) <=> ~EVEN n));
   ("EXCLUDED_MIDDLE", |- !t. t \/ ~t);
   ("EXISTS_THM", |- (?) = (\P. P ((@) P)));
   ("EXISTS_UNIQUE_DEF1", |- (?!) = (\P. ?t. P t /\ (!x. P x ==> x = t)));
   ("EXP", |- (!m. m EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n));
   ("FST", |- !x y. FST (x,y) = x); ("GE1", |- !m n. m >= n <=> n <= m);
   ("GT1", |- !m n. m > n <=> n < m);
   ("IMP_ANTISYM_AX", |- !t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 <=> t2));
   ("IND_SUC_0", |- !x. ~(IND_SUC x = IND_0));
   ("IND_SUC_INJ", |- !x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2);
   ("LE1", |- !m n. m <= n <=> m < n \/ m = n);
   ("LT", |- (!m. m < 0 <=> F) /\ (!m n. m < SUC n <=> m = n \/ m < n));
   ("MULT1", |- (!n. 0 * n = 0) /\ (!m n. SUC m * n = n + m * n));
   ("NOT_SUC", |- !n. ~(SUC n = 0)); ("NOT_TRUE", |- ~T <=> F);
   ("ODD1", |- !n. ODD n <=> ~EVEN n);
   ("PAIR_EQ", |- !x y a b. x,y = a,b <=> x = a /\ y = b);
   ("PAIR_SURJECTIVE", |- !p. ?x y. p = x,y);
   ("PRE", |- PRE 0 = 0 /\ (!n. PRE (SUC n) = n));
   ("SND", |- !x y. SND (x,y) = y);
   ("SUB", |- (!m. m - 0 = m) /\ (!m n. m - SUC n = PRE (m - n)));
   ("SUC_INJ", |- !m n. SUC m = SUC n <=> m = n); ("TRUTH", |- T);
   ("num_CASES", |- !m. m = 0 \/ (?n. m = SUC n));
   ("num_INDUCTION", |- !P. P 0 /\ (!n. P n ==> P (SUC n)) ==> (!n. P n));
   ("num_RECURSION", |- !e f. ?fn. fn 0 = e /\ (!n. fn (SUC n) = f (fn n) n))]

# otheorems ();;
val it : (string * Platform.thm) list = []

# ntheorems ();;
val it : (int * Platform.thm) list = []

*/