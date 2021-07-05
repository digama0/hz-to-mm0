use crate::kernel::Environment;
use crate::types::{ConstDef, ConstId, FetchKind, ThmDef, TydefData, TyopDef, TyopId};

impl TyopId {
  pub const BOOL: Self = Self(0);
  pub const FUN: Self = Self(1);
  pub const PROD: Self = Self(2); // FIXME
}

impl ConstId {
  pub const CONJ: Self = Self(0); // FIXME
  pub const DISJ: Self = Self(0); // FIXME
  pub const IMP: Self = Self(0); // FIXME
  pub const NOT: Self = Self(0); // FIXME
  pub const EQ: Self = Self(0); // FIXME
  pub const PAIR: Self = Self(0); // FIXME
  pub const FORALL: Self = Self(0); // FIXME
  pub const EXISTS: Self = Self(0); // FIXME
  pub const UEXISTS: Self = Self(0); // FIXME
  pub const SELECT: Self = Self(0); // FIXME
  pub const NUMERAL: Self = Self(0); // FIXME
  pub const ZERO: Self = Self(0); // FIXME
  pub const BIT0: Self = Self(0); // FIXME
  pub const BIT1: Self = Self(0); // FIXME
}

impl Environment {

  pub fn new() -> Self {
    use FetchKind::*;
    let mut env = Self::default();
    assert_eq!(TyopId::BOOL, env.add_tyop("bool", 0, None));
    assert_eq!(TyopId::FUN, env.add_tyop("fun", 2, None));
    let bool_ty = "K \"bool\"";
    let num_ty = "K \"num\"";
    let p_tm = "V \"p\" z1";
    let q_tm = "V \"q\" z1";
    let r_tm = "V \"r\" z1";
    let a_ty = "V \"A\"";
    let b_ty = "V \"B\"";
    let vx = "V \"x\" z1";
    let vy = "V \"y\" z2";
    let vn = "V \"n\" z1";
    env.parse_const("=", &[a_ty], "F z1 (F z1 (K \"bool\"))");
    env.parse_const("@", &[a_ty], "F (F z1 (K \"bool\")) z1");
    // T = ((\p:bool. p) = (\p:bool. p))
    env.parse_basic_def("T", &[bool_ty], &[p_tm, "L t1 t1"], "E t2 t2");
    // (/\) = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)
    env.parse_basic_def("/\\", &[bool_ty, "F z1 (F z1 z1)"],
      &[p_tm, q_tm, "V \"f\" z2", "K \"T\""],
      "L t1 (L t2 (E (L t3 (A (A t3 t1) t2)) (L t3 (A (A t3 t4) t4))))");
    // (==>) = \p q. p /\ q <=> p
    env.parse_basic_def("==>", &[bool_ty], &[p_tm, q_tm], "L t1 (L t2 (E (C t1 t2) t1))");
    // (!) = \P:A->bool. P = \x. T
    env.parse_basic_def("!", &[a_ty, "F z1 (K \"bool\")"], &["V \"P\" z2"],
      "L t1 (E t1 (L (V \"x\" z1) (K \"T\")))");
    // (?) = \P:A->bool. !q. (!x. P x ==> q) ==> q
    env.parse_basic_def("?", &[bool_ty, a_ty, "F z2 z1"],
      &["V \"P\" z3", q_tm, "V \"x\" z2"],
      r#"L t1 (U t2 (I (U t3 (I (A t1 t3) t2)) t2))"#);
    // (\/) = \p q. !r. (p ==> r) ==> (q ==> r) ==> r
    env.parse_basic_def("\\/", &[bool_ty], &[p_tm, q_tm, r_tm],
      "L t1 (L t2 (U t3 (I (I t1 t3) (I (I t2 t3) t3))))");
    // F = !p:bool. p
    env.parse_basic_def("F", &[bool_ty], &[p_tm], "U t1 t1");
    // (~) = \p. p ==> F
    env.parse_basic_def("~", &[bool_ty], &[p_tm], "L t1 (I t1 (K \"F\"))");
    // (?!) = \P:A->bool. (?) P /\ (!x y. P x /\ P y ==> x = y)
    env.parse_basic_def("?!", &[a_ty, "F z1 (K \"bool\")"],
      &["V \"P\" z2", vx, "V \"y\" z1"],
      r#"L t1 (C (A (K "?" z1) t1) (U t2 (U t3 (I (C (A t1 t2) (A t1 t3)) (E t2 t3)))))"#);
    // COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ ((t <=> F) ==> (x = t2))
    env.parse_basic_def("COND", &[bool_ty, a_ty],
      &["V \"t\" z1", "V \"t1\" z2", "V \"t2\" z2", "V \"x\" z2",
        "I (E t1 (K \"T\")) (E t4 t2)", "I (E t1 (K \"F\")) (E t4 t3)"],
      "L t1 (L t2 (L t3 (S t4 (C t5 t6))))");
    // ONE_ONE = \f:A->B. !x1 x2. (f x1 = f x2) ==> (x1 = x2)
    env.parse_basic_def("ONE_ONE", &[a_ty, b_ty, "F z1 z2"],
      &["V \"x1\" z1", "V \"x2\" z1", "V \"f\" z3"],
      "L t3 (U t1 (U t2 (I (E (A t3 t1) (A t3 t2)) (E t1 t2))))");
    // ONTO = \f:A->B. !y. ?x. y = f x
    env.parse_basic_def("ONTO", &[a_ty, b_ty, "F z1 z2"],
      &[vx, vy, "V \"f\" z3"],
      "L t3 (U t2 (X t1 (E t2 (A t3 t1))))");
    env.add_tyop("ind", 0, None);
    // (,) = \(x:A) (y:B). ABS_prod(mk_pair x y)
    env.parse_basic_def(",", &[a_ty, b_ty], &[vx, vy],
      r#"L t1 (L t2 (A (K "ABS_prod" z1 z2) (B (K "mk_pair" z1 z2) t1 t2)))"#);
    // FST = \p:A#B. @x. ?y. p = x,y
    env.parse_basic_def("FST", &[a_ty, b_ty, "K \"prod\" z1 z2"], &["V \"p\" z3", vx, vy],
      "L t1 (S t2 (X t3 (E t1 (P t2 t3))))");
    // SND = \p:A#B. @y. ?x. p = x,y`
    env.parse_basic_def("SND", &[a_ty, b_ty, "K \"prod\" z1 z2"], &["V \"p\" z3", vx, vy],
      "L t1 (S t3 (X t2 (E t1 (P t2 t3))))");
    env.parse_const("IND_0", &[], "K \"ind\"");
    env.parse_const("IND_SUC", &["K \"ind\""], "F z1 z1");
    // _0 = mk_num IND_0
    assert_eq!(ConstId::ZERO,
      env.parse_basic_def("_0", &[], &[], "A (K \"mk_num\") (K \"IND_0\")").0);
    // SUC = \n. mk_num(IND_SUC(dest_num n))
    env.parse_basic_def("SUC", &[num_ty], &[vn],
      r#"L t1 (A (K "mk_num") (A (K "IND_SUC") (A (K "dest_num") t1)))"#);
    // env.add_const("PRE", ConstDef);
    // env.add_const("+", ConstDef);
    // env.add_const("-", ConstDef);
    // env.add_const("*", ConstDef);
    // env.add_const("EXP", ConstDef);
    // env.add_const("EVEN", ConstDef);
    // env.add_const("ODD", ConstDef);
    // NUMERAL = \n:num. n
    assert_eq!(ConstId::NUMERAL, env.parse_basic_def("NUMERAL",
      &[num_ty], &[vn], "L t1 t1").0);
    // BIT0 = @fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC(fn n)))
    assert_eq!(ConstId::BIT0, env.parse_basic_def("BIT0",
      &[num_ty, "F z1 z1"], &["V \"fn\" z2", vn, "K \"SUC\"", "M 0"],
      "S t1 (C (E (A t1 t4) t4) (U t2 (E (A t1 (A t3 t2)) (A t3 (A t3 (A t1 t2))))))").0);
    // BIT1 = \n. SUC (BIT0 n)
    assert_eq!(ConstId::BIT1, env.parse_basic_def("BIT1",
      &[num_ty], &[vn], "L t1 (A (K \"SUC\") (A (K \"BIT0\") t1))").0);
    // NUM_REP = \k. !P. P IND_0 /\ (!j. P j ==> P (IND_SUC j)) ==> P i
    env.parse_basic_def("NUM_REP", &["K \"ind\"", "F z1 (K \"bool\")"],
      &["V \"k\" z1", "V \"P\" z2", "V \"j\" z1", "V \"i\" z1",
        r#"(D (E t3 (K "IND_0")) (X t4 (C (E t3 (A (K "IND_SUC") t4)) (A t2 t4))))"#],
      "L t1 (U t2 (I (U t3 (I t5 (A t2 t3))) (A t2 t1)))");
    // num = basic_typedef [?k:ind. NUM_REP k]
    let num = env.parse_basic_typedef("num", &["K \"ind\""], &["V \"k\" z1"],
      "E t1 (A (K \"NUM_REP\") t1)");
    env.add_type_bijs(num, "num", "mk_num", "dest_num");
    // mk_pair = \(x:A) (y:B) a b. (a = x) /\ (b = y)
    env.parse_basic_def("mk_pair", &[a_ty, b_ty], &[vx, vy, "V \"a\" z1", "V \"b\" z2"],
      "L t1 (L t2 (L t3 (L t4 (C (E t3 t1) (E t4 t2)))))");
    let prod = env.parse_basic_typedef("prod", &["K \"ind\""], &["V \"k\" z1"],
      "E t1 (A (K \"NUM_REP\") t1)");
    env.add_type_bijs(prod, "prod", "ABS_prod", "REP_prod");
    // env.add_thm(Thm, "AND_DEF1", ThmDef);
    env.add_thm(Thm, "EXISTS_THM", ThmDef::default());
    env.add_thm(Thm, "EXISTS_UNIQUE_DEF1", ThmDef::default());
    env.add_thm(Axiom, "ETA_AX", ThmDef::default());
    // env.add_thm(Thm, "IMP_ANTISYM_AX", ThmDef::default());
    env.add_thm(Thm, "BOOL_CASES_AX", ThmDef::default());
    env.add_thm(Axiom, "SELECT_AX", ThmDef::default());
    env.add_thm(Thm, "TRUTH", ThmDef::default());
    env.add_thm(Thm, "NOT_TRUE", ThmDef::default());
    env.add_thm(Thm, "EXCLUDED_MIDDLE", ThmDef::default());
    env.add_thm(Thm, "PAIR_EQ", ThmDef::default());
    env.add_thm(Thm, "PAIR_SURJECTIVE", ThmDef::default());
    env.add_thm(Thm, "FST", ThmDef::default());
    env.add_thm(Thm, "SND", ThmDef::default());
    env.add_thm(Axiom, "INFINITY_AX", ThmDef::default());
    env.add_thm(Thm, "IND_SUC_0", ThmDef::default());
    env.add_thm(Thm, "IND_SUC_INJ", ThmDef::default());
    env.add_thm(Thm, "NOT_SUC", ThmDef::default());
    env.add_thm(Thm, "SUC_INJ", ThmDef::default());
    env.add_thm(Thm, "num_CASES", ThmDef::default());
    env.add_thm(Thm, "num_INDUCTION", ThmDef::default());
    env.add_thm(Thm, "num_RECURSION", ThmDef::default());
    env.add_thm(Thm, "PRE", ThmDef::default());
    env.add_thm(Thm, "ADD", ThmDef::default());
    env.add_thm(Thm, "SUB", ThmDef::default());
    env.add_thm(Thm, "MULT1", ThmDef::default());
    env.add_thm(Thm, "EXP", ThmDef::default());
    env.add_thm(Thm, "LT", ThmDef::default());
    env.add_thm(Thm, "LE1", ThmDef::default());
    env.add_thm(Thm, "GT1", ThmDef::default());
    env.add_thm(Thm, "GE1", ThmDef::default());
    env.add_thm(Thm, "EVEN", ThmDef::default());
    env.add_thm(Thm, "ODD1", ThmDef::default());
    env
  }
}
