use crate::kernel::Environment;
use crate::types::{ConstDef, FetchKind, ThmDef, TyopDef};

impl Environment {

  pub fn new() -> Self {
    use FetchKind::*;
    let mut env = Self::default();
    env.add_tyop("bool", TyopDef {arity: 0});
    let bool_ty = "K \"bool\"";
    let num_ty = "K \"num\"";
    let p_tm = "V \"p\" z1";
    let a_ty = "V \"A\"";
    let b_ty = "V \"B\"";
    let vx = "V \"x\" z1";
    let vy = "V \"y\" z2";
    let vn = "V \"n\" z1";
    env.add_tyop("fun", TyopDef {arity: 2});
    env.add_tyop("ind", TyopDef {arity: 0});
    // T = ((\p:bool. p) = (\p:bool. p))
    env.parse_basic_def("T", &[bool_ty], &[p_tm, "L t1 t1"], "E t2 t2");
    // env.parse_basic_def("F", &[], &[], "TODO");
    // env.parse_basic_def("==>", &[], &[], "TODO");
    // env.add_const("/\\", ConstDef);
    // env.parse_basic_def("\\/", &[], &[], "TODO");
    // (~) = \p. p ==> F
    env.parse_basic_def("~", &[bool_ty], &[p_tm], "L t1 (I t1 (K \"F\"))");
    // (!) = \P:A->bool. P = \x. T
    env.parse_basic_def("!", &[a_ty, "F z1 (K \"bool\")"], &["V \"P\" z2"],
      "L t1 (E t1 (L (V \"x\" z1) (K \"T\")))");
    // env.add_const("?", ConstDef);
    // env.add_const("?!", ConstDef);
    // env.add_const("=", ConstDef);
    // env.add_const("@", ConstDef);
    // env.parse_basic_def("TYPE_DEFINITION", &[], &[], "TODO");
    // ONE_ONE = \f:A->B. !x1 x2. (f x1 = f x2) ==> (x1 = x2)
    env.parse_basic_def("ONE_ONE", &[a_ty, b_ty, "F z1 z2"],
      &["V \"x1\" z1", "V \"x2\" z1", "V \"f\" z3"],
      "L t3 (U t1 (U t2 (I (E (A t3 t1) (A t3 t2)) (E t1 t2))))");
    // ONTO = \f:A->B. !y. ?x. y = f x
    env.parse_basic_def("ONTO", &[a_ty, b_ty, "F z1 z2"],
      &[vx, vy, "V \"f\" z3"],
      "L t3 (U t2 (X t1 (E t2 (A t3 t1))))");
    // COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ ((t <=> F) ==> (x = t2))
    env.parse_basic_def("COND", &[bool_ty, a_ty],
      &["V \"t\" z1", "V \"t1\" z2", "V \"t2\" z2", "V \"x\" z2",
        "I (E t1 (K \"T\")) (E t4 t2)", "I (E t1 (K \"F\")) (E t4 t3)"],
      "L t1 (L t2 (L t3 (S t4 (C t5 t6))))");
    // (,) = \(x:A) (y:B). ABS_prod(mk_pair x y)
    env.parse_basic_def(",", &[a_ty, b_ty], &[vx, vy],
      r#"L t1 (L t2 (A (K "ABS_prod" z1 z2) (B (K "mk_pair" z1 z2) t1 t2)))"#);
    // FST = \p:A#B. @x. ?y. p = x,y
    env.parse_basic_def("FST", &[a_ty, b_ty, "K \"prod\" z1 z2"], &["V \"p\" z3", vx, vy],
      "L t1 (S t2 (X t3 (E t1 (P t2 t3))))");
    // SND = \p:A#B. @y. ?x. p = x,y`
    env.parse_basic_def("SND", &[a_ty, b_ty, "K \"prod\" z1 z2"], &["V \"p\" z3", vx, vy],
      "L t1 (S t3 (X t2 (E t1 (P t2 t3))))");
    env.add_const("IND_0", ConstDef {});
    env.add_const("IND_SUC", ConstDef {});
    // _0 = mk_num IND_0
    env.parse_basic_def("_0", &[], &[], "A (K \"mk_num\") (K \"IND_0\")");
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
    env.parse_basic_def("NUMERAL", &[num_ty], &[vn], "L t1 t1");
    // BIT0 = @fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC(fn n)))
    env.parse_basic_def("BIT0", &[num_ty, "F z1 z1"],
      &["V \"fn\" z2", vn, "K \"SUC\"", "M 0"],
      "S t1 (C (E (A t1 t4) t4) (U t2 (E (A t1 (A t3 t2)) (A t3 (A t3 (A t1 t2))))))");
    // BIT1 = \n. SUC (BIT0 n)
    env.parse_basic_def("BIT1", &[num_ty], &[vn], "L t1 (A (K \"SUC\") (A (K \"BIT0\") t1))");
    env.add_type_bijs("num", "mk_num", "dest_num");
    // NUM_REP = \k. !P. P IND_0 /\ (!j. P j ==> P (IND_SUC j)) ==> P i
    env.parse_basic_def("NUM_REP", &["K \"ind\"", "F z1 (K \"bool\")"],
      &["V \"k\" z1", "V \"P\" z2", "V \"j\" z1", "V \"i\" z1",
        r#"(D (E t3 (K "IND_0")) (X t4 (C (E t3 (A (K "IND_SUC") t4)) (A t2 t4))))"#],
      "L t1 (U t2 (I (U t3 (I t5 (A t2 t3))) (A t2 t1)))");
    // env.add_tyop("prod", TyopDef {arity: 2});
    // mk_pair = \(x:A) (y:B) a b. (a = x) /\ (b = y)
    env.parse_basic_def("mk_pair", &[a_ty, b_ty], &[vx, vy, "V \"a\" z1", "V \"b\" z2"],
      "L t1 (L t2 (L t3 (L t4 (C (E t3 t1) (E t4 t2)))))");
    env.add_type_bijs("prod", "ABS_prod", "REP_prod");
    // env.add_thm(Thm, "AND_DEF1", ThmDef);
    env.add_thm(Thm, "EXISTS_THM", ThmDef {});
    env.add_thm(Thm, "EXISTS_UNIQUE_DEF1", ThmDef {});
    env.add_thm(Axiom, "ETA_AX", ThmDef {});
    // env.add_thm(Thm, "IMP_ANTISYM_AX", ThmDef {});
    env.add_thm(Thm, "BOOL_CASES_AX", ThmDef {});
    env.add_thm(Axiom, "SELECT_AX", ThmDef {});
    env.add_thm(Thm, "TRUTH", ThmDef {});
    env.add_thm(Thm, "NOT_TRUE", ThmDef {});
    env.add_thm(Thm, "EXCLUDED_MIDDLE", ThmDef {});
    env.add_thm(Thm, "PAIR_EQ", ThmDef {});
    env.add_thm(Thm, "PAIR_SURJECTIVE", ThmDef {});
    env.add_thm(Thm, "FST", ThmDef {});
    env.add_thm(Thm, "SND", ThmDef {});
    env.add_thm(Axiom, "INFINITY_AX", ThmDef {});
    env.add_thm(Thm, "IND_SUC_0", ThmDef {});
    env.add_thm(Thm, "IND_SUC_INJ", ThmDef {});
    env.add_thm(Thm, "NOT_SUC", ThmDef {});
    env.add_thm(Thm, "SUC_INJ", ThmDef {});
    env.add_thm(Thm, "num_CASES", ThmDef {});
    env.add_thm(Thm, "num_INDUCTION", ThmDef {});
    env.add_thm(Thm, "num_RECURSION", ThmDef {});
    env.add_thm(Thm, "PRE", ThmDef {});
    env.add_thm(Thm, "ADD", ThmDef {});
    env.add_thm(Thm, "SUB", ThmDef {});
    env.add_thm(Thm, "MULT1", ThmDef {});
    env.add_thm(Thm, "EXP", ThmDef {});
    env.add_thm(Thm, "LT", ThmDef {});
    env.add_thm(Thm, "LE1", ThmDef {});
    env.add_thm(Thm, "GT1", ThmDef {});
    env.add_thm(Thm, "GE1", ThmDef {});
    env.add_thm(Thm, "EVEN", ThmDef {});
    env.add_thm(Thm, "ODD1", ThmDef {});
    env
  }
}
