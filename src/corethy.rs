use crate::kernel::Environment;
use crate::types::{ConstId, FetchKind, ThmDef, TyopId};

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
    env.add_thm(Axiom, "ETA_AX", ThmDef::default());
    env.parse_const("@", &[a_ty], "F (F z1 (K \"bool\")) z1");
    env.add_thm(Axiom, "SELECT_AX", ThmDef::default());
    // COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\ ((t <=> F) ==> (x = t2))
    env.parse_basic_def("COND", &[bool_ty, a_ty],
      &["V \"t\" z1", "V \"t1\" z2", "V \"t2\" z2", "V \"x\" z2",
        "I (E t1 (K \"T\")) (E t4 t2)", "I (E t1 (K \"F\")) (E t4 t3)"],
      "L t1 (L t2 (L t3 (S t4 (C t5 t6))))");
    // mk_pair = \(x:A) (y:B) a b. (a = x) /\ (b = y)
    env.parse_basic_def("mk_pair", &[a_ty, b_ty], &[vx, vy, "V \"a\" z1", "V \"b\" z2"],
      "L t1 (L t2 (L t3 (L t4 (C (E t3 t1) (E t4 t2)))))");
    let prod = env.parse_basic_typedef("prod", &["K \"ind\""], &["V \"k\" z1"],
      "E t1 (A (K \"NUM_REP\") t1)");
    env.add_type_bijs(prod, "prod", "ABS_prod", "REP_prod");
    // (,) = \(x:A) (y:B). ABS_prod(mk_pair x y)
    env.parse_basic_def(",", &[a_ty, b_ty], &[vx, vy],
      r#"L t1 (L t2 (A (K "ABS_prod" z1 z2) (B (K "mk_pair" z1 z2) t1 t2)))"#);
    // FST = \p:A#B. @x. ?y. p = x,y
    env.parse_basic_def("FST", &[a_ty, b_ty, "K \"prod\" z1 z2"], &["V \"p\" z3", vx, vy],
      "L t1 (S t2 (X t3 (E t1 (P t2 t3))))");
    // SND = \p:A#B. @y. ?x. p = x,y`
    env.parse_basic_def("SND", &[a_ty, b_ty, "K \"prod\" z1 z2"], &["V \"p\" z3", vx, vy],
      "L t1 (S t3 (X t2 (E t1 (P t2 t3))))");
    env.add_tyop("ind", 0, None);
    // env.parse_def("ONE_ONE", "!f. ONE_ONE f <=> (!x1 x2. f x1 = f x2 ==> x1 = x2)");
    // ONE_ONE = \f:A->B. !x1 x2. (f x1 = f x2) ==> (x1 = x2)
    env.parse_basic_def("ONE_ONE", &[a_ty, b_ty, "F z1 z2"],
      &["V \"x1\" z1", "V \"x2\" z1", "V \"f\" z3"],
      "L t3 (U t1 (U t2 (I (E (A t3 t1) (A t3 t2)) (E t1 t2))))");
    // env.parse_def("ONTO", "!f. ONTO f <=> (!y. ?x. y = f x)");
    // ONTO = \f:A->B. !y. ?x. y = f x
    env.parse_basic_def("ONTO", &[a_ty, b_ty, "F z1 z2"],
      &[vx, vy, "V \"f\" z3"],
      "L t3 (U t2 (X t1 (E t2 (A t3 t1))))");
    env.add_thm(Axiom, "INFINITY_AX", ThmDef::default());
    // env.parse_def("IND_SUC",
    //   "IND_SUC = (@f. ?z. (!x1 x2. f x1 = f x2 <=> x1 = x2) /\ (!x. ~(f x = z)))");
    env.parse_const("IND_SUC", &["K \"ind\""], "F z1 z1");
    // env.parse_def("IND_0",
    //   "IND_0 = (@z. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\ (!x. ~(IND_SUC x = z)))");
    env.parse_const("IND_0", &[], "K \"ind\"");
    // NUM_REP = \k. !P. P IND_0 /\ (!j. P j ==> P (IND_SUC j)) ==> P i
    env.parse_basic_def("NUM_REP", &["K \"ind\"", "F z1 (K \"bool\")"],
      &["V \"k\" z1", "V \"P\" z2", "V \"j\" z1", "V \"i\" z1",
        r#"(D (E t3 (K "IND_0")) (X t4 (C (E t3 (A (K "IND_SUC") t4)) (A t2 t4))))"#],
      "L t1 (U t2 (I (U t3 (I t5 (A t2 t3))) (A t2 t1)))");
    // num = basic_typedef [?k:ind. NUM_REP k]
    let num = env.parse_basic_typedef("num", &["K \"ind\""], &["V \"k\" z1"],
      "E t1 (A (K \"NUM_REP\") t1)");
    env.add_type_bijs(num, "num", "mk_num", "dest_num");
    // env.parse_def("_0", "mk_num IND_0");
    // _0 = mk_num IND_0
    assert_eq!(ConstId::ZERO,
      env.parse_basic_def("_0", &[], &[], "A (K \"mk_num\") (K \"IND_0\")").0);
    // env.parse_def("SUC", "!n. SUC n = mk_num (IND_SUC (dest_num n))");
    // SUC = \n. mk_num (IND_SUC (dest_num n))
    env.parse_basic_def("SUC", &[num_ty], &[vn],
      r#"L t1 (A (K "mk_num") (A (K "IND_SUC") (A (K "dest_num") t1)))"#);
    // env.parse_def("NUMERAL", "!n. NUMERAL n = n");
    // NUMERAL = \n:num. n
    assert_eq!(ConstId::NUMERAL, env.parse_basic_def("NUMERAL",
      &[num_ty], &[vn], "L t1 t1").0);
    // env.parse_def("BIT0", "BIT0 = (@fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC (fn n))))");
    // BIT0 = @fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC(fn n)))
    assert_eq!(ConstId::BIT0, env.parse_basic_def("BIT0",
      &[num_ty, "F z1 z1"], &["V \"fn\" z2", vn, "K \"SUC\"", "M 0"],
      "S t1 (C (E (A t1 t4) t4) (U t2 (E (A t1 (A t3 t2)) (A t3 (A t3 (A t1 t2))))))").0);
    // env.parse_def("BIT1", "!n. BIT1 n = SUC (BIT0 n)");
    // BIT1 = \n. SUC (BIT0 n)
    assert_eq!(ConstId::BIT1, env.parse_basic_def("BIT1",
      &[num_ty], &[vn], "L t1 (A (K \"SUC\") (A (K \"BIT0\") t1))").0);
    // env.add_spec("PRE", "PRE 0 = 0 /\ (!n. PRE (SUC n) = n))");
    // env.add_spec("+", "(!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n))");
    // env.add_spec("*", "(!n. 0 * n = 0) /\ (!m n. SUC m * n = m * n + n)");
    // env.add_spec("EXP", "(!m. m EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n)");
    // env.add_spec("<=", "(!m. m <= 0 <=> m = 0) /\ (!m n. m <= SUC n <=> m = SUC n \/ m <= n)");
    // env.add_spec("<", "(!m. m < 0 <=> F) /\ (!m n. m < SUC n <=> m = n \/ m < n)");
    // env.add_def(">=", "!m n. m >= n <=> n <= m");
    // env.add_def(">", "!m n. m > n <=> n < m");
    // env.add_spec("EVEN", "(EVEN 0 <=> T) /\ (!n. EVEN (SUC n) <=> ~EVEN n)");
    // env.add_spec("ODD", "(ODD 0 <=> F) /\ (!n. ODD (SUC n) <=> ~ODD n)");
    // env.add_spec("-", "(!m. m - 0 = m) /\ (!m n. m - SUC n = PRE (m - n))");
    // env.parse_basic_def("TYPE_DEFINITION",
    //   "(\P rep. ONE_ONE rep /\ (!x. P x <=> (?y. x = rep y)))");
    // env.add_thm(Thm, "AND_DEF1", "(/\) = (\p q. !t. (p ==> q ==> t) ==> t)");
    // env.add_thm(Thm, "EXISTS_THM", "(?) = (\P. P ((@) P))");
    // env.add_thm(Thm, "EXISTS_UNIQUE_DEF1", "(?!) = (\P. ?t. P t /\ (!x. P x ==> x = t))");
    // env.add_thm(Thm, "IMP_ANTISYM_AX", "!t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 <=> t2)");
    // env.add_thm(Thm, "BOOL_CASES_AX", "!t. (t <=> T) \/ (t <=> F)");
    // env.add_thm(Thm, "TRUTH", "T");
    // env.add_thm(Thm, "NOT_TRUE", "~T <=> F");
    // env.add_thm(Thm, "EXCLUDED_MIDDLE", "!t. t \/ ~t");
    // env.add_thm(Thm, "PAIR_EQ", "!x y a b. x,y = a,b <=> x = a /\ y = b");
    // env.add_thm(Thm, "PAIR_SURJECTIVE", "!p. ?x y. p = x,y");
    // env.add_thm(Thm, "FST", "!x y. FST (x,y) = x");
    // env.add_thm(Thm, "SND", "!x y. SND (x,y) = y");
    // env.add_thm(Thm, "IND_SUC_0", "!x. ~(IND_SUC x = IND_0)");
    // env.add_thm(Thm, "IND_SUC_INJ", "!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2");
    // env.add_thm(Thm, "NOT_SUC", "!n. ~(SUC n = 0)");
    // env.add_thm(Thm, "SUC_INJ", "!m n. SUC m = SUC n <=> m = n");
    // env.add_thm(Thm, "num_CASES", "!m. m = 0 \/ (?n. m = SUC n)");
    // env.add_thm(Thm, "num_INDUCTION", "!P. P 0 /\ (!n. P n ==> P (SUC n)) ==> (!n. P n)");
    // env.add_thm(Thm, "num_RECURSION", "!e f. ?fn. fn 0 = e /\ (!n. fn (SUC n) = f (fn n) n)");
    // env.add_thm(Thm, "PRE", "PRE 0 = 0 /\ (!n. PRE (SUC n) = n)");
    // env.add_thm(Thm, "ADD", "(!n. 0 + n = n) /\ (!m n. SUC m + n = SUC (m + n))");
    // env.add_thm(Thm, "SUB", "(!m. m - 0 = m) /\ (!m n. m - SUC n = PRE (m - n))");
    // env.add_thm(Thm, "MULT1", "(!n. 0 * n = 0) /\ (!m n. SUC m * n = n + m * n)");
    // env.add_thm(Thm, "EXP", "(!m. m EXP 0 = 1) /\ (!m n. m EXP SUC n = m * m EXP n)");
    // env.add_thm(Thm, "LT", "(!m. m < 0 <=> F) /\ (!m n. m < SUC n <=> m = n \/ m < n)");
    // env.add_thm(Thm, "LE1", "!m n. m <= n <=> m < n \/ m = n");
    // env.add_thm(Thm, "GT1", "!m n. m > n <=> n < m");
    // env.add_thm(Thm, "GE1", "!m n. m >= n <=> n <= m");
    // env.add_thm(Thm, "EVEN", "(EVEN 0 <=> T) /\ (!n. EVEN (SUC n) <=> ~EVEN n)");
    // env.add_thm(Thm, "ODD1", "!n. ODD n <=> ~EVEN n");
    env
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