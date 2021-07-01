use crate::types::{ConstDef, Environment, FetchKind, ThmDef, TyopDef};

impl Environment {

  pub fn new() -> Self {
    use FetchKind::*;
    let mut env = Self {
      tyops: vec![],
      consts: vec![],
      thms: vec![],
      trans: Default::default()
    };
    env.add_tyop("bool", TyopDef {arity: 0});
    // env.add_tyop("fun", TyopDef {arity: 2});
    // env.add_tyop("ind", TyopDef {arity: 0});
    // env.add_basic_def("T");
    // env.add_basic_def("F");
    // env.add_basic_def("==>");
    // env.add_const("/\\", ConstDef);
    // env.add_basic_def("\\/");
    env.add_basic_def("~");
    env.add_basic_def("!");
    // env.add_const("?", ConstDef);
    // env.add_const("?!", ConstDef);
    // env.add_const("=", ConstDef);
    // env.add_const("@", ConstDef);
    // env.add_basic_def("TYPE_DEFINITION");
    env.add_basic_def("ONTO");
    env.add_basic_def("ONE_ONE");
    env.add_basic_def("COND");
    env.add_basic_def(",");
    env.add_basic_def("FST");
    env.add_basic_def("SND");
    // env.add_const("IND_0", ConstDef);
    // env.add_const("IND_SUC", ConstDef);
    env.add_basic_def("_0");
    env.add_basic_def("SUC");
    // env.add_const("PRE", ConstDef);
    // env.add_const("+", ConstDef);
    // env.add_const("-", ConstDef);
    // env.add_const("*", ConstDef);
    // env.add_const("EXP", ConstDef);
    // env.add_const("EVEN", ConstDef);
    // env.add_const("ODD", ConstDef);
    env.add_basic_def("NUMERAL");
    env.add_basic_def("BIT0");
    env.add_basic_def("BIT1");
    env.add_type_bijs("num", "mk_num", "dest_num");
    env.add_basic_def("NUM_REP");
    // env.add_tyop("prod", TyopDef {arity: 2});
    env.add_basic_def("mk_pair");
    env.add_type_bijs("prod", "ABS_prod", "REP_prod");
    // env.add_thm(Thm, "AND_DEF1", ThmDef);
    env.add_thm(Thm, "EXISTS_THM", ThmDef);
    env.add_thm(Thm, "EXISTS_UNIQUE_DEF1", ThmDef);
    env.add_thm(Axiom, "ETA_AX", ThmDef);
    // env.add_thm(Thm, "IMP_ANTISYM_AX", ThmDef);
    env.add_thm(Thm, "BOOL_CASES_AX", ThmDef);
    env.add_thm(Axiom, "SELECT_AX", ThmDef);
    env.add_thm(Thm, "TRUTH", ThmDef);
    env.add_thm(Thm, "NOT_TRUE", ThmDef);
    env.add_thm(Thm, "EXCLUDED_MIDDLE", ThmDef);
    env.add_thm(Thm, "PAIR_EQ", ThmDef);
    env.add_thm(Thm, "PAIR_SURJECTIVE", ThmDef);
    env.add_thm(Thm, "FST", ThmDef);
    env.add_thm(Thm, "SND", ThmDef);
    env.add_thm(Axiom, "INFINITY_AX", ThmDef);
    env.add_thm(Thm, "IND_SUC_0", ThmDef);
    env.add_thm(Thm, "IND_SUC_INJ", ThmDef);
    env.add_thm(Thm, "NOT_SUC", ThmDef);
    env.add_thm(Thm, "SUC_INJ", ThmDef);
    env.add_thm(Thm, "num_CASES", ThmDef);
    env.add_thm(Thm, "num_INDUCTION", ThmDef);
    env.add_thm(Thm, "num_RECURSION", ThmDef);
    env.add_thm(Thm, "PRE", ThmDef);
    env.add_thm(Thm, "ADD", ThmDef);
    env.add_thm(Thm, "SUB", ThmDef);
    env.add_thm(Thm, "MULT1", ThmDef);
    env.add_thm(Thm, "EXP", ThmDef);
    env.add_thm(Thm, "LT", ThmDef);
    env.add_thm(Thm, "LE1", ThmDef);
    env.add_thm(Thm, "GT1", ThmDef);
    env.add_thm(Thm, "GE1", ThmDef);
    env.add_thm(Thm, "EVEN", ThmDef);
    env.add_thm(Thm, "ODD1", ThmDef);
    env
  }
}
