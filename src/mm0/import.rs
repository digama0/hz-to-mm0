use std::{io, path::PathBuf};
use std::collections::HashMap;
use crate::mm0::{SortId, TermId, ThmId};

#[cfg(debug_assertions)] use mm0b_parser::BasicMmbFile as MmbFile;
#[cfg(not(debug_assertions))] use mm0b_parser::BareMmbFile as MmbFile;

use super::Mm0Writer;

macro_rules! const_assert { ($cond:expr) => { let _ = [(); 0 - (!($cond) as usize)]; } }
macro_rules! build_consts {
  (@NIL $n:ident) => { () };
  (@CONST sort $name:ident $e:expr) => { pub const $name: SortId = SortId($e); };
  (@CONST term $name:ident $e:expr) => { pub const $name: TermId = TermId($e); };
  (@CONST thm $name:ident $e:expr) => { pub const $name: ThmId = ThmId($e); };
  (@CONST tydef $name:ident $e:expr) => { pub const $name: TydefId = TydefId($e); };
  (@INDEX $mmb:expr, sort $name:ident) => { $mmb.sort_index(mm0_const::$name) };
  (@INDEX $mmb:expr, term $name:ident) => { $mmb.term_index(mm0_const::$name) };
  (@INDEX $mmb:expr, thm $name:ident) => { $mmb.thm_index(mm0_const::$name) };
  (@CONJ $mmb:expr, tydef $name:ident: $s:tt) => {};
  (@CONJ $mmb:expr, $ty:ident $name:ident: $s:tt) => {
    if build_consts!(@INDEX $mmb, $ty $name)?.value()? != $s { return None }
  };
  (@GET $index:expr, sort $s:tt) => { $index.sorts.get($s).map(|n| n.0 as u32) };
  (@GET $index:expr, term $s:tt) => { $index.terms.get($s).map(|n| n.0) };
  (@GET $index:expr, thm $s:tt) => { $index.thms.get($s).map(|n| n.0) };
  (@PRINT $print1:ident, $out:expr, $index:expr, $name:expr, tydef $s:tt = $e:expr) => {
    write!($out, "  tydef {}: {:?} = {};", $name, stringify!($s), $e).unwrap()
  };
  (@PRINT $print1:ident, $out:expr, $index:expr, $name:expr, $ty:ident $s:tt = $e:expr) => {
    $print1(&mut $out, stringify!($ty), $name, $s, build_consts!(@GET $index, $ty $s), $e)
  };
  (@TYDEFS_CALLBACK $cb:ident $($t:tt)*) => {
    $cb! { $(build_consts!(@TYDEFS_FILTER $t))* }
  };
  (@TYDEFS ($($left:tt)*) (tydef $t:tt) $($right:tt)*) => {
    build_consts! { @TYDEFS ($($left)* $t) $($right)* }
  };
  (@TYDEFS ($($left:tt)*) $t:tt $($right:tt)*) => {
    build_consts! { @TYDEFS ($($left)*) $($right)* }
  };
  (@TYDEFS ($(($name:ident $s:expr, $e:expr))*)) => {
    pub const TYDEFS: [
      (ThmId, TermId, [(TermId, ThmId); 2], [ThmId; 2]);
      [$(build_consts!(@NIL $name)),*].len()
    ] = {
      const_assert!({
        let mut n = 0;
        ($($e == (n, n += 1).0 &&)* true, n).0
      });
      use mm0_const::*;
      [$($s),*]
    };
  };
  ($($ty:ident $name:ident: $s:tt = $e:expr;)*) => {
    pub mod mm0_const {
      use crate::mm0::{SortId, TermId, ThmId, TydefId};
      $(build_consts!(@CONST $ty $name $e);)*
    }

    build_consts! { @TYDEFS () $(($ty ($name $s, $e)))* }

    #[cfg(debug_assertions)]
    fn check_consts(mmb: &MmbFile<'_>) {
      #[derive(Default)]
      struct Index<'a> {
        sorts: HashMap<&'a str, SortId>,
        terms: HashMap<&'a str, TermId>,
        thms: HashMap<&'a str, ThmId>,
      }

      #[cold] fn rebuild_consts(mmb: &MmbFile<'_>) {
        use std::fmt::Write;
        let mut index = Index::default();
        for n in (0..mmb.header.num_sorts).map(SortId) {
          if let Some(s) = mmb.sort_index(n).and_then(|ix| ix.value()) {
            index.sorts.insert(s, n);
          }
        }
        for n in (0..mmb.header.num_terms.get()).map(TermId) {
          if let Some(s) = mmb.term_index(n).and_then(|ix| ix.value()) {
            index.terms.insert(s, n);
          }
        }
        for n in (0..mmb.header.num_thms.get()).map(ThmId) {
          if let Some(s) = mmb.thm_index(n).and_then(|ix| ix.value()) {
            index.thms.insert(s, n);
          }
        }
        let mut out = String::new();
        fn print1(out: &mut String, ty: &str, name: &str, s: &str, o: Option<u32>, e: u32) {
          if let Some(n) = o {
            write!(out, "  {} {}: {:?} = {};", ty, name, s, n).unwrap();
            if n == e { *out += "\n" } else { write!(out, " // not {}\n", e).unwrap() }
          } else {
            eprintln!("{} {:?} not found", ty, s);
            write!(out, "  {} {}: {:?} = ???;\n", ty, name, s).unwrap();
          }
        }
        $(build_consts!(@PRINT print1, out, index, stringify!($name), $ty $s = $e);)*
        eprintln!("build_consts! {{\n{}}}", out);
        panic!("Rebuild needed. Put this in 'mm0/import.rs'");
      }

      #[inline]
      fn check_consts(mmb: &MmbFile<'_>) -> Option<()> {
        $(build_consts!(@CONJ mmb, $ty $name: $s);)*
        Some(())
      }
      if check_consts(mmb).is_none() { rebuild_consts(mmb) }
    }
  }
}

// This is a list of indexes into the hol.mmb file; it is checked during startup,
// and if any of the indexes are wrong then it will print the appropriate replacement.
build_consts! {
  sort WFF: "wff" = 0;
  sort TYPE: "type" = 1;
  sort TERM: "term" = 2;
  term MM0_IM: "im" = 0;
  term MM0_AN: "an" = 1;
  term TY: "ty" = 4;
  term THM: "thm" = 9;
  term APP: "app" = 5;
  term LAM: "lam" = 6;

  term BOOL: "bool" = 2;
  term FUN: "fun" = 3;
  term EQ: "eq" = 7;  thm EQ_T: "eqT" = 20;
  term TRUE: "T" = 11;  thm TRUE_T: "TT" = 44;  thm TRUE_DEF: "T_DEF" = 43;
  term AND: "and" = 16;  thm AND_T: "andT" = 59;  thm AND_DEF: "AND_DEF" = 58;
  term IMP: "imp" = 18;  thm IMP_T: "impT" = 67;  thm IMP_DEF: "IMP_DEF" = 66;
  term ALL: "all" = 20;  thm ALL_T: "allT" = 80;  thm ALL_DEF: "FORALL_DEF" = 79;
  term EX: "ex" = 22;  thm EX_T: "exT" = 89;  thm EX_DEF: "EXISTS_DEF" = 88;
  term OR: "or" = 24;  thm OR_T: "orT" = 111;  thm OR_DEF: "OR_DEF" = 110;
  term FALSE: "F" = 26;  thm FALSE_T: "FT" = 119;  thm FALSE_DEF: "F_DEF" = 118;
  term NOT: "not" = 27;  thm NOT_T: "notT" = 122;  thm NOT_DEF: "NOT_DEF" = 121;
  term EU: "eu" = 29;  thm EU_T: "euT" = 132;  thm EU_DEF: "EU_DEF" = 131;
  thm ETA_AX: "ETA_AX" = 62;
  term SEL: "sel" = 30;  thm SEL_T: "selT" = 62;
  thm SELECT_AX: "SELECT_AX" = 134;
  term COND: "COND" = 30;  thm COND_T: "condT" = 137;  thm COND_DEF: "COND_DEF" = 138;

  thm CONJ: "CONJ" = 62;
  thm CONJ_PAIR: "CONJ_PAIR" = 63;
  thm CONJUNCT1: "CONJUNCT1" = 64;
  thm CONJUNCT2: "CONJUNCT2" = 65;
  thm REFL: "refl" = 26;
  thm AEQ: "aeq" = 27;
  thm AEQ1: "aeq1" = 28;
  thm AEQ2: "aeq2" = 29;
  thm MP: "MP" = 71;
  thm DISCH: "DISCH" = 72;
  thm UNDISCH: "UNDISCH" = 73;
  thm IMP_ANTISYM: "IMP_ANTISYM" = 74;
  thm EQ_IMP1: "EQ_IMP1" = 75;
  thm EQ_IMP2: "EQ_IMP2" = 76;
  thm IMP_ID: "IMP_ID" = 77;
  thm IMP_TRANS: "IMP_TRANS" = 78;
  thm SPEC: "SPEC" = 86;
  thm GEN: "GEN" = 87;
  thm CHOOSE: "CHOOSE" = 94;
  thm EXISTS: "EXISTS" = 96;
  thm DISJ1: "DISJ1" = 115;
  thm DISJ2: "DISJ2" = 116;
  thm DISJ_CASES: "DISJ_CASES" = 117;
  thm CONTR: "CONTR" = 120;
  thm NOT_ELIM: "NOT_ELIM" = 126;
  thm NOT_INTRO: "NOT_INTRO" = 127;
  thm EQF_INTRO: "EQF_INTRO" = 128;
  thm EQF_ELIM: "EQF_ELIM" = 129;
  thm NOT_FALSE: "NOT_FALSE" = 130;
  thm CCONTR: "CCONTR" = 136;
  thm PROD_TYBIJ1: "prod_tybij1" = 142;
  thm PROD_TYBIJ2: "prod_tybij2" = 143;
  thm ONE_ONE_THM: "ONE_ONE" = 145;
  thm ONTO_THM: "ONTO" = 147;
  thm INF: "inf" = 148;

  term MK_PAIR: "mk_pair" = 31;
    thm MK_PAIR_T: "mk_pairT" = 138;
    thm MK_PAIR_DEF: "mk_pair_DEF" = 138;

  term PROD: "prod" = 32;
    thm PROD_THM: "PROD_THM" = 142;
    term ABS_PROD: "ABS_prod" = 33;  thm ABS_PROD_T: "ABS_prodT" = 122;
    term REP_PROD: "REP_prod" = 34;  thm REP_PROD_T: "REP_prodT" = 122;
    thm PROD_BIJ1: "PROD_BIJ1" = 142;  thm PROD_BIJ2: "PROD_BIJ2" = 142;
  tydef PROD_TYDEF: (PROD_THM, PROD,
    [(ABS_PROD, ABS_PROD_T), (REP_PROD, REP_PROD_T)], [PROD_BIJ1, PROD_BIJ2]) = 0;

  term PAIR: "pr" = 31;  thm PAIR_T: "prT" = 138;  thm PAIR_DEF: "PAIR_DEF" = 138;
  term FST: "fst" = 31;  thm FST_T: "fstT" = 138;  thm FST_DEF: "FST_DEF" = 138;
  term SND: "snd" = 31;  thm SND_T: "sndT" = 138;  thm SND_DEF: "SND_DEF" = 138;

  term IND: "ind" = 37;
  term ONE_ONE: "one_one" = 35;
    thm ONE_ONE_T: "one_one_T" = 144;
    thm ONE_ONE_BD: "one_one_BD" = 144;
    thm ONE_ONE_DEF: "one_one_DEF" = 144;
  term ONTO: "onto" = 36;
    thm ONTO_T: "onto_T" = 144;
    thm ONTO_BD: "onto_BD" = 144;
    thm ONTO_DEF: "onto_DEF" = 144;

  thm INFINITY_AX: "inf" = 144;
  term IND_SUC: "IND_SUC" = 144;
    thm IND_SUC_T: "IND_SUC_T" = 144;
    thm IND_SUC_DEF: "IND_SUC_DEF" = 144;
  term IND_0: "IND_0" = 144;
    thm IND_0_T: "IND_0_T" = 144;
    thm IND_0_DEF: "IND_0_DEF" = 144;
  term NUM_REP: "NUM_REP" = 144;
    thm NUM_REP_T: "NUM_REP_T" = 144;
    thm NUM_REP_DEF: "NUM_REP_DEF" = 144;

  term NUM: "num" = 32;
    thm NUM_THM: "NUM_THM" = 142;
    term MK_NUM: "mk_num" = 33;  thm MK_NUM_T: "mk_numT" = 122;
    term DEST_NUM: "dest_num" = 34;  thm DEST_NUM_T: "dest_numT" = 122;
    thm NUM_BIJ1: "NUM_BIJ1" = 142;  thm NUM_BIJ2: "NUM_BIJ2" = 142;
  tydef NUM_TYDEF: (NUM_THM, NUM,
    [(MK_NUM, MK_NUM_T), (DEST_NUM, DEST_NUM_T)], [NUM_BIJ1, NUM_BIJ2]) = 1;

  term ZERO: "_0" = 32; thm ZERO_T: "_0T" = 144; thm ZERO_DEF: "_0_DEF" = 144;

  term SUC: "SUC" = 32;
    thm SUC_T: "SUC_T" = 144;
    thm SUC_BD: "SUC_BD" = 144;
    thm SUC_DEF: "SUC_DEF" = 144;

  term NUMERAL: "NUMERAL" = 32;
    thm NUMERAL_T: "NUMERAL_T" = 144;
    thm NUMERAL_BD: "NUMERAL_BD" = 144;
    thm NUMERAL_DEF: "NUMERAL_DEF" = 144;

  term BIT0: "BIT0" = 32;
    thm BIT0_T: "BIT0T" = 144;
    thm BIT0_DEF: "BIT0_DEF" = 144;

  term BIT1: "BIT1" = 32;
    thm BIT1_T: "BIT1T" = 144;
    thm BIT1_BD: "BIT1_BD" = 144;
    thm BIT1_DEF: "BIT1_DEF" = 144;

  term PRE: "pre" = 32;
    thm PRE_T: "preT" = 144;
    thm PRE_DEF: "PRE_DEF" = 144;
    thm PRE_SPEC: "PRE" = 144;

  term ADD: "add" = 32;
    thm ADD_T: "addT" = 144;
    thm ADD_DEF: "ADD_DEF" = 144;
    thm ADD_SPEC: "ADD" = 144;

  term MUL: "mul" = 32;
    thm MUL_T: "mulT" = 144;
    thm MUL_DEF: "MUL_DEF" = 144;
    thm MUL_SPEC: "MUL" = 144;

  term EXP: "exp" = 32;
    thm EXP_T: "expT" = 144;
    thm EXP_DEF: "EXP_DEF" = 144;
    thm EXP_SPEC: "EXP" = 144;

  term LE: "le" = 32;
    thm LE_T: "leT" = 144;
    thm LE_DEF: "LE_DEF" = 144;
    thm LE_SPEC: "LE" = 144;

  term LT: "lt" = 32;
    thm LT_T: "ltT" = 144;
    thm LT_DEF: "LT_DEF" = 144;
    thm LT_SPEC: "LT" = 144;

  term GE: "ge" = 32;
    thm GE_T: "geT" = 144;
    thm GE_BD: "GE_BD" = 144;
    thm GE_DEF: "GE_DEF" = 144;

  term GT: "gt" = 32;
    thm GT_T: "gtT" = 144;
    thm GT_BD: "GT_BD" = 144;
    thm GT_DEF: "GT_DEF" = 144;

  term EVEN: "even" = 32;
    thm EVEN_T: "evenT" = 144;
    thm EVEN_DEF: "EVEN_DEF" = 144;
    thm EVEN_SPEC: "EVEN" = 144;

  term ODD: "odd" = 32;
    thm ODD_T: "oddT" = 144;
    thm ODD_DEF: "ODD_DEF" = 144;
    thm ODD_SPEC: "ODD" = 144;

  term SUB: "sub" = 32;
    thm SUB_T: "subT" = 144;
    thm SUB_DEF: "SUB_DEF" = 144;
    thm SUB_SPEC: "SUB" = 144;

  term TYPEDEF: "typedef" = 32;
    thm TYPEDEF_T: "typedefT" = 144;
    thm TYPEDEF_DEF: "TYPEDEF_DEF" = 144;

  thm AND_DEF1: "AND_DEF1" = 62;
  thm EXISTS_THM: "EXISTS_THM" = 64;
  thm EU_DEF1: "EU_DEF1" = 65;
  thm IMP_ANTISYM_AX: "IMP_ANTISYM_AX" = 65;
  thm BOOL_CASES_AX: "BOOL_CASES_AX" = 65;
  thm TRUTH: "TRUTH" = 65;
  thm NOT_TRUE: "NOT_TRUE" = 65;
  thm EM: "em" = 135;
  thm PAIR_EQ: "PAIR_EQ" = 65;
  thm PAIR_SURJ: "PAIR_SURJ" = 65;
  thm FST_THM: "FST" = 65;
  thm SND_THM: "SND" = 65;
  thm IND_SUC_0: "IND_SUC_0" = 65;
  thm IND_SUC_INJ: "IND_SUC_INJ" = 65;
  thm NOT_SUC: "NOT_SUC" = 65;
  thm SUC_INJ: "SUC_INJ" = 65;
  thm NUM_CASES: "num_CASES" = 65;
  thm NUM_IND: "num_INDUCTION" = 65;
  thm NUM_REC: "num_RECURSION" = 65;
  thm MUL1: "MUL1" = 65;
  thm LE1: "LE1" = 65;
  thm GT1: "GT1" = 65;
  thm GE1: "GE1" = 65;
  thm ODD1: "ODD1" = 65;
}

pub fn hol_writer(out: PathBuf, temp: PathBuf) -> io::Result<Mm0Writer> {
  let mmb = MmbFile::parse(include_bytes!("../../hol.mmb")).unwrap();
  #[cfg(debug_assertions)] check_consts(&mmb);
  Mm0Writer::new(out, temp, &mmb)
}
