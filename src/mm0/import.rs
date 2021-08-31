use std::{io, path::PathBuf};
use std::collections::HashMap;
use crate::mm0::{SortId, TermId, ThmId};

#[cfg(debug_assertions)] use mm0b_parser::BasicMmbFile as MmbFile;
#[cfg(not(debug_assertions))] use mm0b_parser::BareMmbFile as MmbFile;

use super::Mm0Writer;

macro_rules! const_assert { ($cond:expr) => { let _ = [(); 0 - (!($cond) as usize)]; } }
macro_rules! build_consts {
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
    writeln!($out, "  tydef {}: {} = {};", $name, stringify!($s), $e).unwrap()
  };
  (@PRINT $print1:ident, $out:expr, $index:expr, $name:expr, $ty:ident $s:tt = $e:expr) => {
    $print1(&mut $out, stringify!($ty), $name, $s, build_consts!(@GET $index, $ty $s), $e)
  };
  (@TYDEFS $(($nil:tt ($name:ident $s:expr, $e:expr)))*) => {
    pub const TYDEFS: [
      (ThmId, TermId, [(TermId, ThmId); 2], [ThmId; 2]);
      [$($nil),*].len()
    ] = {
      const_assert!({
        let mut n = 0;
        ($($e == (n, n += 1).0 &&)* true, n).0
      });
      use mm0_const::*;
      [$($s),*]
    };
  };
  (@FILTER_TYDEFS $(($(tydef $($tydef:literal)?)? $(sort)? $(term)? $(thm)?: $t:tt))*) => {
    build_consts! { @TYDEFS $($($($tydef)? (() $t))?)* }
  };
  ($($ty:ident $name:ident: $s:tt = $e:expr;)*) => {
    pub mod mm0_const {
      use crate::mm0::{SortId, TermId, ThmId, TydefId};
      $(build_consts!(@CONST $ty $name $e);)*
    }

    build_consts! { @FILTER_TYDEFS $(($ty: ($name $s, $e)))* }

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
// (TODO: use code generation)
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

  term EQ: "eq" = 7;
  thm EQ_T: "eqT" = 27;

  term TRUE: "T" = 11;
  thm TRUE_T: "TT" = 51;
  thm TRUE_DEF: "T_DEF" = 52;

  term AND: "and" = 16;
  thm AND_T: "andT" = 68;
  thm AND_DEF: "AND_DEF" = 69;

  term IMP: "imp" = 18;
  thm IMP_T: "impT" = 76;
  thm IMP_DEF: "IMP_DEF" = 77;

  term ALL: "all" = 20;
  thm ALL_T: "allT" = 90;
  thm ALL_DEF: "FORALL_DEF" = 91;

  term EX: "ex" = 22;
  thm EX_T: "exT" = 105;
  thm EX_DEF: "EXISTS_DEF" = 106;

  term OR: "or" = 24;
  thm OR_T: "orT" = 127;
  thm OR_DEF: "OR_DEF" = 128;

  term FALSE: "F" = 26;
  thm FALSE_T: "FT" = 138;
  thm FALSE_DEF: "F_DEF" = 139;

  term NOT: "not" = 27;
  thm NOT_T: "notT" = 142;
  thm NOT_DEF: "NOT_DEF" = 143;

  term EU: "eu" = 29;
  thm EU_T: "euT" = 153;
  thm EU_DEF: "EU_DEF" = 154;
  thm ETA_AX: "ETA_AX" = 104;

  term SEL: "sel" = 15;
  thm SEL_T: "selT" = 63;
  thm SELECT_AX: "SELECT_AX" = 157;

  term COND: "COND" = 30;
  thm COND_T: "condT" = 163;
  thm COND_DEF: "COND_DEF" = 164;

  thm CONJ: "CONJ" = 72;
  thm CONJ_PAIR: "CONJ_PAIR" = 73;
  thm CONJUNCT1: "CONJUNCT1" = 74;
  thm CONJUNCT2: "CONJUNCT2" = 75;
  thm REFL: "refl" = 33;
  thm AEQ: "aeq" = 34;
  thm AEQ1: "aeq1" = 35;
  thm AEQ2: "aeq2" = 36;
  thm MP: "MP" = 81;
  thm DISCH: "DISCH" = 82;
  thm UNDISCH: "UNDISCH" = 84;
  thm IMP_ANTISYM: "IMP_ANTISYM" = 85;
  thm EQ_IMP1: "EQ_IMP1" = 86;
  thm EQ_IMP2: "EQ_IMP2" = 87;
  thm IMP_ID: "IMP_ID" = 88;
  thm IMP_TRANS: "IMP_TRANS" = 89;
  thm SPEC: "SPEC" = 97;
  thm GEN: "GEN" = 98;
  thm CHOOSE: "CHOOSE" = 111;
  thm EXISTS: "EXISTS" = 113;
  thm DISJ1: "DISJ1" = 132;
  thm DISJ2: "DISJ2" = 134;
  thm DISJ_CASES: "DISJ_CASES" = 136;
  thm CONTR: "CONTR" = 140;
  thm NOT_ELIM: "NOT_ELIM" = 147;
  thm NOT_INTRO: "NOT_INTRO" = 148;
  thm EQF_INTRO: "EQF_INTRO" = 149;
  thm EQF_ELIM: "EQF_ELIM" = 150;
  thm NOT_FALSE: "NOT_FALSE" = 151;
  thm CCONTR: "CCONTR" = 162;
  thm PROD_TYBIJ1: "prod_tybij1" = 172;
  thm PROD_TYBIJ2: "prod_tybij2" = 173;
  thm ONE_ONE_THM: "ONE_ONE" = 192;
  thm ONTO_THM: "ONTO" = 197;
  thm INF: "inf" = 198;

  term MK_PAIR: "mk_pair" = 31;
  thm MK_PAIR_T: "mk_pairT" = 165;
  thm MK_PAIR_DEF: "mk_pair_DEF" = 166;

  term PROD: "prod" = 32;
  thm PROD_THM: "PROD_THM" = 168;
  term ABS_PROD: "ABS_prod" = 33;
  thm ABS_PROD_T: "ABS_prodT" = 170;
  term REP_PROD: "REP_prod" = 34;
  thm REP_PROD_T: "REP_prodT" = 171;
  thm PROD_BIJ1: "PROD_BIJ1" = 174;
  thm PROD_BIJ2: "PROD_BIJ2" = 175;
  tydef PROD_TYDEF: (PROD_THM, PROD,
    [(ABS_PROD, ABS_PROD_T), (REP_PROD, REP_PROD_T)], [PROD_BIJ1, PROD_BIJ2]) = 0;

  term PAIR: "pr" = 35;
  thm PAIR_T: "prT" = 176;
  thm PAIR_DEF: "PAIR_DEF" = 177;

  term FST: "fst" = 36;
  thm FST_T: "fstT" = 180;
  thm FST_DEF: "FST_DEF" = 181;

  term SND: "snd" = 37;
  thm SND_T: "sndT" = 184;
  thm SND_DEF: "SND_DEF" = 185;

  term IND: "ind" = 40;

  term ONE_ONE: "one_one" = 38;
  thm ONE_ONE_T: "one_one_T" = 188;
  thm ONE_ONE_BD: "one_one_BD" = 189;
  thm ONE_ONE_DEF: "one_one_DEF" = 191;

  term ONTO: "onto" = 39;
  thm ONTO_T: "onto_T" = 193;
  thm ONTO_BD: "onto_BD" = 194;
  thm ONTO_DEF: "onto_DEF" = 196;

  thm INFINITY_AX: "inf" = 198;

  term IND_SUC: "IND_SUC" = 41;
  thm IND_SUC_T: "IND_SUC_T" = 199;
  thm IND_SUC_DEF: "IND_SUC_DEF" = 200;

  term IND_0: "IND_0" = 42;
  thm IND_0_T: "IND_0_T" = 203;
  thm IND_0_DEF: "IND_0_DEF" = 204;

  term NUM_REP: "NUM_REP" = 43;
  thm NUM_REP_T: "NUM_REP_T" = 205;
  thm NUM_REP_DEF: "NUM_REP_DEF" = 206;

  term NUM: "num" = 44;
  thm NUM_THM: "NUM_THM" = 207;
  term MK_NUM: "mk_num" = 45;
  thm MK_NUM_T: "mk_numT" = 208;
  term DEST_NUM: "dest_num" = 46;
  thm DEST_NUM_T: "dest_numT" = 209;
  thm NUM_BIJ1: "NUM_BIJ1" = 212;
  thm NUM_BIJ2: "NUM_BIJ2" = 213;
  tydef NUM_TYDEF: (NUM_THM, NUM,
    [(MK_NUM, MK_NUM_T), (DEST_NUM, DEST_NUM_T)], [NUM_BIJ1, NUM_BIJ2]) = 1;

  term ZERO: "_0" = 47;
  thm ZERO_T: "_0T" = 214;
  thm ZERO_DEF: "_0_DEF" = 215;

  term SUC: "suc" = 48;
  thm SUC_T: "sucT" = 216;
  thm SUC_BD: "suc_BD" = 218;
  thm SUC_DEF: "suc_DEF" = 219;

  term NUMERAL: "NUMERAL" = 49;
  thm NUMERAL_T: "NUMERAL_T" = 220;
  thm NUMERAL_BD: "NUMERAL_BD" = 222;
  thm NUMERAL_DEF: "NUMERAL_DEF" = 223;

  term BIT0: "bit0" = 51;
  thm BIT0_T: "bit0T" = 230;
  thm BIT0_DEF: "bit0_DEF" = 232;

  term BIT1: "bit1" = 52;
  thm BIT1_T: "bit1T" = 233;
  thm BIT1_BD: "bit1_BD" = 235;
  thm BIT1_DEF: "bit1_DEF" = 236;

  term PRE: "pre" = 54;
  thm PRE_T: "preT" = 238;
  thm PRE_DEF: "pre_DEF" = 239;
  thm PRE_SPEC: "PRE" = 240;

  term ADD: "add" = 55;
  thm ADD_T: "addT" = 241;
  thm ADD_DEF: "add_DEF" = 243;
  thm ADD_SPEC: "ADD" = 244;

  term MUL: "mul" = 57;
  thm MUL_T: "mulT" = 245;
  thm MUL_DEF: "mul_DEF" = 247;
  thm MUL_SPEC: "MUL" = 248;

  term EXP: "exp" = 59;
  thm EXP_T: "expT" = 250;
  thm EXP_DEF: "exp_DEF" = 252;
  thm EXP_SPEC: "EXP" = 253;

  term LE: "le" = 60;
  thm LE_T: "leT" = 254;
  thm LE_DEF: "le_DEF" = 256;
  thm LE_SPEC: "LE" = 257;

  term LT: "lt" = 62;
  thm LT_T: "ltT" = 258;
  thm LT_DEF: "lt_DEF" = 260;
  thm LT_SPEC: "LT" = 261;

  term GE: "ge" = 64;
  thm GE_T: "geT" = 263;
  thm GE_BD: "ge_BD" = 264;
  thm GE_DEF: "ge_DEF" = 265;

  term GT: "gt" = 65;
  thm GT_T: "gtT" = 266;
  thm GT_BD: "gt_BD" = 267;
  thm GT_DEF: "gt_DEF" = 268;

  term EVEN: "even" = 66;
  thm EVEN_T: "evenT" = 269;
  thm EVEN_DEF: "even_DEF" = 270;
  thm EVEN_SPEC: "EVEN" = 271;

  term ODD: "odd" = 67;
  thm ODD_T: "oddT" = 272;
  thm ODD_DEF: "odd_DEF" = 273;
  thm ODD_SPEC: "ODD" = 274;

  term SUB: "sub" = 68;
  thm SUB_T: "subT" = 276;
  thm SUB_DEF: "sub_DEF" = 278;
  thm SUB_SPEC: "SUB" = 279;

  term TYPEDEF: "TYPEDEF" = 70;
  thm TYPEDEF_T: "TYPEDEF_T" = 280;
  thm TYPEDEF_DEF: "TYPEDEF_DEF" = 281;

  thm AND_DEF1: "AND_DEF1" = 102;
  thm EXISTS_THM: "EXISTS_THM" = 158;
  thm EU_DEF1: "EU_DEF1" = 156;
  thm IMP_ANTISYM_AX: "IMP_ANTISYM_AX" = 103;
  thm BOOL_CASES_AX: "BOOL_CASES_AX" = 161;
  thm TRUTH: "TRUTH" = 53;
  thm NOT_TRUE: "NOT_TRUE" = 152;
  thm EM: "em" = 159;
  thm PAIR_EQ: "PAIR_EQ" = 178;
  thm PAIR_SURJ: "PAIR_SURJ" = 179;
  thm FST_THM: "FST" = 183;
  thm SND_THM: "SND" = 187;
  thm IND_SUC_0: "IND_SUC_0" = 201;
  thm IND_SUC_INJ: "IND_SUC_INJ" = 202;
  thm NOT_SUC: "NOT_SUC" = 225;
  thm SUC_INJ: "SUC_INJ" = 226;
  thm NUM_CASES: "num_CASES" = 227;
  thm NUM_IND: "num_INDUCTION" = 228;
  thm NUM_REC: "num_RECURSION" = 229;
  thm MUL1: "MUL1" = 249;
  thm LE1: "LE1" = 262;
  thm ODD1: "ODD1" = 275;
}

pub fn hol_writer(out: PathBuf, temp: PathBuf) -> io::Result<Mm0Writer> {
  #[repr(C, align(8))]
  pub struct Aligned<T: ?Sized>(T);
  static HOL_MMB: &Aligned<[u8]> = &Aligned(*include_bytes!("../../hol.mmb"));
  let mmb = MmbFile::parse(&HOL_MMB.0).unwrap();
  #[cfg(debug_assertions)] check_consts(&mmb);
  Mm0Writer::new(out, temp, &mmb)
}
