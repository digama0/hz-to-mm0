use std::fmt::{self, Display, Formatter};

use crate::types::*;
use crate::kernel::*;

pub struct Print<'a, S: ?Sized, T> {
  pub env: &'a Environment,
  pub arena: &'a S,
  pub t: T,
}

impl Display for TyVarId {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result { write!(f, "T{}", self.0) }
}

impl<'a, S: HasTypeStore + ?Sized> Display for Print<'a, S, TypeId> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    print_type(self.env, self.arena, self.t, 0, f)
  }
}

fn print_type(
  env: &Environment,
  arena: &(impl HasTypeStore + ?Sized),
  ty: TypeId,
  prec: u32,
  f: &mut Formatter<'_>
) -> fmt::Result {
  match *arena[ty] {
    Type::Var(v) => write!(f, "{}", v)?,
    Type::Const(TyopId::FUN, ref args) => {
      if prec >= 5 { write!(f, "(")? }
      print_type(env, arena, args[0], 5, f)?;
      write!(f, "->")?;
      print_type(env, arena, args[1], 4, f)?;
      if prec >= 5 { write!(f, ")")? }
    }
    Type::Const(TyopId::PROD, ref args) => {
      if prec >= 10 { write!(f, "(")? }
      print_type(env, arena, args[0], 10, f)?;
      write!(f, "#")?;
      print_type(env, arena, args[1], 9, f)?;
      if prec >= 10 { write!(f, ")")? }
    }
    Type::Const(tyop, ref args) => {
      write!(f, "{}", env[tyop].name)?;
      if let Some((&first, rest)) = args.split_first() {
        write!(f, "[")?;
        print_type(env, arena, first, 0, f)?;
        for &ty in rest {
          write!(f, ",")?;
          print_type(env, arena, ty, 0, f)?;
        }
        write!(f, "]")?;
      }
    }
  }
  Ok(())
}

impl Display for VarName {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match *self {
      VarName::Str(ref s) => write!(f, "{}", s),
      VarName::Genvar(n) => write!(f, "_{}", n),
    }
  }
}

impl<'a, S: HasTermStore + ?Sized> Display for Print<'a, S, VarId> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.arena[self.t].name)
  }
}

impl<'a, S: HasTermStore + ?Sized> Display for Print<'a, S, TermId> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    print_term(self.env, self.arena, self.t, 0, f)
  }
}

fn print_term(
  env: &Environment,
  arena: &(impl HasTermStore + ?Sized),
  tm: TermId,
  prec: u32,
  f: &mut Formatter<'_>
) -> fmt::Result {
  match *arena[tm] {
    Term::Var(v) => write!(f, "{}", arena[v].name)?,
    Term::Const(c, _) => write!(f, "{}", env[c].name)?,
    Term::Lam(mut v, mut e) => {
      if prec >= 10 { write!(f, "(")? }
      write!(f, "\\")?;
      loop {
        let Var{ref name, ty} = *arena[v];
        write!(f, " ({}: ", name)?;
        print_type(env, arena, ty, 0, f)?;
        write!(f, ")")?;
        if let Some((v2, e2)) = arena.try_dest_lam(e) { v = v2; e = e2 } else { break }
      }
      write!(f, ". ")?;
      print_term(env, arena, e, 9, f)?;
      if prec >= 10 { write!(f, ")")? }
    }
    Term::App(g, t) => {
      if prec >= 50 { write!(f, "(")? }
      print_term(env, arena, g, 49, f)?;
      write!(f, " ")?;
      print_term(env, arena, t, 50, f)?;
      if prec >= 50 { write!(f, ")")? }
    }
  }
  Ok(())
}

