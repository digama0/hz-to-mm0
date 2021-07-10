use std::fmt::{self, Display, Formatter};

use crate::types::*;
use crate::kernel::*;

pub struct Print<'a, S: ?Sized, T> {
  pub env: Option<&'a Environment>,
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
  env: Option<&Environment>,
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
      if let Some(env) = env {
        write!(f, "{}", env[tyop].name)?;
      } else {
        write!(f, "_{}", tyop.0)?;
      }
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

const TYPES: bool = true;
const CONST_TYPES: bool = true;

fn print_binder<S: HasTermStore + ?Sized>(
  env: Option<&Environment>,
  arena: &S,
  s: &str,
  prec: u32,
  mut v: VarId,
  mut e: TermId,
  f: &mut Formatter<'_>,
  dest: impl Fn(&S, TermId) -> Option<(VarId, TermId)>,
) -> fmt::Result {
  if prec >= 10 { write!(f, "(")? }
  f.write_str(s)?;
  loop {
    let Var {ref name, ty} = *arena[v];
    if TYPES {
      write!(f, " ({}: ", name)?;
      print_type(env, arena, ty, 0, f)?;
      write!(f, ")")?;
    } else {
      write!(f, " {}", name)?;
    }
    if let Some((v2, e2)) = dest(arena, e) { v = v2; e = e2 } else { break }
  }
  write!(f, ". ")?;
  print_term(env, arena, e, 9, f)?;
  if prec >= 10 { write!(f, ")")? }
  Ok(())
}

fn print_term(
  env: Option<&Environment>,
  arena: &(impl HasTermStore + ?Sized),
  tm: TermId,
  prec: u32,
  f: &mut Formatter<'_>
) -> fmt::Result {
  match *arena[tm] {
    Term::Var(v) => write!(f, "{}", arena[v].name)?,
    Term::Const(ConstId::FORALL, _) => write!(f, "(!)")?,
    Term::Const(ConstId::EXISTS, _) => write!(f, "(?)")?,
    Term::Const(ConstId::EQ, _) => write!(f, "(=)")?,
    Term::Const(ConstId::ADD, _) => write!(f, "(+)")?,
    Term::Const(ConstId::SUB, _) => write!(f, "(-)")?,
    Term::Const(ConstId::MULT, _) => write!(f, "(*)")?,
    Term::Const(c, ref args) => {
      if let Some(env) = env { write!(f, "{}", env[c].name)? } else { write!(f, "C{}", c.0)? }
      if CONST_TYPES {
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
    Term::Lam(v, e) => print_binder(env, arena, "\\", prec, v, e, f, |a, e| a.try_dest_lam(e))?,
    Term::App(g, t) => {
      match *arena[g] {
        Term::Const(ConstId::FORALL, _) => if let Term::Lam(v, e) = *arena[t] {
          return print_binder(env, arena, "!", prec, v, e, f, |a, e| a.try_dest_forall(e))
        }
        Term::Const(ConstId::EXISTS, _) => if let Term::Lam(v, e) = *arena[t] {
          return print_binder(env, arena, "?", prec, v, e, f, |a, e| a.try_dest_exists(e))
        }
        Term::App(g, t1) => match *arena[g] {
          Term::Const(ConstId::EQ, ref ty) => if arena.is_bool(ty[0]) {
            if prec >= 2 { write!(f, "(")? }
            print_term(env, arena, t1, 2, f)?;
            write!(f, " <=> ")?;
            print_term(env, arena, t, 1, f)?;
            if prec >= 2 { write!(f, ")")? }
            return Ok(())
          } else {
            if prec >= 12 { write!(f, "(")? }
            print_term(env, arena, t1, 12, f)?;
            write!(f, " = ")?;
            print_term(env, arena, t, 11, f)?;
            if prec >= 12 { write!(f, ")")? }
            return Ok(())
          }
          Term::Const(ConstId::ADD, _) => {
            if prec >= 16 { write!(f, "(")? }
            print_term(env, arena, t1, 16, f)?;
            write!(f, " + ")?;
            print_term(env, arena, t, 15, f)?;
            if prec >= 16 { write!(f, ")")? }
            return Ok(())
          }
          Term::Const(ConstId::SUB, _) => {
            if prec >= 18 { write!(f, "(")? }
            print_term(env, arena, t1, 17, f)?;
            write!(f, " - ")?;
            print_term(env, arena, t, 18, f)?;
            if prec >= 18 { write!(f, ")")? }
            return Ok(())
          }
          Term::Const(ConstId::MULT, _) => {
            if prec >= 20 { write!(f, "(")? }
            print_term(env, arena, t1, 20, f)?;
            write!(f, " * ")?;
            print_term(env, arena, t, 19, f)?;
            if prec >= 20 { write!(f, ")")? }
            return Ok(())
          }
          _ => {}
        }
        _ => {}
      }
      if prec >= 50 { write!(f, "(")? }
      print_term(env, arena, g, 49, f)?;
      write!(f, " ")?;
      print_term(env, arena, t, 50, f)?;
      if prec >= 50 { write!(f, ")")? }
    }
  }
  Ok(())
}

