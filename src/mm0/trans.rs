#![allow(unused)]

use crate::hol;
use super::{TermId, ThmId, TydefId, writer::Mm0Writer};

#[derive(Debug)]
pub struct Mm0Env {
  w: Mm0Writer,
}

impl Mm0Env {
  pub fn new(w: Mm0Writer) -> Self {
    Self { w }
  }

  pub fn add_tyop(&mut self,
    name: &str, n: hol::TyopId, ty: &hol::TyopDef,
    orig: Option<TermId>,
  ) -> (TermId, TydefId) {
    todo!()
  }

  pub fn add_const(&mut self,
    name: &str, n: hol::ConstId, ty: &hol::OwnedType,
    orig: Option<(TermId, ThmId)>,
    reason: hol::ConstReason<'_>,
  ) -> (TermId, ThmId) {
    todo!()
  }

  pub fn add_thm(&mut self,
    name: Option<&str>, n: hol::ThmId, d: &hol::ThmDef,
    orig: Option<ThmId>,
  ) -> ThmId {
    todo!()
  }
}