#![allow(unused)]

use std::{fs::File, io::{self, BufReader, BufWriter, Write}, path::PathBuf};
use mm0_util::{TermId, ThmId};
use mm0b_parser::{Arg, HasSymbolNames, MmbFile};

#[derive(Debug)]
struct Temp(PathBuf, BufWriter<File>);

impl io::Write for Temp {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> { self.1.write(buf) }
  fn write_all(&mut self, buf: &[u8]) -> io::Result<()> { self.1.write_all(buf) }
  fn flush(&mut self) -> io::Result<()> { self.1.flush() }
}

impl mm0b_parser::Reopen for Temp {
  type Reopened = BufReader<File>;
  fn reopen(mut self) -> io::Result<Self::Reopened> {
    self.1.flush()?;
    Ok(BufReader::new(File::open(self.0)?))
  }
}

#[derive(Debug)]
pub struct Mm0Writer {
  w: mm0b_parser::Mm0Writer<Temp>,
  out: PathBuf,
}

impl Mm0Writer {
  /// Initialize an MMB writer with the entire contents of another MMB file.
  /// Requires that the writer is newly initialized, i.e. has no sorts/terms/thms declared yet.
  pub fn new<'a, X: HasSymbolNames<'a>>(out: PathBuf, temp: PathBuf, mmb: &MmbFile<'a, X>) -> io::Result<Self> {
    let w = BufWriter::new(File::create(&temp)?);
    let mut w = mm0b_parser::Mm0Writer::new(Temp(temp, w));
    w.init(mmb)?;
    Ok(Self { w, out })
  }

  /// Add a new term with the given name and arguments. Returns the ID of the new term.
  pub fn add_term(&mut self, name: Option<&str>, args: &[Arg], ret: Arg) -> io::Result<TermId> {
    self.w.add_term(name, args, ret)
  }

  /// Begin construction of a new def with the given name and arguments.
  /// The returned `DefBuilder` contains references to the unify and proof streams, where the
  /// value of the definition should be inserted.
  pub fn add_def(
    &mut self, local: bool, name: Option<&str>, args: &[Arg], ret: Arg,
  ) -> DefBuilder<'_> {
    DefBuilder(self.w.add_def(local, name, args, ret))
  }

  /// Begin construction of a new axiom with the given name and arguments.
  /// The returned `ThmBuilder` contains references to the unify and proof streams, where the
  /// statement of the axiom should be inserted.
  pub fn add_axiom(&mut self, name: Option<&str>, args: &[Arg]) -> ThmBuilder<'_> {
    ThmBuilder(self.w.add_axiom(name, args))
  }

  /// Begin construction of a new theorem with the given name and arguments.
  /// The returned `ThmBuilder` contains references to the unify and proof streams, where the
  /// statement and proof of the theorem should be inserted.
  pub fn add_thm(&mut self, local: bool, name: Option<&str>, args: &[Arg]) -> ThmBuilder<'_> {
    ThmBuilder(self.w.add_thm(local, name, args))
  }

  /// This function consumes the `Mm0Writer` instance and actually writes the MMB data to the given
  /// writer, given a function `reopen` which reads the data just written to `proof`.
  pub fn finish(self) -> io::Result<()> {
    self.w.finish(&mut File::create(self.out)?)
  }
}

/// An unfinished definition. The `unify` and `proof` streams should be used to write unify and
/// proof commands, respectively, and when completed the `finish` function will finalize the
/// streams and return the `TermId` of the new definition.
#[derive(Debug)]
#[must_use = "discarding a DefBuilder will result in a corrupted file"]
pub struct DefBuilder<'a>(mm0b_parser::DefBuilder<'a, Temp>);

impl<'a> DefBuilder<'a> {
  pub fn finish(self) -> io::Result<TermId> { self.0.finish() }
}

/// An unfinished axiom or theorem. The `unify` and `proof` streams should be used to write unify
/// and proof commands, respectively, and when completed the `finish` function will finalize the
/// streams and return the `ThmId` of the new theorem.
#[derive(Debug)]
#[must_use = "discarding a ThmBuilder will result in a corrupted file"]
pub struct ThmBuilder<'a>(mm0b_parser::ThmBuilder<'a, Temp>);

impl<'a> ThmBuilder<'a> {
  pub fn finish(self) -> io::Result<ThmId> { self.0.finish() }
}