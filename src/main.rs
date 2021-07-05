#![allow(unused)]
mod lexer;
mod parser;
mod kernel;
mod corethy;
mod types;

use std::collections::VecDeque;
use std::fs::File;
use std::path::PathBuf;
use std::io::Read;
use parser::Summary;
use types::{ObjectData, ObjectSpec};
use kernel::Environment;

struct Importer {
  env: Environment,
  mpath: PathBuf,
  deferred: VecDeque<(ObjectSpec, ObjectData)>,
}

fn main() {
  let rpath = PathBuf::from("../flyspeck");
  let mdl = "BaseSystem";
  let mpath = rpath.join(mdl);
  let summary = mpath.join("SUMMARY");
  let summary = Summary::from(File::open(summary).unwrap().bytes().map(Result::unwrap));
  assert_eq!(summary.hol_system, "HOL Light");
  let env = Environment::new();
  let mut importer = Importer {
    env,
    mpath,
    deferred: Default::default(),
  };
  for (kind, data) in summary {
    importer.import(kind, data, true);
  }
  let mut failures = 0;
  let mut defer = true;
  while let Some((kind, data)) = importer.deferred.pop_front() {
    if importer.import(kind, data, defer) {
      failures = 0;
    } else {
      failures += 1;
      if failures >= importer.deferred.len() {
        defer = false;
      }
    }
  }
  let mut types: Vec<_> = importer.env.counts.into_iter().collect();
  types.sort_by(|a, b| a.1.cmp(&b.1));
  println!("{:?}", types)
}
