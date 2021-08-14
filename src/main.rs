mod lexer;
mod parser;
pub mod kernel;
mod corethy;
mod types;
mod print;

use std::collections::VecDeque;
use std::fs::File;
use std::path::PathBuf;
use std::io::Read;
use parser::Summary;
use types::{ObjectData, ObjectSpec};
use kernel::Environment;

struct Importer {
  env: Environment,
  deferred: VecDeque<(ObjectSpec, ObjectData)>,
}

fn main() {
  let rpath = PathBuf::from("../flyspeck");
  let modules = [
    "BaseSystem",
    "Multivariate",
    "Start",
    "TrigNonlinear",
    "Volume",
    "Hypermap",
    "Fan",
    "Packing",
    "Local1",
    "Tame1",
    "Local2",
    "Local3",
    "Local4",
    "Local5",
    "Tame2",
    "Tame3",
    "End"
  ];
  let mut importer = Importer {
    env: Environment::new(),
    deferred: Default::default(),
  };
  for module in modules {
    println!("importing {}", module);
    let mpath = rpath.join(module);
    let summary = mpath.join("SUMMARY");
    let summary = Summary::from(File::open(summary).unwrap().bytes().map(Result::unwrap));
    assert_eq!(summary.hol_system, "HOL Light");
    for (kind, data) in summary {
      importer.import(&mpath, kind, data, true);
    }
    let mut failures = 0;
    let mut defer = true;
    while let Some((kind, data)) = importer.deferred.pop_front() {
      if importer.import(&mpath, kind, data, defer) {
        failures = 0;
      } else {
        failures += 1;
        if failures >= importer.deferred.len() {
          defer = false;
        }
      }
    }
    println!("finished {}", module);
  }
  let mut types: Vec<_> = importer.env.counts.into_iter().collect();
  types.sort_by(|a, b| a.1.cmp(&b.1));
  println!("{:?}", types)
}
