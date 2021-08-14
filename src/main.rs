mod lexer;
mod parser;
pub mod kernel;
mod corethy;
mod types;
mod print;

use std::{collections::VecDeque, time::Instant};
use std::fs::File;
use std::path::PathBuf;
use std::io::Read;
use parser::Summary;
use types::{ObjectData, ObjectSpec, FetchKind};
use kernel::{Environment, set_print};

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
  let boot = Instant::now();
  for module in modules {
    println!("importing {}", module);
    let start = Instant::now();
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
    println!("finished {} in {:.2}s, total {:.2}s", module,
      start.elapsed().as_secs_f32(), boot.elapsed().as_secs_f32());
  }
  let env = importer.env;
  println!("success");
  let thm = "kepler_conjecture_with_assumptions";
  let td = &env[*env.trans.fetches[FetchKind::Thm].get(thm).expect("theorem not found")];
  set_print(true);
  env.print(&td.arena, |p| println!("{}:\n{}", thm, p.pp(td.concl)));
}
