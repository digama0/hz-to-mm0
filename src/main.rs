mod lexer;
mod parser;
mod corethy;
mod types;

use std::collections::VecDeque;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fs::File;
use std::path::PathBuf;
use std::io::Read;
use std::rc::Rc;
use parser::Summary;
use types::{Environment, Idx, Node, UnparsedObjectData, ObjectSpec};

struct Importer {
  env: Environment,
  mpath: PathBuf,
  deferred: VecDeque<(ObjectSpec, UnparsedObjectData)>,
}

#[derive(Debug)]
pub struct Dedup<H> {
  map: HashMap<Rc<H>, u32>,
  named: Vec<u32>,
  objects: Vec<(Rc<H>, bool)>,
}

impl<H: Node> Dedup<H> {
  fn new() -> Self {
    Self { map: Default::default(), named: vec![u32::MAX], objects: vec![] }
  }

  fn reuse(&mut self, n: H::Idx) -> H::Idx {
    self.objects[n.into_u32() as usize].1 = true;
    n
  }

  fn named(&self, n: u32) -> H::Idx { Idx::from(self.named[n as usize]) }
}

impl<H: Node> Dedup<H> {
  fn add(&mut self, v: H) -> H::Idx {
    match self.map.entry(Rc::new(v)) {
      Entry::Vacant(e) => {
        let vec = &mut self.objects;
        let n = vec.len() as u32;
        vec.push((e.key().clone(), false));
        e.insert(n);
        Idx::from(n)
      }
      Entry::Occupied(e) => {
        let &n = e.get();
        self.reuse(Idx::from(n))
      }
    }
  }
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
    importer.import_target_object(kind, data, true);
  }
  let mut failures = 0;
  let mut defer = true;
  while let Some((kind, data)) = importer.deferred.pop_front() {
    if importer.import_target_object(kind, data, defer) {
      failures = 0;
    } else {
      failures += 1;
      if failures >= importer.deferred.len() {
        defer = false;
      }
    }
  }
}
