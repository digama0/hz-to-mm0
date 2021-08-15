mod lexer;
mod parser;
pub mod kernel;
mod corethy;
mod types;
mod print;

use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use tokio::sync::Notify;
use tokio::sync::watch::{self, Receiver, Sender};
use std::time::Instant;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::io::Read;
use parser::Summary;
use types::{FetchKind, ObjectSpec};
use kernel::Environment;

struct Importer {
  env: Environment,
  jobs: RwLock<HashMap<ObjectSpec, Receiver<()>>>,
  flush: Notify,
}

pub struct DepIterator<'a> {
  env: &'a Environment,
  mpath: &'a Path,
  filemap: HashMap<ObjectSpec, String>,
  top: std::vec::IntoIter<ObjectSpec>,
  stack: Vec<(std::vec::IntoIter<ObjectSpec>, (ObjectSpec, PathBuf))>,
}

impl Iterator for DepIterator<'_> {
  type Item = (ObjectSpec, PathBuf);
  fn next(&mut self) -> Option<Self::Item> {
    loop {
      if let Some(o) = self.top.next() {
        if let Some(file) = self.filemap.remove(&o) {
          let path = self.mpath.join(&file);
          let deps = self.env.parse_header(&o,
            File::open(&path).unwrap().bytes().map(Result::unwrap)).2;
          self.stack.push((std::mem::replace(&mut self.top, deps.into_iter()), (o, path)));
        }
      } else if let Some((it, k)) = self.stack.pop() {
        self.top = it;
        return Some(k)
      } else {
        return None
      }
    }
  }
}

impl<I: Iterator<Item=u8>> Summary<I> {
  pub fn dep_iterator<'a>(self, env: &'a Environment, mpath: &'a Path) -> DepIterator<'a> {
    let mut objs = vec![];
    let filemap = self.map(|(k, d)| { objs.push(k.clone()); (k, d.file) }).collect();
    DepIterator { env, mpath, filemap, top: objs.into_iter(), stack: vec![] }
  }
}

impl Importer {
  pub async fn depend(&self, k: &ObjectSpec) {
    let mut rx = if let Some(rx) = self.jobs.read().unwrap().get(&k) {
      rx.clone()
    } else {
      return
    };
    rx.changed().await.unwrap();
  }

  pub async fn import(self: Arc<Self>, k: ObjectSpec, file: PathBuf, tx: Sender<()>) {
    self.import_core(k.clone(), file).await;
    self.jobs.write().unwrap().remove(&k);
    let _ = tx.send(());
    self.flush.notify_one();
  }

  pub async fn flush(&self) {
    while !self.jobs.read().unwrap().is_empty() {
      self.flush.notified().await;
    }
  }
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

  let rt = &tokio::runtime::Runtime::new().unwrap();
  let boot = Instant::now();
  let importer = Arc::new(Importer {
    env: Environment::new(),
    jobs: Default::default(),
    flush: Default::default(),
  });
  for module in modules {
    println!("importing {}", module);
    let start = Instant::now();
    let mpath = rpath.join(module);
    let summary = mpath.join("SUMMARY");
    let summary = Summary::from(File::open(summary).unwrap().bytes().map(Result::unwrap));
    assert_eq!(summary.hol_system, "HOL Light");
    let importer = importer.clone();
    rt.block_on(async move {
      for (kind, path) in summary.dep_iterator(&importer.env, &mpath) {
        let mut sync = kind.sync();
        let (tx, rx) = watch::channel(());
        match &mut *importer.jobs.write().unwrap() {
          j => {
            j.insert(kind.clone(), rx);
            if j.len() > 16 { sync = true }
          }
        }
        let fut = importer.clone().import(kind, path, tx);
        if sync { fut.await } else { rt.spawn(fut); }
      }
      importer.flush().await
    });
    println!("finished {} in {:.2}s, total {:.2}s", module,
      start.elapsed().as_secs_f32(), boot.elapsed().as_secs_f32());
  }
  let env = importer.env.read();
  println!("success");
  let thm = "kepler_conjecture_with_assumptions";
  let td = &env[*env.trans.fetches[FetchKind::Thm].get(thm).expect("theorem not found")];
  env.print_always(&td.arena, |p| println!("{}:\n{}", thm, p.pp(td.concl)));
}
