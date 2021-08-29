mod hol {
  pub mod lexer;
  pub mod parser;
  pub mod kernel;
  pub mod corethy;
  pub mod types;
  pub mod print;
}

use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::io::{Read, BufRead};
use std::time::{Duration, Instant};
use std::fs::File;
use std::path::{Path, PathBuf};
use tokio::runtime::Runtime;
use tokio::sync::Notify;
use tokio::sync::watch::{self, Receiver, Sender};
use hol::parser::Summary;
use hol::types::{FetchKind, ObjectSpec};
use hol::kernel::Environment;

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

  fn import_module(self: Arc<Self>, rt: &Runtime, rpath: &Path, module: &str) {
    println!("importing {}", module);
    let mpath = rpath.join(module);
    let summary = mpath.join("SUMMARY");
    let summary = Summary::from(File::open(summary).unwrap().bytes().map(Result::unwrap));
    assert_eq!(summary.hol_system, "HOL Light");
    rt.block_on(async move {
      for (kind, path) in summary.dep_iterator(&self.env, &mpath) {
        let mut sync = kind.sync();
        let (tx, rx) = watch::channel(());
        match &mut *self.jobs.write().unwrap() {
          j => {
            j.insert(kind.clone(), rx);
            if j.len() > 16 { sync = true }
          }
        }
        let fut = self.clone().import(kind, path, tx);
        if sync { fut.await } else { rt.spawn(fut); }
      }
      self.flush().await
    });
  }
}

fn main() {
  let mut rpath = PathBuf::from(".");
  let rt = &Runtime::new().unwrap();
  let importer = Arc::new(Importer {
    env: Environment::new(),
    jobs: Default::default(),
    flush: Default::default(),
  });
  let mut total = Duration::ZERO;
  for line in std::io::stdin().lock().lines() {
    let line = line.unwrap();
    let (cmd, arg) = match line.split_once(" ") {
      Some((cmd, arg)) => (cmd, arg),
      None => (&*line, "")
    };
    match cmd {
      "set-cwd" => rpath = PathBuf::from(arg),
      "import" => {
        let start = Instant::now();
        importer.clone().import_module(rt, &rpath, arg);
        let dur = start.elapsed();
        total += dur;
        println!("finished {} in {:.2}s, total {:.2}s", arg,
          dur.as_secs_f32(), total.as_secs_f32());
      }
      "print-thm" => {
        let env = importer.env.read();
        let td = &env[*env.trans.fetches[FetchKind::Thm].get(arg).expect("theorem not found")];
        env.print_always(&td.arena, |p| println!("{}:\n{}", arg, p.pp(td.concl)));
      }
      _ => panic!("unexpected command {}", cmd),
    }
  }
}
