//! DRAT proof logging for the box engine (`doc/box_backend_design.md` §4).
//!
//! The engine's refutation is certified against the **original** formula —
//! the clauses it was given plus, when boxes are plugged in, the clauses
//! those boxes stand for (`--boxes-source`).  Two kinds of step reach the
//! sink:
//!
//! * **Learned clauses.**  A 1-UIP clause is a resolution consequence of the
//!   reasons on the trail, so it is RUP over the clauses emitted so far —
//!   an ordinary DRAT addition, exactly as a clausal CDCL solver logs.
//! * **Box lemmas.**  A table propagation is *not* unit propagation (that is
//!   the point of boxes: generalized arc consistency over a cone), so the
//!   clause `ℓ ∨ ¬A` it justifies is implied by the box's source clauses but
//!   need not be RUP over them.  The engine derives each such lemma once,
//!   with a sub-refutation by a second engine over the source clauses under
//!   the assumption `¬(ℓ ∨ ¬A)`; that sub-refutation's own learned clauses
//!   are ordinary RUP additions, and the lemma itself is RUP once they are
//!   in the proof.  The recursion bottoms out because the sub-engine holds
//!   no boxes.
//!
//! A lemma the sub-refutation cannot derive marks the proof `incomplete`:
//! the verdict still stands (the table is trusted for it), but the file is
//! not a certificate and the caller must not offer it as one.

use std::io::Write;

/// Where the steps go: a file for the engine being certified, a buffer for
/// the sub-engine whose steps its parent splices in.
enum Sink {
    Writer(std::io::BufWriter<std::fs::File>),
    Buffer(Vec<Vec<i32>>),
}

/// A DRAT sink.  Literals arrive in the engine's code form
/// (`var << 1 | neg`) and are written as DIMACS.
pub struct Proof {
    sink: Sink,
    /// Clause additions and deletions written.
    pub steps: u64,
    pub deletions: u64,
    /// Box lemmas derived, and the sub-refutation steps they cost.
    pub lemmas: u64,
    pub lemma_steps: u64,
    /// Why the file is not a certificate, if it is not.
    pub incomplete: Option<String>,
    /// Set once the empty clause has been written.
    pub closed: bool,
}

#[inline]
fn dimacs(l: u32) -> i32 {
    let v = (l >> 1) as i32 + 1;
    if l & 1 == 1 { -v } else { v }
}

impl Proof {
    /// A proof written to `path` as it is produced.
    pub fn to_file(path: &std::path::Path) -> std::io::Result<Proof> {
        let f = std::fs::File::create(path)?;
        Ok(Proof { sink: Sink::Writer(std::io::BufWriter::new(f)), steps: 0, deletions: 0, lemmas: 0, lemma_steps: 0, incomplete: None, closed: false })
    }

    /// A proof collected in memory (the sub-engine's; its parent drains it).
    pub fn buffer() -> Proof {
        Proof { sink: Sink::Buffer(Vec::new()), steps: 0, deletions: 0, lemmas: 0, lemma_steps: 0, incomplete: None, closed: false }
    }

    /// Record that the proof cannot be completed (first reason wins).
    pub fn fail(&mut self, why: impl Into<String>) {
        if self.incomplete.is_none() { self.incomplete = Some(why.into()); }
    }

    /// A clause addition, in the engine's literal codes.  Steps after the
    /// empty clause are dropped: the refutation is finished, and a sub-proof
    /// that reached the empty clause on its own finishes the parent's too.
    pub fn add(&mut self, lits: &[u32]) {
        if self.closed { return; }
        self.steps += 1;
        match &mut self.sink {
            Sink::Writer(w) => {
                let mut line = String::with_capacity(4 * lits.len() + 2);
                for &l in lits { line.push_str(&dimacs(l).to_string()); line.push(' '); }
                line.push_str("0\n");
                let _ = w.write_all(line.as_bytes());
            }
            Sink::Buffer(b) => b.push(lits.iter().map(|&l| dimacs(l)).collect()),
        }
    }

    /// A clause addition already in DIMACS (splicing a sub-proof).
    pub fn add_dimacs(&mut self, lits: &[i32]) {
        if self.closed { return; }
        self.steps += 1;
        match &mut self.sink {
            Sink::Writer(w) => {
                let mut line = String::with_capacity(4 * lits.len() + 2);
                for &l in lits { line.push_str(&l.to_string()); line.push(' '); }
                line.push_str("0\n");
                let _ = w.write_all(line.as_bytes());
            }
            Sink::Buffer(b) => b.push(lits.to_vec()),
        }
    }

    /// A clause deletion.  Deletions only speed the checker up; dropping one
    /// is always sound, so the buffered sink ignores them.
    pub fn del(&mut self, lits: &[u32]) {
        if self.closed { return; }
        match &mut self.sink {
            Sink::Writer(w) => {
                self.deletions += 1;
                let mut line = String::with_capacity(4 * lits.len() + 4);
                line.push_str("d ");
                for &l in lits { line.push_str(&dimacs(l).to_string()); line.push(' '); }
                line.push_str("0\n");
                let _ = w.write_all(line.as_bytes());
            }
            Sink::Buffer(_) => {}
        }
    }

    /// The empty clause: the refutation's last step.
    pub fn empty(&mut self) {
        if self.closed { return; }
        self.closed = true;
        self.steps += 1;
        match &mut self.sink {
            Sink::Writer(w) => { let _ = w.write_all(b"0\n"); let _ = w.flush(); }
            Sink::Buffer(b) => b.push(Vec::new()),
        }
    }

    /// Take the buffered steps (sub-engine sinks only).
    pub fn take_buffer(&mut self) -> Vec<Vec<i32>> {
        match &mut self.sink {
            Sink::Buffer(b) => std::mem::take(b),
            Sink::Writer(_) => Vec::new(),
        }
    }

    pub fn flush(&mut self) {
        if let Sink::Writer(w) = &mut self.sink { let _ = w.flush(); }
    }
}
