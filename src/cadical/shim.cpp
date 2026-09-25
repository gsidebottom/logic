// C ABI over CaDiCaL 3.0.1's C++ interface, for `src/cadical/solver.rs`.
//
// CaDiCaL ships a C façade of its own (`ccadical.cpp`), but it exposes no
// learner: the web UI's learned-clause panel and `sat --backend cadical`'s
// progress line both need one, so we bind the C++ API directly.  Only the
// calls `solver.rs` offers are here.
//
// Rust owns the callback object and passes it back as `data`; this file
// owns nothing but the solver and the literal buffer a learned clause is
// assembled in (CaDiCaL hands them over one literal at a time).

// The counters behind the summary line: CaDiCaL 3.0.1's public API prints
// its statistics but does not expose them, and the internal solver is a
// private member.  Read through the usual hack, for diagnostics only.
#define private public
#include "cadical.hpp"
#include "internal.hpp"
#undef private

#include <cstddef>
#include <vector>

namespace {

typedef int (*c3_terminate_fn) (void *);
typedef void (*c3_learn_fn) (void *, const int *, size_t);

// Both callbacks CaDiCaL takes, routed to one Rust object.
struct Hooks : public CaDiCaL::Terminator, public CaDiCaL::Learner {
  void *data = 0;
  c3_terminate_fn on_terminate = 0;
  c3_learn_fn on_learn = 0;
  int max_length = 0;
  std::vector<int> clause;

  bool terminate () { return on_terminate && on_terminate (data); }

  // Declining here is what keeps the export path cold for callers that
  // only want termination (`max_length` <= 0).
  bool learning (int size) { return on_learn && size <= max_length; }

  void learn (int lit) {
    if (lit)
      clause.push_back (lit);
    else {
      if (on_learn)
        on_learn (data, clause.data (), clause.size ());
      clause.clear ();
    }
  }
};

struct Wrapper {
  CaDiCaL::Solver solver;
  Hooks hooks;
};

inline Wrapper *self (void *s) { return static_cast<Wrapper *> (s); }

} // namespace

extern "C" {

void *c3_new () { return new Wrapper (); }

void c3_delete (void *s) { delete self (s); }

const char *c3_signature () { return CaDiCaL::Solver::signature (); }

void c3_add_clause (void *s, const int *lits, size_t len) {
  CaDiCaL::Solver &solver = self (s)->solver;
  for (size_t i = 0; i != len; i++)
    solver.add (lits[i]);
  solver.add (0);
}

int c3_solve (void *s) { return self (s)->solver.solve (); }

int c3_status (void *s) { return self (s)->solver.status (); }

// Only legal in the SATISFIED state — CaDiCaL aborts the process on a
// contract violation, so the state check stays on this side of the ABI.
// Declared-but-unused variables get CaDiCaL's default value, so every
// literal in range answers.
int c3_val (void *s, int lit) {
  CaDiCaL::Solver &solver = self (s)->solver;
  if (solver.status () != 10 || !lit)
    return 0;
  return solver.val (lit);
}

int c3_max_var (void *s) { return self (s)->solver.vars (); }

int64_t c3_conflicts (void *s) { return self (s)->solver.internal->stats.conflicts; }
int64_t c3_decisions (void *s) { return self (s)->solver.internal->stats.decisions; }
int64_t c3_propagations (void *s) { return self (s)->solver.internal->stats.propagations.search; }

// Clause quality: learned clauses and their literals as stored (after
// minimisation and shrinking), the literals those two removed, and what
// inprocessing did to the clause database.
int64_t c3_learned_clauses (void *s) { return self (s)->solver.internal->stats.learned.clauses; }
int64_t c3_learned_literals (void *s) { return self (s)->solver.internal->stats.learned.literals; }
int64_t c3_minimized (void *s) { return self (s)->solver.internal->stats.minimized; }
int64_t c3_shrunken (void *s) { return self (s)->solver.internal->stats.shrunken; }
int64_t c3_vivified (void *s) {
  CaDiCaL::Stats &st = self (s)->solver.internal->stats;
  return st.vivifiedirred + st.vivifiedtier1 + st.vivifiedtier2 + st.vivifiedtier3;
}
int64_t c3_subsumed (void *s) { return self (s)->solver.internal->stats.subsumed; }
int64_t c3_strengthened (void *s) { return self (s)->solver.internal->stats.strengthened; }
int64_t c3_eagersub (void *s) { return self (s)->solver.internal->stats.eagersub; }

// Initializes `n` further variables and protects them from being taken as
// bounded-variable-addition extension variables.  With `factor` on,
// CaDiCaL 3.0.1 *requires* user variables to be declared this way before
// they appear in a clause (`factorcheck`) and aborts the process
// otherwise; the standalone binary does it from the `p cnf` header.
int c3_declare_vars (void *s, int n) {
  return self (s)->solver.declare_more_variables (n);
}

// Most options may only be set before the first clause (CaDiCaL requires
// the CONFIGURING state); `solver.rs` enforces that, and an unknown name
// returns false rather than aborting.
int c3_set_option (void *s, const char *name, int val) {
  return self (s)->solver.set (name, val) ? 1 : 0;
}

void c3_connect (void *s, void *data, c3_terminate_fn on_terminate,
                 c3_learn_fn on_learn, int max_length) {
  Wrapper *w = self (s);
  w->hooks.data = data;
  w->hooks.on_terminate = on_terminate;
  w->hooks.on_learn = on_learn;
  w->hooks.max_length = max_length;
  if (on_terminate)
    w->solver.connect_terminator (&w->hooks);
  else
    w->solver.disconnect_terminator ();
  if (on_learn)
    w->solver.connect_learner (&w->hooks);
  else
    w->solver.disconnect_learner ();
}

// ---- IPASIR-UP: an external propagator whose callbacks live in Rust ----
//
// A clause callback fills `out` with a reason clause for `lit` (lit != 0,
// the clause containing lit) or an external clause (lit == 0, a conflict
// under the current assignment), returning its length, 0 for none.
typedef void (*c3_pnotify_fn) (void *, const int *, size_t);
typedef void (*c3_plevel_fn) (void *);
typedef void (*c3_pbacktrack_fn) (void *, size_t);
typedef int (*c3_pcheck_fn) (void *, const int *, size_t);
typedef int (*c3_ppropagate_fn) (void *);
typedef size_t (*c3_pclause_fn) (void *, int, int *, size_t);

struct BoxProp : CaDiCaL::ExternalPropagator {
  void *data = 0;
  c3_pnotify_fn notify = 0;
  c3_plevel_fn level = 0;
  c3_pbacktrack_fn backtrack = 0;
  c3_pcheck_fn check = 0;
  c3_ppropagate_fn propagate = 0;
  c3_pclause_fn clause = 0;
  std::vector<int> rbuf, ebuf;
  size_t rpos = 0, rlen = 0, epos = 0, elen = 0;
  BoxProp () { rbuf.resize (1 << 16); ebuf.resize (1 << 16); }
  void notify_assignment (const std::vector<int> &lits) override {
    notify (data, lits.data (), lits.size ());
  }
  void notify_new_decision_level () override { level (data); }
  void notify_backtrack (size_t l) override { backtrack (data, l); }
  bool cb_check_found_model (const std::vector<int> &m) override {
    return check (data, m.data (), m.size ()) != 0;
  }
  int cb_propagate () override { return propagate (data); }
  // CaDiCaL pulls a reason literal by literal until 0; the first call for
  // a literal fetches the whole clause.
  int cb_add_reason_clause_lit (int lit) override {
    if (!rlen) { rlen = clause (data, lit, rbuf.data (), rbuf.size ()); rpos = 0; }
    if (rpos < rlen) return rbuf[rpos++];
    rlen = rpos = 0;
    return 0;
  }
  bool cb_has_external_clause (bool &forgettable) override {
    elen = clause (data, 0, ebuf.data (), ebuf.size ());
    epos = 0;
    forgettable = true;
    return elen > 0;
  }
  int cb_add_external_clause_lit () override {
    if (epos < elen) return ebuf[epos++];
    elen = epos = 0;
    return 0;
  }
};

void *c3_connect_propagator (void *s, void *data, c3_pnotify_fn notify, c3_plevel_fn level,
                             c3_pbacktrack_fn backtrack, c3_pcheck_fn check,
                             c3_ppropagate_fn propagate, c3_pclause_fn clause) {
  BoxProp *p = new BoxProp ();
  p->data = data; p->notify = notify; p->level = level; p->backtrack = backtrack;
  p->check = check; p->propagate = propagate; p->clause = clause;
  p->are_reasons_forgettable = true;
  self (s)->solver.connect_external_propagator (p);
  return p;
}

void c3_disconnect_propagator (void *s, void *p) {
  self (s)->solver.disconnect_external_propagator ();
  delete (BoxProp *) p;
}

void c3_add_observed_var (void *s, int var) { self (s)->solver.add_observed_var (var); }

void c3_disconnect (void *s) {
  Wrapper *w = self (s);
  w->solver.disconnect_terminator ();
  w->solver.disconnect_learner ();
  w->hooks.data = 0;
  w->hooks.on_terminate = 0;
  w->hooks.on_learn = 0;
}

} // extern "C"
