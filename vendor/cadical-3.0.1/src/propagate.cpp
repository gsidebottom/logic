#include "internal.hpp"

#include <unordered_set>
#include <chrono>
#include <cstdlib>

// CADICAL_TABLE_STATS=1: counters and timers for the native table hook,
// printed at exit (the sampling profilers are unavailable on this host).
namespace {
struct TStats {
  uint64_t calls = 0, updates = 0, visits = 0, forced = 0, conflicts = 0, reasons = 0;
  uint64_t ns_hook = 0, ns_reason = 0;
  bool on = false, registered = false;
} tstats;
static inline uint64_t tnow () {
  return (uint64_t) std::chrono::duration_cast<std::chrono::nanoseconds> (
             std::chrono::steady_clock::now ().time_since_epoch ()).count ();
}
static void tstats_print () {
  fprintf (stderr,
           "c tables: %llu fixpoint passes, %llu updates, %llu visits, %llu forced, %llu conflicts, "
           "%llu reasons; %.2f s in the hook, %.2f s building reasons\n",
           (unsigned long long) tstats.calls, (unsigned long long) tstats.updates, (unsigned long long) tstats.visits,
           (unsigned long long) tstats.forced, (unsigned long long) tstats.conflicts,
           (unsigned long long) tstats.reasons, tstats.ns_hook * 1e-9, tstats.ns_reason * 1e-9);
}
} // namespace

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// We are using the address of 'decision_reason' as pseudo reason for
// decisions to distinguish assignment decisions from other assignments.
// Before we added chronological backtracking all learned units were
// assigned at decision level zero ('Solver.level == 0') and we just used a
// zero pointer as reason.  After allowing chronological backtracking units
// were also assigned at higher decision level (but with assignment level
// zero), and it was not possible anymore to just distinguish the case
// 'unit' versus 'decision' by just looking at the current level.  Both had
// a zero pointer as reason.  Now only units have a zero reason and
// decisions need to use the pseudo reason 'decision_reason'.

// External propagation steps use the pseudo reason 'external_reason'.
// The corresponding actual reason clauses are learned only when they are
// relevant in conflict analysis or in root-level fixing steps.

static Clause decision_reason_clause;
Clause *Internal::decision_reason = &decision_reason_clause;

// If chronological backtracking is used the actual assignment level might
// be lower than the current decision level. In this case the assignment
// level is defined as the maximum level of the literals in the reason
// clause except the literal for which the clause is a reason.  This
// function determines this assignment level. For non-chronological
// backtracking as in classical CDCL this function always returns the
// current decision level, the concept of assignment level does not make
// sense, and accordingly this function can be skipped.

// In case of external propagation, it is implicitly assumed that the
// assignment level is the level of the literal (since the reason clause,
// i.e., the set of other literals, is unknown).

inline int Internal::assignment_level (int lit, Clause *reason) {

  if (!reason || reason == external_reason)
    return level;

  int res = 0;

  for (const auto &other : *reason) {
    if (other == lit)
      continue;
    assert (val (other));
    int tmp = var (other).level;
    if (tmp > res)
      res = tmp;
  }

  return res;
}

// calculate lrat_chain
//
void Internal::build_chain_for_units (int lit, Clause *reason,
                                      bool forced) {
  if (!lrat)
    return;
  if (assignment_level (lit, reason) && !forced)
    return;
  assert (lrat_chain.empty ());
  for (auto &reason_lit : *reason) {
    if (lit == reason_lit)
      continue;
    assert (val (reason_lit));
    if (!val (reason_lit))
      continue;
    const int signed_reason_lit = val (reason_lit) * reason_lit;
    int64_t id = unit_id (signed_reason_lit);
    lrat_chain.push_back (id);
  }
  lrat_chain.push_back (reason->id);
}

// same code as above but reason is assumed to be conflict and lit is not
// needed
//
void Internal::build_chain_for_empty () {
  if (!lrat || !lrat_chain.empty ())
    return;
  assert (!level || in_mode (BACKBONE));
  assert (lrat_chain.empty ());
  assert (conflict);
  LOG (conflict, "lrat for global empty clause with conflict");
  for (auto &lit : *conflict) {
    assert (val (lit) < 0);
    int64_t id = unit_id (-lit);
    lrat_chain.push_back (id);
  }
  lrat_chain.push_back (conflict->id);
}

/*------------------------------------------------------------------------*/

inline void Internal::search_assign (int lit, Clause *reason) {

  if (level)
    require_mode (SEARCH);

  const int idx = vidx (lit);
  const bool from_external = reason == external_reason;
  assert (!val (idx));
  assert (!flags (idx).eliminated () || reason == decision_reason ||
          reason == external_reason);
  Var &v = var (idx);
  int lit_level;
  assert (!lrat || level || reason == external_reason ||
          reason == decision_reason || !lrat_chain.empty ());
  // The following cases are explained in the two comments above before
  // 'decision_reason' and 'assignment_level'.
  //
  // External decision reason means that the propagation was done by
  // an external propagation and the reason clause not known (yet).
  // In that case it is assumed that the propagation is NOT out of
  // order (i.e. lit_level = level), because due to lazy explanation,
  // we can not calculate the real assignment level.
  // The function assignment_level () will also assign the current level
  // to literals with external reason.
  if (!reason)
    lit_level = 0; // unit
  else if (reason == decision_reason)
    lit_level = level, reason = 0;
  else
    lit_level = assignment_level (lit, reason);
  if (!lit_level)
    reason = 0;

  v.level = lit_level;
  v.trail = trail.size ();
  v.reason = reason;
  assert ((int) num_assigned < max_var);
  assert (num_assigned == trail.size ());
  num_assigned++;
  if (!lit_level && !from_external)
    learn_unit_clause (lit); // increases 'stats.fixed'
  assert (lit_level || !from_external);
  const signed char tmp = sign (lit);
  set_val (idx, tmp);
  assert (val (lit) > 0);  // Just a bit paranoid but useful.
  assert (val (-lit) < 0); // Ditto.
  if (!searching_lucky_phases)
    phases.saved[idx] = tmp; // phase saving during search
  trail.push_back (lit);
#ifdef LOGGING
  if (!lit_level)
    LOG ("root-level unit assign %d @ 0", lit);
  else
    LOG (reason, "search assign %d @ %d", lit, lit_level);
#endif

  if (watching ()) {
    const Watches &ws = watches (-lit);
    if (!ws.empty ()) {
      const Watch &w = ws[0];
      __builtin_prefetch (&w, 0, 1);
    }
  }
  lrat_chain.clear ();
}

/*------------------------------------------------------------------------*/

// External versions of 'search_assign' which are not inlined.  They either
// are used to assign unit clauses on the root-level, in 'decide' to assign
// a decision or in 'analyze' to assign the literal 'driven' by a learned
// clause.  This happens far less frequently than the 'search_assign' above,
// which is called directly in 'propagate' below and thus is inlined.

void Internal::assign_unit (int lit) {
  assert (!level);
  search_assign (lit, 0);
}

// Just assume the given literal as decision (increase decision level and
// assign it).  This is used below in 'decide'.

void Internal::search_assume_decision (int lit) {
  require_mode (SEARCH);
  assert (propagated == trail.size ());
  new_trail_level (lit);
  notify_decision ();
  LOG ("search decide %d", lit);
  search_assign (lit, decision_reason);
}

void Internal::search_assign_driving (int lit, Clause *c) {
  require_mode (SEARCH);
  search_assign (lit, c);
  notify_assignments ();
}

void Internal::search_assign_external (int lit) {
  require_mode (SEARCH);
  search_assign (lit, external_reason);
  notify_assignments ();
}

/*------------------------------------------------------------------------*/

// The 'propagate' function is usually the hot-spot of a CDCL SAT solver.
// The 'trail' stack saves assigned variables and is used here as BFS queue
// for checking clauses with the negation of assigned variables for being in
// conflict or whether they produce additional assignments.

// This version of 'propagate' uses lazy watches and keeps two watched
// literals at the beginning of the clause.  We also use 'blocking literals'
// to reduce the number of times clauses have to be visited (2008 JSAT paper
// by Chu, Harwood and Stuckey).  The watches know if a watched clause is
// binary, in which case it never has to be visited.  If a binary clause is
// falsified we continue propagating.

// Finally, for long clauses we save the position of the last watch
// replacement in 'pos', which in turn reduces certain quadratic accumulated
// propagation costs (2013 JAIR article by Ian Gent) at the expense of four
// more bytes for each clause.

/*------------------------------------------------------------------------*/

// Native table constraints (see 'internal.hpp').

void Internal::add_table (const std::vector<int> &vars,
                          const std::vector<std::vector<int>> &rows) {
  if (!tstats.registered) {
    tstats.registered = true;
    tstats.on = getenv ("CADICAL_TABLE_STATS") != 0;
    if (tstats.on) atexit (tstats_print);
  }
  TTable T;
  T.vars = vars;
  const size_t nr = rows.size ();
  T.nwords = (int) ((nr + 63) / 64);
  if (!T.nwords) T.nwords = 1;
  T.full.assign (T.nwords, 0);
  for (size_t r = 0; r < nr; r++) T.full[r / 64] |= (uint64_t) 1 << (r % 64);
  T.kill.assign (2 * vars.size () * T.nwords, 0);
  for (size_t r = 0; r < nr; r++) {
    for (const int lit : rows[r]) {
      const int v = abs (lit);
      size_t li = 0;
      while (li < vars.size () && vars[li] != v) li++;
      assert (li < vars.size ());
      // a row with the variable TRUE dies when it is assigned FALSE (value 0)
      const size_t slot = (2 * li + (lit > 0 ? 0 : 1)) * T.nwords;
      T.kill[slot + r / 64] |= (uint64_t) 1 << (r % 64);
    }
  }
  // Variables already assigned at the root (unit clauses added before the
  // table) were propagated before the table existed: fold them in now.
  if (level) backtrack (0);
  T.words = T.full;
  for (size_t li = 0; li < vars.size (); li++) {
    const signed char x = val (vars[li]);
    if (!x) continue;
    const uint64_t *k = &T.kill[(2 * li + (x > 0 ? 1 : 0)) * T.nwords];
    for (int w = 0; w < T.nwords; w++) T.words[w] &= ~k[w];
  }
  T.index.resize (T.nwords);
  T.limit = 0;
  for (int w = 0; w < T.nwords; w++) if (T.words[w]) T.index[T.limit++] = w;
  for (int w = 0, i = T.limit; w < T.nwords; w++) if (!T.words[w]) T.index[i++] = w;
  T.stamp.assign (T.nwords, -1);
  T.limit_stamp = -1;
  T.residue.assign (2 * vars.size (), 0);
  const int t = (int) ttables.size ();
  if (tocc.size () < vsize) { tocc.resize (vsize); treason.resize (vsize, -1); }
  for (size_t li = 0; li < vars.size (); li++) {
    if (flags (vars[li]).unused ()) mark_active (vars[li]);
    tocc[vars[li]].push_back (std::make_pair (t, (int) li));
  }
  ttables.push_back (T);
  ttouched_flag.resize (ttables.size () + 1, 0);
  ttouched_flag[t] = 1;
  ttouched.push_back (t); // examined once before any assignment: it may force at the root
  tassigned = trail.size (); // the fold above covers the trail so far
}

// AND the assigned literal's kill masks into the non-zero words of its
// tables; a table whose rows changed is touched.  Called from the
// propagate loop as the literal is processed, so kept literals that
// CaDiCaL re-propagates after a backtrack are applied again.
void Internal::table_assign (int lit) {
  const int idx = vidx (lit);
  if ((size_t) idx >= tocc.size ()) return;
  const int value = lit > 0 ? 1 : 0;
  for (const auto &p : tocc[idx]) {
    const int t = p.first;
    TTable &T = ttables[t];
    const uint64_t *k = &T.kill[(2 * p.second + value) * T.nwords];
    bool changed = false;
    int i = 0;
    while (i < T.limit) {
      const int w = T.index[i];
      const uint64_t old = T.words[w];
      const uint64_t nv = old & ~k[w];
      if (nv == old) { i++; continue; }
      if (level && T.stamp[w] != level) {
        tundo.push_back ({t, w, level, old});
        T.stamp[w] = level;
      }
      T.words[w] = nv;
      changed = true;
      if (nv) { i++; continue; }
      if (level && T.limit_stamp != level) {
        tundo.push_back ({t, -1, level, (uint64_t) T.limit});
        T.limit_stamp = level;
      }
      T.limit--;
      T.index[i] = T.index[T.limit];
      T.index[T.limit] = w;
    }
    tstats.updates++;
    if (changed && !ttouched_flag[t]) {
      ttouched_flag[t] = 1;
      ttouched.push_back (t);
    }
  }
}

// Apply every trail literal not yet applied.  The trail is the source of
// truth, not the propagate loop: probing, vivification and the other
// inprocessors assign root units through their own propagation, past the
// loop's pointer (an external propagator is told through its own
// 'notified' pointer for the same reason).
void Internal::table_sync () {
  while (tassigned < trail.size ())
    table_assign (trail[tassigned++]);
}

// Restore the words saved above 'new_level'; literals kept by the
// backtrack (out of order, below the level) are re-applied from
// 'assigned' on, as CaDiCaL re-propagates and re-notifies them.
void Internal::tables_backtrack (int new_level, size_t assigned) {
  while (!tundo.empty () && tundo.back ().level > new_level) {
    const TUndo &u = tundo.back ();
    TTable &T = ttables[u.table];
    if (u.word < 0) { T.limit = (int) u.old; T.limit_stamp = -1; }
    else { T.words[u.word] = u.old; T.stamp[u.word] = -1; }
    tundo.pop_back ();
  }
  if (tassigned > assigned)
    tassigned = assigned;
}

// A trail-order cover: literals of the assigned variables (trail position
// below 'limit') whose kill masks together kill every row of 'target';
// pushed on 'tclause' negated, i.e. as the clause literals.
void Internal::table_cover (int t, const uint64_t *target, size_t limit) {
  const TTable &T = ttables[t];
  const int nw = T.nwords;
  std::vector<uint64_t> rem (target, target + nw);
  std::vector<std::pair<int, int>> order; // (trail position, local index)
  for (size_t li = 0; li < T.vars.size (); li++) {
    const int v = T.vars[li];
    if (!val (v)) continue;
    const Var &x = var (v);
    if ((size_t) x.trail >= limit) continue;
    order.push_back (std::make_pair (x.trail, (int) li));
  }
  std::sort (order.begin (), order.end ());
  for (const auto &pr : order) {
    bool any = false;
    for (int w = 0; w < nw; w++) if (rem[w]) { any = true; break; }
    if (!any) break;
    const int li = pr.second;
    const int v = T.vars[li];
    const signed char x = val (v);
    const uint64_t *k = &T.kill[(2 * li + (x > 0 ? 1 : 0)) * nw];
    bool hits = false;
    for (int w = 0; w < nw; w++) if (rem[w] & k[w]) { hits = true; break; }
    if (!hits) continue;
    tclause.push_back (x > 0 ? -v : v);
    for (int w = 0; w < nw; w++) rem[w] &= ~k[w];
  }
#ifndef NDEBUG
  for (int w = 0; w < nw; w++) assert (!rem[w]);
#endif
}

static bool table_trace () { static int t = -1; if (t < 0) t = getenv ("CADICAL_TABLE_TRACE") ? 1 : 0; return t; }

// Install 'tclause' through the external-clause path (as an external
// propagator's reason or conflict clause would be), without disturbing
// the clause under construction or the LRAT chain.
Clause *Internal::install_table_clause (bool no_backtrack) {
  assert (original.empty ());
  auto clause_tmp = std::move (clause);
  clause.clear ();
  std::vector<int64_t> chain_tmp = std::move (lrat_chain);
  lrat_chain.clear ();
  assert (!force_no_backtrack);
  assert (!from_propagator);
  force_no_backtrack = no_backtrack;
  from_propagator = true;
  ext_clause_forgettable = true;
  for (const int lit : tclause) add_original_lit (lit);
  add_original_lit (0);
  force_no_backtrack = false;
  from_propagator = false;
  assert (original.empty ());
  assert (clause.empty ());
  clause = std::move (clause_tmp);
  lrat_chain = std::move (chain_tmp);
  return newest_clause;
}

Clause *Internal::learn_table_reason_clause (int ilit, bool no_backtrack) {
  const uint64_t t0 = tstats.on ? tnow () : 0;
  tstats.reasons++;
  struct Timer { uint64_t t0; ~Timer () { if (tstats.on) tstats.ns_reason += tnow () - t0; } } timer{t0};
  const int idx = vidx (ilit);
  const int t = treason[idx];
  assert (t >= 0);
  const TTable &T = ttables[t];
  const int nw = T.nwords;
  const int tlit = val (ilit) > 0 ? ilit : -ilit; // the literal that was propagated
  size_t li = 0;
  while (li < T.vars.size () && T.vars[li] != idx) li++;
  assert (li < T.vars.size ());
  // the rows with the variable at its forced value survive; every other
  // root row must be dead, and the cover says by which literals
  const uint64_t *spec = &T.kill[(2 * li + (tlit > 0 ? 0 : 1)) * nw];
  std::vector<uint64_t> target (nw);
  for (int w = 0; w < nw; w++) target[w] = T.full[w] & ~spec[w];
  tclause.clear ();
  tclause.push_back (tlit);
  table_cover (t, target.data (), (size_t) var (idx).trail);
  return install_table_clause (no_backtrack);
}

// Every live row has variable 'li' at 'value' iff no live row lies outside
// the rows that die when the variable takes the other value.
bool Internal::table_forced (TTable &T, int li, int value) {
  const uint64_t *k = &T.kill[(2 * li + (1 - value)) * T.nwords];
  int &r = T.residue[2 * li + value];
  if (T.words[r] & ~k[r]) return false;
  for (int i = 0; i < T.limit; i++) {
    const int w = T.index[i];
    if (T.words[w] & ~k[w]) { r = w; return false; }
  }
  return true;
}

void Internal::propagate_table (int t) {
  TTable &T = ttables[t];
  if (table_trace ()) {
    fprintf (stderr, "[table] visit %d at level %d: live words %d; vals", t, level, T.limit);
    for (size_t li = 0; li < T.vars.size (); li++) fprintf (stderr, " %d=%d", T.vars[li], (int) val (T.vars[li]));
    fprintf (stderr, "%s\n", T.limit ? "" : " DEAD");
  }
  if (!T.limit) {
    tstats.conflicts++;
    if (!level) { learn_empty_clause (); return; }
    tclause.clear ();
    table_cover (t, T.full.data (), trail.size ());
    if (table_trace ()) {
      fprintf (stderr, "[table] conflict at level %d:", level);
      for (const int l : tclause) fprintf (stderr, " %d@%d", l, var (l).level);
      fprintf (stderr, "\n");
    }
    if (tclause.size () == 1) {
      const int u = tclause[0];
      backtrack (0);
      assign_unit (u);
      return;
    }
    assert (clause.empty ());
    for (const int l : tclause) clause.push_back (l);
    move_literals_to_watch ();
    std::unordered_set<int> levels;
    for (const int l : clause) levels.insert (var (l).level);
    Clause *c = new_clause (true, (int) levels.size ());
    watch_clause (c);
    clause.clear ();
    conflict = c;
    return;
  }
  for (size_t li = 0; li < T.vars.size (); li++) {
    const int v = T.vars[li];
    if (val (v)) continue;
    int value;
    if (table_forced (T, (int) li, 1)) value = 1;
    else if (table_forced (T, (int) li, 0)) value = 0;
    else continue;
    const int lit = value ? v : -v;
    tstats.forced++;
    if (table_trace ()) fprintf (stderr, "[table]   forced %d at level %d by table %d\n", lit, level, t);
    if (!level) {
      assign_unit (lit); // implied by the table under the root assignment
    } else {
      search_assign (lit, external_reason);
      treason[v] = t;
    }
  }
}

// Visit the touched tables at the fixpoint of clause propagation (as
// CaDiCaL asks an external propagator).  Visiting at every assignment
// pre-empted the learned clauses and built 53 reason clauses per
// conflict (pyhala-unsat: 626 us per conflict against 109).
void Internal::propagate_touched_tables () {
  const int level_before = level;
  const uint64_t t0 = tstats.on ? tnow () : 0;
  tstats.calls++;
  while (!ttouched.empty () && !conflict && !unsat && level == level_before) {
    const int t = ttouched.back ();
    ttouched.pop_back ();
    ttouched_flag[t] = 0;
    tstats.visits++;
    propagate_table (t);
  }
  if (tstats.on) tstats.ns_hook += tnow () - t0;
}

// Every table has a row all of whose literals hold under the current
// assignment (a diagnostic; the model check in the driver is the gate).
bool Internal::tables_satisfied (bool verbose) {
  bool ok = true;
  for (size_t t = 0; t < ttables.size (); t++) {
    TTable &T = ttables[t];
    // recompute the live rows from the values, independent of 'words'
    std::vector<uint64_t> live (T.full);
    for (size_t li = 0; li < T.vars.size (); li++) {
      const signed char x = val (T.vars[li]);
      if (!x) continue;
      const uint64_t *k = &T.kill[(2 * li + (x > 0 ? 1 : 0)) * T.nwords];
      for (int w = 0; w < T.nwords; w++) live[w] &= ~k[w];
    }
    bool any = false, all_assigned = true;
    for (int w = 0; w < T.nwords; w++) if (live[w]) any = true;
    for (size_t li = 0; li < T.vars.size (); li++) if (!val (T.vars[li])) all_assigned = false;
    bool words_any = T.limit > 0;
    if (any && all_assigned && words_any) continue;
    ok = false;
    if (!verbose) return false;
    fprintf (stderr, "c TABLE CHECK: table %zu %s (live-from-values %s, words limit %d, %s):",
             t, any ? "alive" : "DEAD", any ? "yes" : "no", T.limit, all_assigned ? "all assigned" : "NOT all assigned");
    for (size_t li = 0; li < T.vars.size (); li++) {
      const int v = T.vars[li];
      Flags &f = flags (v);
      fprintf (stderr, " %d=%d[%s%s%s%s%s lvl %d]", v, (int) val (v), f.active () ? "A" : "", f.fixed () ? "F" : "",
               f.eliminated () ? "E" : "", f.substituted () ? "S" : "", f.pure () ? "P" : "", val (v) ? var (v).level : -1);
    }
    fprintf (stderr, "\n");
    // which assigned literals' kills are missing from 'words'?
    for (size_t li = 0; li < T.vars.size (); li++) {
      const signed char x = val (T.vars[li]);
      if (!x) continue;
      const uint64_t *k = &T.kill[(2 * li + (x > 0 ? 1 : 0)) * T.nwords];
      bool missing = false;
      for (int w = 0; w < T.nwords; w++) if (T.words[w] & k[w]) missing = true;
      if (missing) fprintf (stderr, "c TABLE CHECK:   kill of %d=%d (level %d, trail %d, reason %s) NOT applied to words\n",
                            T.vars[li], (int) x, var (T.vars[li]).level, (int) var (T.vars[li]).trail,
                            var (T.vars[li]).reason == external_reason ? "table" : var (T.vars[li]).reason ? "clause" : "decision/unit");
    }
    fprintf (stderr, "c TABLE CHECK:   trail size %zu, propagated %zu, level %d, undo entries %zu, touched %zu\n",
             trail.size (), (size_t) propagated, level, tundo.size (), ttouched.size ());
  }
  return ok;
}

/*------------------------------------------------------------------------*/

bool Internal::propagate () {

  if (level)
    require_mode (SEARCH);
  assert (!unsat);
  LOG ("starting propagate");
  START (propagate);

  // Updating statistics counter in the propagation loops is costly so we
  // delay until propagation ran to completion.
  //
  int64_t before = propagated;
  int64_t ticks = 0;

  // Native tables: clause propagation to its fixpoint, then the trail
  // synced into the tables and the touched ones visited; their forced
  // literals extend the trail and the round repeats.
  for (;;) {

  while (!conflict && propagated != trail.size ()) {

    const int lit = -trail[propagated++];
    LOG ("propagating %d", -lit);
    Watches &ws = watches (lit);

    const const_watch_iterator eow = ws.end ();
    watch_iterator j = ws.begin ();
    const_watch_iterator i = j;
    ticks += 1 + cache_lines (ws.size (), sizeof *i);

    while (i != eow) {

      const Watch w = *j++ = *i++;
      const signed char b = val (w.blit);
      LOG (w.clause, "checking");

      if (b > 0)
        continue; // blocking literal satisfied

      if (w.binary ()) {

        // assert (w.clause->redundant || !w.clause->garbage);

        // In principle we can ignore garbage binary clauses too, but that
        // would require to dereference the clause pointer all the time with
        //
        // if (w.clause->garbage) { j--; continue; } // (*)
        //
        // This is too costly.  It is however necessary to produce correct
        // proof traces if binary clauses are traced to be deleted ('d ...'
        // line) immediately as soon they are marked as garbage.  Actually
        // finding instances where this happens is pretty difficult (six
        // parallel fuzzing jobs in parallel took an hour), but it does
        // occur.  Our strategy to avoid generating incorrect proofs now is
        // to delay tracing the deletion of binary clauses marked as garbage
        // until they are really deleted from memory.  For large clauses
        // this is not necessary since we have to access the clause anyhow.
        //
        // Thanks go to Mathias Fleury, who wanted me to explain why the
        // line '(*)' above was in the code. Removing it actually really
        // improved running times and thus I tried to find concrete
        // instances where this happens (which I found), and then
        // implemented the described fix.

        // Binary clauses are treated separately since they do not require
        // to access the clause at all (only during conflict analysis, and
        // there also only to simplify the code).

        if (b < 0)
          conflict = w.clause; // but continue ...
        else {
          build_chain_for_units (w.blit, w.clause, 0);
          search_assign (w.blit, w.clause);
          // lrat_chain.clear (); done in search_assign
          ticks++;
        }

      } else {
        assert (w.clause->size > 2);

        if (conflict)
          break; // Stop if there was a binary conflict already.

        // The cache line with the clause data is forced to be loaded here
        // and thus this first memory access below is the real hot-spot of
        // the solver.  Note, that this check is positive very rarely and
        // thus branch prediction should be almost perfect here.

        ticks++;

        if (w.clause->garbage) {
          j--;
          continue;
        }

        literal_iterator lits = w.clause->begin ();
        assert (lits[0] == lit || lits[1] == lit);

        // Simplify code by forcing 'lit' to be the second literal in the
        // clause.  This goes back to MiniSAT.  We use a branch-less version
        // for conditionally swapping the first two literals, since it
        // turned out to be substantially faster than this one
        //
        //  if (lits[0] == lit) swap (lits[0], lits[1]);
        //
        // which achieves the same effect, but needs a branch.
        //
        const int other = lits[0] ^ lits[1] ^ lit;
        const signed char u = val (other); // value of the other watch

        if (u > 0)
          j[-1].blit = other; // satisfied, just replace blit
        else {

          // This follows Ian Gent's (JAIR'13) idea of saving the position
          // of the last watch replacement.  In essence it needs two copies
          // of the default search for a watch replacement (in essence the
          // code in the 'if (v < 0) { ... }' block below), one starting at
          // the saved position until the end of the clause and then if that
          // one failed to find a replacement another one starting at the
          // first non-watched literal until the saved position.

          const int size = w.clause->size;
          const literal_iterator middle = lits + w.clause->pos;
          const const_literal_iterator end = lits + size;
          literal_iterator k = middle;

          // Find replacement watch 'r' at position 'k' with value 'v'.
          assert (lits + 2 <= k);
          LOG (w.clause, "search starting at %d", w.clause->pos);
          int r = 0;
          signed char v = -1;

          while (k != end && (v = val (r = *k)) < 0)
            k++;

          if (v < 0) { // need second search starting at the head?

            k = lits + 2;
            assert (w.clause->pos <= size);
            while (k != middle && (v = val (r = *k)) < 0)
              k++;
          }

          w.clause->pos = k - lits; // always save position

          assert (lits + 2 <= k), assert (k <= w.clause->end ());

          if (v > 0) {

            // Replacement satisfied, so just replace 'blit'.

            j[-1].blit = r;

          } else if (!v) {

            // Found new unassigned replacement literal to be watched.

            LOG (w.clause, "unwatch %d in", lit);

            lits[0] = other;
            lits[1] = r;
            *k = lit;

            watch_literal (r, lit, w.clause);

            j--; // Drop this watch from the watch list of 'lit'.

            ticks++;

          } else if (!u) {

            assert (v < 0);

            // The other watch is unassigned ('!u') and all other literals
            // assigned to false (still 'v < 0'), thus we found a unit.
            //
            build_chain_for_units (other, w.clause, 0);
            search_assign (other, w.clause);
            // lrat_chain.clear (); done in search_assign
            ticks++;

            // Similar code is in the implementation of the SAT'18 paper on
            // chronological backtracking but in our experience, this code
            // first does not really seem to be necessary for correctness,
            // and further does not improve running time either.
            //
            if (opts.chrono > 1) {

              const int other_level = var (other).level;

              if (other_level > var (lit).level) {

                // The assignment level of the new unit 'other' is larger
                // than the assignment level of 'lit'.  Thus we should find
                // another literal in the clause at that higher assignment
                // level and watch that instead of 'lit'.

                assert (size > 2);

                int pos, s = 0;

                for (pos = 2; pos < size; pos++)
                  if (var (s = lits[pos]).level == other_level)
                    break;

                assert (s);
                assert (pos < size);

                LOG (w.clause, "unwatch %d in", lit);
                lits[pos] = lit;
                lits[0] = other;
                lits[1] = s;
                watch_literal (s, lit, w.clause);

                j--; // Drop this watch from the watch list of 'lit'.
              }
            }
          } else {

            assert (u < 0);
            assert (v < 0);

            // The other watch is assigned false ('u < 0') and all other
            // literals as well (still 'v < 0'), thus we found a conflict.

            conflict = w.clause;
            break;
          }
        }
      }
    }

    if (j != i) {

      while (i != eow)
        *j++ = *i++;

      ws.resize (j - ws.begin ());
    }

  }

  if (conflict || unsat || ttables.empty ())
    break;
  table_sync ();
  if (ttouched.empty ())
    break;
  propagate_touched_tables ();
  if (conflict || unsat)
    break;
  if (propagated == trail.size () && ttouched.empty ())
    break;
  } // for (;;)

  if (searching_lucky_phases) {

    if (conflict)
      LOG (conflict, "ignoring lucky conflict");

  } else {

    // Avoid updating stats eagerly in the hot-spot of the solver.
    //
    stats.propagations.search += propagated - before;
    stats.ticks.search[stable] += ticks;

    if (!conflict)
      no_conflict_until = propagated;
    else {

      if (stable)
        stats.stabconflicts++;
      stats.conflicts++;

      LOG (conflict, "conflict");

      // The trail before the current decision level was conflict free.
      //
      no_conflict_until = control[level].trail;
    }
  }

  if (conflict && randomized_deciding) {
    if (!--randomized_deciding)
      VERBOSE (3, "last random decision conflict");
  }
  STOP (propagate);

  return !conflict;
}

/*------------------------------------------------------------------------*/

void Internal::propergate () {

  assert (!conflict);
  assert (propagated == trail.size ());

  while (propergated != trail.size ()) {

    const int lit = -trail[propergated++];
    LOG ("propergating %d", -lit);
    Watches &ws = watches (lit);

    const const_watch_iterator eow = ws.end ();
    watch_iterator j = ws.begin ();
    const_watch_iterator i = j;

    while (i != eow) {

      const Watch w = *j++ = *i++;
      LOG (w.clause, "propergate");
      if (w.binary ()) {
        assert (val (w.blit) > 0);
        continue;
      }
      if (w.clause->garbage) {
        j--;
        continue;
      }

      literal_iterator lits = w.clause->begin ();

      const int other = lits[0] ^ lits[1] ^ lit;
      const signed char u = val (other);

      // TODO: check if u == 0 can happen.
      if (u > 0)
        continue;
      assert (u < 0);

      const int size = w.clause->size;
      const literal_iterator middle = lits + w.clause->pos;
      const const_literal_iterator end = lits + size;
      literal_iterator k = middle;

      int r = 0;
      signed char v = -1;

      while (k != end && (v = val (r = *k)) < 0)
        k++;

      if (v < 0) {
        k = lits + 2;
        assert (w.clause->pos <= size);
        while (k != middle && (v = val (r = *k)) < 0)
          k++;
      }

      assert (lits + 2 <= k), assert (k <= w.clause->end ());
      w.clause->pos = k - lits;

      assert (v > 0);

      LOG (w.clause, "unwatch %d in", lit);

      lits[0] = other;
      lits[1] = r;
      *k = lit;

      watch_literal (r, lit, w.clause);

      j--;
    }

    if (j != i) {

      while (i != eow)
        *j++ = *i++;

      ws.resize (j - ws.begin ());
    }
  }
}

} // namespace CaDiCaL
