#include "../src/analyze.h"
#include "../src/backtrack.h"
#include "../src/chb.h"
#include "../src/decide.h"
#include "../src/error.h"
#include "../src/inlinepolicy.h"
#include "../src/propsearch.h"
#include "../src/warmup.h"

#include "test.h"

#include <setjmp.h>

#if !defined(HEAPARGMAX) && !defined(NOPTIONS)

// LRB's reward on CHB's ERWA (see 'lrb.h'): the options it excludes, the
// intervals its walk opens, the participations of an analysis step, the
// reward at the closes of the assignment intervals (see 'intervals.h'),
// and what earns nothing.

static jmp_buf jump_buffer;

static void abort_call_back (void) { longjmp (jump_buffer, 42); }

// Whether the start of the search is a fatal error with 'lrb=1' and the
// options 'name' and 'other', if given.

static bool start_fails (const char *name, int value, const char *other,
                         int other_value) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, "lrb", 1);
  if (name)
    kissat_set_option (solver, name, value);
  if (other)
    kissat_set_option (solver, other, other_value);
  for (int i = 1; i <= 4; i++)
    kissat_add (solver, i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  bool res = false;
  kissat_call_function_instead_of_abort (abort_call_back);
  if (setjmp (jump_buffer))
    res = true;
  else
    kissat_start_policy (solver);
  kissat_call_function_instead_of_abort (0);
  kissat_release (solver);
  return res;
}

// 'lrb' feeds CHB's ERWA and decides by Argmax: without 'chb=1', and with
// Sample, P1, TS, UCB or mixing, the start of the search is a fatal error.
// Feedback builds measure LRB's reward (see 'feedback.h').

static void test_lrb_options (void) {
  assert (start_fails (0, 0, 0, 0));
  assert (start_fails ("chb", 0, 0, 0));
  assert (start_fails ("chb", 1, "softmax", 1));
  assert (start_fails ("chb", 1, "perturbed", 1));
  assert (start_fails ("chb", 1, "thompson", 1));
  assert (start_fails ("chb", 1, "ucb", 1));
  assert (start_fails ("chb", 1, "gammappm", 100));
  assert (!start_fails ("chb", 1, 0, 0));
  assert (!start_fails ("chb", 1, "randecstable", 1));
  assert (!start_fails ("chb", 1, "ucbinterval", 0));
}

// A solver in stable mode with CHB scores and LRB, its policy started as
// the search starts it, over
//
//   (-1 2) (-3 4) (-2 -4 5) (-2 -4 -5) (6 7 8 9)
//
// with the option 'name' set to 'value' if given.  Deciding 1 propagates 2,
// and deciding 3 then propagates 4 and 5 and falsifies (-2 -4 -5).
// Without on-the-fly strengthening the analysis learns (-4 -2), with 4 its
// UIP, from the participants 2, 4 and 5, and the reasons of the learned
// clause's literals, (-3 4) and (-1 2), add 3 and 1 on the reason side; it
// backjumps to level 1 and asserts -4, which propagates -3.

static kissat *new_solver (const char *name, int value) {
  kissat *solver = kissat_init ();
#ifndef NDEBUG
  kissat_set_option (solver, "check", 0);
#endif
  kissat_set_option (solver, "chb", 1);
  kissat_set_option (solver, "lrb", 1);
  if (name)
    kissat_set_option (solver, name, value);
  const int clauses[][5] = {{-1, 2, 0},
                            {-3, 4, 0},
                            {-2, -4, 5, 0},
                            {-2, -4, -5, 0},
                            {6, 7, 8, 9, 0}};
  for (unsigned i = 0; i < sizeof clauses / sizeof *clauses; i++)
    for (const int *p = clauses[i];; p++) {
      kissat_add (solver, *p);
      if (!*p)
        break;
    }
  solver->stable = true;
  kissat_init_averages (solver, &AVERAGES);
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  return solver;
}

static double erwa (double q, double alpha, double reward) {
  return (1 - alpha) * q + alpha * reward;
}

// Every leaf present, with its variable's Q as key, and every internal
// node what its children give: every variable is unassigned.

static void check_fresh_tree (kissat *solver) {
  const tree *const tree = &solver->policy.tree;
  for (all_variables (idx)) {
    assert (kissat_tree_contains (tree, idx));
    assert (kissat_same_double (kissat_tree_key (tree, idx),
                                kissat_get_score (solver, idx)));
  }
  assert (!kissat_tree_inconsistent_node (tree));
}

// The variable's participations in the current step, by hand, as the
// record of an analysis step makes them.

static void participate (kissat *solver, unsigned idx) {
  PUSH_STACK (solver->analyzed, idx);
  kissat_chb_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
}

// LRB starts the assignment intervals on the CHB line with LRB's interval,
// every interval closed, every Q zero and no pseudo-activity.  Argmax-CHB
// starts neither, but in feedback builds, which start the intervals under
// every policy.

static void test_lrb_start (void) {
  kissat *solver = new_solver (0, 0);
  const lrb *const lrb = &solver->policy.lrb;
  const intervals *intervals = &solver->policy.intervals;
  assert (lrb->started);
  assert (lrb->start && lrb->participated && lrb->reasoned);
  assert (lrb->boundary == LRB_NO_BOUNDARY);
  assert (intervals->started && intervals->lrb && intervals->interval);
  assert (!intervals->vsids && !intervals->ucb && !intervals->rounds);
  assert (!intervals->opened);
  assert (!kissat_pseudo_activity (solver));
  for (all_variables (idx)) {
    assert (lrb->start[idx] == LRB_CLOSED);
    assert (kissat_get_score (solver, idx) == 0);
  }
  assert (kissat_policy_pick (solver) == 0);
  kissat_release (solver);
  solver = kissat_init ();
  kissat_set_option (solver, "chb", 1);
  for (unsigned i = 1; i <= 4; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  assert (!solver->policy.lrb.started && !solver->policy.lrb.start);
#ifdef FEEDBACK
  assert (solver->policy.intervals.started);
  assert (!solver->policy.intervals.lrb);
#else
  assert (!solver->policy.intervals.started);
#endif
  kissat_release (solver);
}

// Through the solver's own propagation and analysis (see 'new_solver'),
// with or without Kissat's reason-side literals ('bumpreasons').  The walk
// opens the intervals of 1 and 2 at conflict 0, and those of 3, 4 and 5,
// whose propagation ends in the conflict, at 0 too, before it counts the
// conflict: each of these spans one conflict.  The step's backjump
// unassigns 3, 4 and 5, which close at the step's end, after the record of
// its participants: 4, the UIP, and 5 with the ending conflict's
// participation, reward 1, and 3 with its reason-side one, or none.  The
// leaves of 3 and 5 take the new Q at once; that of 4, asserted again by
// then, lags until it is unassigned.  The asserted literal and the -3 it
// propagates open their intervals at the next walk, at conflict 1, and a
// restart closes them without a conflict, no update, and those of 1 and 2
// after one: 2 participated, 1 on the reason side.

static void conflict_with_reasons (bool reasons) {
  kissat *solver = new_solver ("otfs", 0);
  kissat_set_option (solver, "bumpreasons", reasons);
  const lrb *const lrb = &solver->policy.lrb;
  const tree *const tree = &solver->policy.tree;
  const estimator *const estimator = &solver->estimator;
  kissat_internal_assume (solver, LIT (0));
  assert (!kissat_search_propagate (solver));
  assert (VALUE (LIT (1)) > 0);
  assert (!lrb->start[0] && !lrb->start[1]);
  kissat_internal_assume (solver, LIT (2));
  clause *conflict = kissat_search_propagate (solver);
  assert (conflict);
  assert (estimator->chb.conflicts == 1);
  for (unsigned idx = 0; idx < 5; idx++)
    assert (!lrb->start[idx]);
  assert (lrb->count.opened == 5);
  kissat_analyze (solver, conflict);
  assert (solver->level == 1);
  assert (VALUE (LIT (3)) < 0);
  assert (!VALUE (LIT (2)) && !VALUE (LIT (4)));
  assert (lrb->count.participations == 3);
  assert (lrb->count.reasons == (reasons ? 2 : 0));
  assert (estimator->chb.analyzed == 1);
  assert (lrb->count.closed[INTERVALS_CLOSE_DEFERRED] == 3);
  assert (!lrb->count.closed[INTERVALS_CLOSE_UNASSIGNED]);
  assert (lrb->count.updates == 3);
  const double alpha = kissat_chb_alpha (1);
  const double paid = erwa (0, alpha, 1);
  assert (kissat_get_score (solver, 2) == (reasons ? paid : 0));
  assert (kissat_get_score (solver, 3) == paid);
  assert (kissat_get_score (solver, 4) == paid);
  assert (lrb->start[2] == LRB_CLOSED && lrb->start[3] == LRB_CLOSED);
  assert (lrb->start[4] == LRB_CLOSED);
  // 1 and 2 stay assigned in their intervals, with Q unchanged.
  assert (!lrb->start[0] && !lrb->start[1]);
  assert (lrb->participated[1] == 1 && !lrb->reasoned[1]);
  assert (!lrb->participated[0] && lrb->reasoned[0] == reasons);
  assert (!kissat_get_score (solver, 0) && !kissat_get_score (solver, 1));
  // The leaves.
  assert (kissat_tree_key (tree, 2) == kissat_get_score (solver, 2));
  assert (kissat_tree_key (tree, 4) == paid);
  assert (kissat_tree_key (tree, 3) == 0);
  assert (kissat_policy_pick (solver) == (reasons ? 2 : 4));
  // The asserted literal opens its interval at the next walk.
  assert (lrb->start[3] == LRB_CLOSED);
  assert (!kissat_search_propagate (solver));
  assert (VALUE (LIT (2)) < 0);
  assert (lrb->start[3] == 1 && lrb->start[2] == 1);
  assert (lrb->count.opened == 7);
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (lrb->count.closed[INTERVALS_CLOSE_UNASSIGNED] == 4);
  assert (lrb->count.skipped == 2);
  assert (lrb->count.updates == 5);
  assert (kissat_get_score (solver, 0) == (reasons ? paid : 0));
  assert (kissat_get_score (solver, 1) == paid);
  assert (kissat_get_score (solver, 2) == (reasons ? paid : 0));
  assert (kissat_get_score (solver, 3) == paid);
  check_fresh_tree (solver);
#ifndef NDEBUG
  assert (lrb->check.closes == 7);
  assert (lrb->check.logged[0] == 3);
  assert (lrb->check.logged[1] == (reasons ? 2 : 0));
#endif
  kissat_release (solver);
}

static void test_lrb_conflict (void) { conflict_with_reasons (true); }

static void test_lrb_no_reasons (void) { conflict_with_reasons (false); }

// With on-the-fly strengthening the same conflict takes two steps: the
// first strengthens the reason (-2 -4 5) of 5 to the conflict (-2 -4),
// without a backtrack, and records the participants 2, 4 and 5; the
// second reuses that conflict as the driving clause of -4, without
// analysis, and its backtrack ends the intervals of 3, 4 and 5, which close
// at its end with the first step's participations.  No reason side.

static void test_lrb_strengthened (void) {
  kissat *solver = new_solver (0, 0);
  const lrb *const lrb = &solver->policy.lrb;
  kissat_internal_assume (solver, LIT (0));
  assert (!kissat_search_propagate (solver));
  kissat_internal_assume (solver, LIT (2));
  clause *conflict = kissat_search_propagate (solver);
  assert (conflict);
  kissat_analyze (solver, conflict);
  assert (solver->level == 1);
  assert (VALUE (LIT (3)) < 0);
  assert (lrb->count.participations == 3 && !lrb->count.reasons);
  assert (lrb->count.closed[INTERVALS_CLOSE_DEFERRED] == 3);
  const double paid = erwa (0, kissat_chb_alpha (1), 1);
  assert (kissat_get_score (solver, 2) == 0);
  assert (kissat_get_score (solver, 3) == paid);
  assert (kissat_get_score (solver, 4) == paid);
  kissat_release (solver);
}

// The step size at the close: alpha after 100,000 conflicts, 0.3 up to
// rounding, and from 340,001 on its minimum 0.06.  An interval's reward is
// its participations over its conflicts.

static void test_lrb_alpha (void) {
  kissat *solver = new_solver (0, 0);
  estimator *const estimator = &solver->estimator;
  kissat_internal_assume (solver, LIT (5));
  assert (!kissat_search_propagate (solver));
  kissat_internal_assume (solver, LIT (6));
  assert (!kissat_search_propagate (solver));
  estimator->chb.conflicts = 100000;
  participate (solver, 6);
  kissat_backtrack_without_updating_phases (solver, 1);
  assert (kissat_get_score (solver, 6) ==
          erwa (0, kissat_chb_alpha (100000), 1.0 / 100000));
  estimator->chb.conflicts = 350000;
  participate (solver, 5);
  participate (solver, 5);
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (kissat_chb_alpha (350000) == 0.06);
  assert (kissat_get_score (solver, 5) == erwa (0, 0.06, 2.0 / 350000));
  check_fresh_tree (solver);
  kissat_release (solver);
}

// Chronological backtracking keeps a literal of a lower level that lies
// above the new level's trail and moves it down: its interval goes on, the
// walk does not open it again, and it closes when the literal is
// unassigned, with the participations and conflicts since the walk.

static void test_lrb_kept (void) {
  kissat *solver = new_solver (0, 0);
  const lrb *const lrb = &solver->policy.lrb;
  kissat_internal_assume (solver, LIT (5)); // level 1, trail position 0
  kissat_internal_assume (solver, LIT (6)); // level 2, trail position 1
  kissat_internal_assume (solver, LIT (7)); // trail position 2
  solver->assigned[7].level = 1;            // out of order on level 1
  kissat_chb_assign (solver, false);
  assert (lrb->count.opened == 3);
  kissat_backtrack_without_updating_phases (solver, 1);
  assert (!VALUE (LIT (6)) && VALUE (LIT (7)));
  assert (solver->assigned[7].trail == 1);
  assert (lrb->count.skipped == 1);
  assert (!lrb->start[7]);
  solver->estimator.chb.conflicts = 2;
  participate (solver, 7);
  kissat_chb_assign (solver, false);
  assert (lrb->count.opened == 3);
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (kissat_get_score (solver, 7) ==
          erwa (0, kissat_chb_alpha (2), 0.5));
  assert (kissat_get_score (solver, 5) == 0);
  assert (lrb->count.updates == 2 && lrb->count.skipped == 1);
  check_fresh_tree (solver);
  kissat_release (solver);
}

// Focused mode does not walk: a literal it assigned and that is still
// assigned when stable mode is entered has no interval, so its close at a
// stable-mode backtrack pays nothing, whatever it took part in.  Neither
// do warm-up's literals, which its own propagation assigns.

static void test_lrb_earning_nothing (void) {
  kissat *solver = new_solver (0, 0);
  const lrb *lrb = &solver->policy.lrb;
  solver->stable = false;
  kissat_internal_assume (solver, LIT (0));
  assert (!kissat_search_propagate (solver));
  assert (VALUE (LIT (1)) > 0);
  solver->stable = true;
  kissat_update_scores (solver);
  assert (!lrb->count.opened);
  solver->estimator.chb.conflicts = 1;
  participate (solver, 0);
  participate (solver, 1);
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (lrb->count.ignored == 2);
  assert (!lrb->count.updates && !lrb->count.skipped);
  assert (!kissat_get_score (solver, 0) && !kissat_get_score (solver, 1));
  kissat_release (solver);
  solver = new_solver (0, 0);
  lrb = &solver->policy.lrb;
  kissat_warmup (solver);
  assert (!solver->level);
  assert (!lrb->count.opened);
  assert (lrb->count.ignored == 9);
  assert (!lrb->count.updates && !lrb->count.skipped);
  for (all_variables (idx))
    assert (!kissat_get_score (solver, idx));
  kissat_release (solver);
}

// Leaving stable mode closes the open intervals of the variables still
// assigned, whose leaves lag until entering stable mode rebuilds the tree.

static void test_lrb_modes (void) {
  kissat *solver = new_solver (0, 0);
  const lrb *const lrb = &solver->policy.lrb;
  const tree *const tree = &solver->policy.tree;
  kissat_internal_assume (solver, LIT (5));
  assert (!kissat_search_propagate (solver));
  solver->estimator.chb.conflicts = 1;
  participate (solver, 5);
  kissat_leave_stable_intervals (solver);
  assert (lrb->count.closed[INTERVALS_CLOSE_LEFT] == 1);
  assert (lrb->start[5] == LRB_CLOSED);
  const double paid = erwa (0, kissat_chb_alpha (1), 1);
  assert (kissat_get_score (solver, 5) == paid);
  assert (kissat_tree_key (tree, 5) == 0);
  solver->stable = false;
  kissat_backtrack_without_updating_phases (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  check_fresh_tree (solver);
  kissat_release (solver);
}

#endif

void tissat_schedule_lrb (void) {
#if !defined(HEAPARGMAX) && !defined(NOPTIONS)
  SCHEDULE_FUNCTION (test_lrb_options);
  SCHEDULE_FUNCTION (test_lrb_start);
  SCHEDULE_FUNCTION (test_lrb_conflict);
  SCHEDULE_FUNCTION (test_lrb_no_reasons);
  SCHEDULE_FUNCTION (test_lrb_strengthened);
  SCHEDULE_FUNCTION (test_lrb_alpha);
  SCHEDULE_FUNCTION (test_lrb_kept);
  SCHEDULE_FUNCTION (test_lrb_earning_nothing);
  SCHEDULE_FUNCTION (test_lrb_modes);
#endif
}
