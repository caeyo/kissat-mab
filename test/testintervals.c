#include "../src/analyze.h"
#include "../src/backtrack.h"
#include "../src/decide.h"
#include "../src/inlinepolicy.h"
#include "../src/propsearch.h"

#include "test.h"

#include <math.h>

#if !defined(HEAPARGMAX) && !defined(NOPTIONS)

// The assignment intervals (see 'intervals.h'): who starts them, the class
// of an interval from the reason and the mark of an asserted literal, the
// class of a deferred interval kept apart from that of a new assignment,
// the interval a bump falls in, and the marks across mode switches.

static kissat *new_solver (const char *name, int value, const char *other,
                           int other_value) {
  kissat *solver = kissat_init ();
#ifndef NDEBUG
  kissat_set_option (solver, "check", 0);
#endif
  if (name)
    kissat_set_option (solver, name, value);
  if (other)
    kissat_set_option (solver, other, other_value);
  // Variables 1 to 7 in the order of their indices: deciding 1 and 2 is a
  // conflict on 3, which learns (-1 -2), and deciding 4, 5 and 6 one on 7,
  // which learns (-4 -5 -6), without on-the-fly strengthening.
  const int clauses[][5] = {{-1, -2, 3, 0},
                            {-1, -2, -3, 0},
                            {-4, -5, -6, 7, 0},
                            {-4, -5, -6, -7, 0}};
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

static unsigned class_of (kissat *solver, unsigned idx) {
  const unsigned state = solver->policy.intervals.state[idx];
  assert (state & INTERVALS_OPEN);
  return state & INTERVALS_CLASS;
}

// UCB on VSIDS scores starts the intervals, counting LRB's interval unless
// 'ucbinterval=0'; feedback builds start them whatever the policy, on the
// VSIDS line with the increments and rounds at assignment, on the CHB line
// without.  Otherwise nothing is started.

static void test_intervals_start (void) {
#ifdef FEEDBACK
  const bool feedback = true;
#else
  const bool feedback = false;
#endif
  kissat *solver = new_solver (0, 0, 0, 0);
  const intervals *intervals = &solver->policy.intervals;
  assert (intervals->started == feedback);
  assert (!intervals->ucb);
  if (feedback) {
    assert (intervals->interval && intervals->vsids);
    assert (intervals->rounds);
    assert (intervals->opened && intervals->start && intervals->bumps);
  } else
    assert (!intervals->state && !intervals->interval);
  kissat_release (solver);
  solver = new_solver ("ucb", 1, 0, 0);
  intervals = &solver->policy.intervals;
  assert (intervals->started && intervals->ucb && intervals->interval);
  assert (intervals->vsids && intervals->opened);
  assert (intervals->rounds == feedback);
  kissat_release (solver);
#ifndef FEEDBACK
  solver = new_solver ("ucb", 1, "ucbinterval", 0);
  intervals = &solver->policy.intervals;
  assert (intervals->started && intervals->ucb && !intervals->interval);
  kissat_release (solver);
#endif
  solver = new_solver ("ucb", 1, "chb", 1);
  intervals = &solver->policy.intervals;
  assert (intervals->started == feedback);
  assert (!intervals->ucb && !intervals->vsids && !intervals->opened);
  assert (!intervals->rounds);
  kissat_release (solver);
  solver = new_solver ("thompson", 1, 0, 0);
  assert (solver->policy.intervals.started == feedback);
  kissat_release (solver);
}

// Through the solver's own propagation and analysis, under UCB at c = 0,
// which decides as Argmax and counts the intervals, without on-the-fly
// strengthening: deciding 1 and then 2 propagates 3 and falsifies a
// clause.  The record before the analysis's backjump opens the intervals
// of the decisions and of 3 as decided and propagated; the backjump ends
// those of 2 and 3, which wait for the bump round, 2 keeping its class
// while it is asserted again, now negative, with the learned binary clause
// (-1 -2) as its reason ('learn_binary'); after the round both close and
// 2's new interval opens as asserted.  Then the same with a learned clause
// of three literals ('learn_reference'), asserting -6 at level 2.

static void test_intervals_classes (void) {
  kissat *solver = new_solver ("ucb", 1, "otfs", 0);
  const intervals *const intervals = &solver->policy.intervals;
  const keys *const keys = &solver->policy.keys;
  kissat_internal_assume (solver, LIT (0));
  assert (!kissat_search_propagate (solver));
  kissat_internal_assume (solver, LIT (1));
  clause *conflict = kissat_search_propagate (solver);
  assert (conflict);
  assert (VALUE (LIT (2)));
  kissat_record_intervals (solver);
  assert (class_of (solver, 0) == INTERVALS_DECIDED);
  assert (class_of (solver, 1) == INTERVALS_DECIDED);
  assert (class_of (solver, 2) == INTERVALS_PROPAGATED);
  const double inc = solver->scinc;
  const uint64_t rounds = solver->estimator.rounds;
  kissat_analyze (solver, conflict);
  assert (solver->estimator.rounds == rounds + 1);
  assert (solver->level == 1);
  assert (VALUE (LIT (1)) < 0);
  assert (solver->assigned[1].binary);
  assert (!intervals->analyzing && !intervals->deferring);
  assert (class_of (solver, 0) == INTERVALS_DECIDED);
  assert (class_of (solver, 1) == INTERVALS_ASSERTED);
  assert (intervals->state[1] & INTERVALS_MARKED);
  assert (!VALUE (LIT (2)) && !intervals->state[2]);
  // The ended intervals counted the round, of the increment before it.
  assert (fabs (keys->count[1] - inc) <= 1e-12 * inc);
  assert (fabs (keys->count[2] - inc) <= 1e-12 * inc);
  assert (!keys->count[0]);
  // A restart closes both open intervals, and the marks go with them.
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (!intervals->state[0] && !intervals->state[1]);
  for (unsigned idx = 3; idx < 6; idx++) {
    kissat_internal_assume (solver, LIT (idx));
    conflict = kissat_search_propagate (solver);
    assert (!conflict == (idx < 5));
  }
  kissat_analyze (solver, conflict);
  assert (solver->level == 2);
  assert (VALUE (LIT (5)) < 0);
  assert (!solver->assigned[5].binary);
  assert (class_of (solver, 5) == INTERVALS_ASSERTED);
  assert (class_of (solver, 3) == INTERVALS_DECIDED);
  assert (class_of (solver, 4) == INTERVALS_DECIDED);
  assert (!intervals->state[6]);
  kissat_release (solver);
}

// A conflict that Kissat reuses as the driving clause without analysis:
// with 1, 2 and 4 decided, the binary clause (-1 -2) falsified has one
// literal on its conflict level, 2, below the current level, so the
// analysis backtracks to level 1 and assigns -2 with the conflict as its
// reason.  No round: the ended intervals close at the step's end, and the
// asserted literal's opens at the next record.

static void test_intervals_reused_conflict (void) {
  kissat *solver = new_solver ("ucb", 1, 0, 0);
  const intervals *const intervals = &solver->policy.intervals;
  kissat_internal_assume (solver, LIT (0));
  kissat_internal_assume (solver, LIT (1));
  kissat_internal_assume (solver, LIT (3));
  clause *const conflict =
      kissat_binary_conflict (solver, NOT (LIT (0)), NOT (LIT (1)));
  const uint64_t rounds = solver->estimator.rounds;
  kissat_analyze (solver, conflict);
  assert (solver->estimator.rounds == rounds);
  assert (solver->level == 1);
  assert (VALUE (LIT (1)) < 0);
  assert (!VALUE (LIT (3)));
  assert (intervals->state[1] == INTERVALS_MARKED);
  assert (!intervals->state[3]);
  kissat_record_intervals (solver);
  assert (class_of (solver, 1) == INTERVALS_ASSERTED);
  assert (class_of (solver, 0) == INTERVALS_DECIDED);
  kissat_release (solver);
}

// An implied assignment at the current level, with a reason other than
// 'DECISION_REASON', counted in its level's frame in feedback builds, as
// 'kissat_assign' counts it; asserted if 'asserted' (see 'learn.c').

static void imply (kissat *solver, unsigned idx, bool asserted) {
  const unsigned lit = LIT (idx);
  assert (!VALUE (lit));
  solver->values[lit] = 1;
  solver->values[NOT (lit)] = -1;
  assert (solver->unassigned);
  solver->unassigned--;
  assigned *const a = solver->assigned + idx;
  a->level = solver->level;
  a->trail = SIZE_ARRAY (solver->trail);
  a->binary = false;
  a->reason = 0;
  PUSH_ARRAY (solver->trail, lit);
#ifdef FEEDBACK
  FRAME (solver->level).assigned++;
#endif
  if (asserted)
    kissat_policy_asserted (solver, lit);
}

// A step by hand: its backtrack ends a decided, an asserted and a
// propagated interval, the decided variable is asserted again, keeping the
// class of its ended interval apart; a bump of the step falls in the ended
// interval of its variable, or in the open one of an assigned variable, or
// in none for a variable never assigned.  After the round the ended
// intervals close and the new one opens as asserted.  In feedback builds
// the intervals count their bumped rounds, which the brute force of
// assertion builds checks at every close, so there the bumps are made by
// the round only.

static void test_intervals_deferred (void) {
  kissat *solver = new_solver ("ucb", 1, 0, 0);
  const intervals *const intervals = &solver->policy.intervals;
  kissat_internal_assume (solver, LIT (0));
  kissat_internal_assume (solver, LIT (1));
  imply (solver, 2, true);
  imply (solver, 3, false);
  kissat_record_intervals (solver);
  assert (class_of (solver, 2) == INTERVALS_ASSERTED);
  assert (class_of (solver, 3) == INTERVALS_PROPAGATED);
  kissat_policy_begin_analysis (solver);
  kissat_backtrack_without_updating_phases (solver, 1);
  assert (intervals->deferring);
  assert (SIZE_STACK (intervals->deferred) == 3);
  const unsigned deferred[3] = {1, 2, 3};
  const unsigned classes[3] = {INTERVALS_DECIDED, INTERVALS_ASSERTED,
                               INTERVALS_PROPAGATED};
  for (unsigned i = 0; i < 3; i++)
    assert (intervals->state[deferred[i]] ==
            (INTERVALS_DEFERRED | classes[i] << INTERVALS_DEFERRED_SHIFT));
  imply (solver, 1, true);
  assert (intervals->state[1] ==
          (INTERVALS_DEFERRED | INTERVALS_MARKED |
           INTERVALS_DECIDED << INTERVALS_DEFERRED_SHIFT));
#ifndef FEEDBACK
  assert (!intervals->rounds);
  assert (kissat_interval_bumped (solver, 1) ==
          (INTERVALS_ENDED | INTERVALS_DECIDED));
  assert (kissat_interval_bumped (solver, 2) ==
          (INTERVALS_ENDED | INTERVALS_ASSERTED));
  assert (kissat_interval_bumped (solver, 3) ==
          (INTERVALS_ENDED | INTERVALS_PROPAGATED));
  assert (kissat_interval_bumped (solver, 0) == INTERVALS_DECIDED);
  assert (kissat_interval_bumped (solver, 4) == INTERVALS_NONE);
#endif
  const unsigned bumped[4] = {1, 2, 0, 4};
  for (unsigned i = 0; i < 4; i++)
    PUSH_STACK (solver->analyzed, bumped[i]);
  kissat_bump_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
  kissat_policy_end_analysis (solver);
  assert (!intervals->deferring && EMPTY_STACK (intervals->deferred));
  assert (class_of (solver, 1) == INTERVALS_ASSERTED);
  assert (!intervals->state[2] && !intervals->state[3]);
#ifdef FEEDBACK
  // The open interval of 0 was bumped in the round; the new one of 1
  // starts after it.  The ended ones counted their bumps in the round.
  assert (intervals->bumps[0] == 1 && !intervals->bumps[1]);
  assert (intervals->start[1] == solver->estimator.rounds);
  const feedback *const fb = &solver->policy.feedback;
  assert (fb->m1.intervals[FEEDBACK_DEC] == 1); // 1's, decided
  assert (fb->m1.intervals[FEEDBACK_IMP] == 2); // 2's and 3's
  assert (fb->m1.bumps[1][FEEDBACK_DEC] == 1);
  assert (fb->m1.bumps[1][FEEDBACK_IMP] == 1);
  assert (fb->m1.bumps[0][FEEDBACK_DEC] == 1);
  assert (fb->m1.unobserved == 1);
#else
  assert (kissat_interval_bumped (solver, 1) == INTERVALS_ASSERTED);
#endif
  kissat_release (solver);
}

// Marks across mode switches: leaving stable mode closes every open
// interval and clears the marks, so the asserted literal still assigned
// when stable mode is entered again counts as propagated; focused mode
// marks nothing.

static void test_intervals_modes (void) {
  kissat *solver = new_solver ("ucb", 1, 0, 0);
  const intervals *const intervals = &solver->policy.intervals;
  kissat_internal_assume (solver, LIT (0));
  imply (solver, 1, true);
  kissat_record_intervals (solver);
  assert (class_of (solver, 1) == INTERVALS_ASSERTED);
  kissat_leave_stable_intervals (solver);
  assert (!intervals->state[0] && !intervals->state[1]);
  solver->stable = false;
  imply (solver, 2, true);
  assert (!intervals->state[2]);
  solver->stable = true;
  kissat_update_scores (solver);
  assert (!intervals->counted);
  kissat_record_intervals (solver);
  assert (class_of (solver, 0) == INTERVALS_DECIDED);
  assert (class_of (solver, 1) == INTERVALS_PROPAGATED);
  assert (class_of (solver, 2) == INTERVALS_PROPAGATED);
  kissat_release (solver);
}

#endif

void tissat_schedule_intervals (void) {
#if !defined(HEAPARGMAX) && !defined(NOPTIONS)
  SCHEDULE_FUNCTION (test_intervals_start);
  SCHEDULE_FUNCTION (test_intervals_classes);
  SCHEDULE_FUNCTION (test_intervals_reused_conflict);
  SCHEDULE_FUNCTION (test_intervals_deferred);
  SCHEDULE_FUNCTION (test_intervals_modes);
#endif
}
