#include "../src/analyze.h"
#include "../src/backtrack.h"
#include "../src/bump.h"
#include "../src/chb.h"
#include "../src/collect.h"
#include "../src/decide.h"
#include "../src/inlinepolicy.h"
#include "../src/propsearch.h"

#include "test.h"

#include <math.h>

#if defined(FEEDBACK) && !defined(NOPTIONS)

// Feedback builds' measurements (see 'feedback.h') against values computed
// here from the same steps: assignments as decisions (picked or assumed)
// and as implications, bump rounds and payments, backtracks, rescales,
// leaving and entering stable mode, and compaction.

#define TEST_VARS 8

static kissat *new_solver (unsigned vars, const char *name, int value,
                           const char *other, int other_value) {
  kissat *solver = kissat_init ();
  if (name)
    kissat_set_option (solver, name, value);
  if (other)
    kissat_set_option (solver, other, other_value);
  for (unsigned i = 1; i <= vars; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  return solver;
}

static bool near (double a, double b) {
  return fabs (a - b) <= 1e-12 * fmax (fabs (a), fabs (b));
}

// An implied assignment at the current level: a reason that is not
// 'DECISION_REASON', on the trail, counted in the level's frame as
// 'kissat_assign' counts it.

static void imply (kissat *solver, unsigned idx) {
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
  FRAME (solver->level).assigned++;
}

static unsigned class_of (kissat *solver, unsigned idx) {
  return solver->assigned[idx].reason == DECISION_REASON ? FEEDBACK_DEC
                                                         : FEEDBACK_IMP;
}

// What the VSIDS line's sums must be: the rounds of the open intervals,
// the rounds of the closed ones and the bumps by class, the bumps in no
// interval, and inside an analysis step the variables assigned when it
// started and the intervals its backtracks ended, with their classes.

typedef struct expected expected;

struct expected {
  double open[TEST_VARS];
  double n[2][TEST_VARS], r[2][TEST_VARS];
  uint64_t bumps[2][2], unobserved;
  bool analyzing, listed[TEST_VARS];
  unsigned deferred[TEST_VARS]; // class + 1 of an ended interval, or 0
};

static void close_expected (expected *e, unsigned idx, unsigned c) {
  e->n[c][idx] += e->open[idx];
  e->open[idx] = 0;
}

static void finish_expected (expected *e) {
  for (unsigned idx = 0; idx < TEST_VARS; idx++)
    if (e->deferred[idx]) {
      close_expected (e, idx, e->deferred[idx] - 1);
      e->deferred[idx] = 0;
    }
}

// A step of conflict analysis, as 'kissat_analyze' brackets each of its
// rounds: its bump round observes the variables assigned when it started.

static void begin_step (kissat *solver, expected *e) {
  e->analyzing = true;
  memset (e->listed, 0, sizeof e->listed);
  for (all_stack (unsigned, lit, solver->trail))
    if (ACTIVE (IDX (lit)))
      e->listed[IDX (lit)] = true;
  kissat_policy_begin_analysis (solver);
}

static void end_step (kissat *solver, expected *e) {
  kissat_policy_end_analysis (solver);
  finish_expected (e);
  e->analyzing = false;
}

// A bump round in which the variables 'bumped' are analyzed: every variable
// it observes counts the round's increment (inside a step those listed at
// its start, else those on the trail), and every bumped one the increment
// in the class of the interval it falls in: the one a backtrack of the
// step ended, or the open one of an assigned variable.  Inside a step the
// ended intervals close after it.

static void bump_round (kissat *solver, expected *e, const unsigned *bumped,
                        unsigned size) {
  const double inc = solver->scinc;
  if (e->analyzing) {
    for (unsigned idx = 0; idx < TEST_VARS; idx++)
      if (e->listed[idx])
        e->open[idx] += inc;
  } else
    for (all_stack (unsigned, lit, solver->trail))
      if (ACTIVE (IDX (lit)))
        e->open[IDX (lit)] += inc;
  for (unsigned i = 0; i < size; i++) {
    const unsigned idx = bumped[i];
    if (e->deferred[idx]) {
      const unsigned c = e->deferred[idx] - 1;
      e->r[c][idx] += inc;
      e->bumps[1][c]++;
    } else if (VALUE (LIT (idx))) {
      const unsigned c = class_of (solver, idx);
      e->r[c][idx] += inc;
      e->bumps[0][c]++;
    } else
      e->unobserved++;
    PUSH_STACK (solver->analyzed, idx);
  }
  kissat_bump_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
  if (e->analyzing) {
    finish_expected (e);
    memset (e->listed, 0, sizeof e->listed);
  }
}

// A backtrack closes the intervals it ends, or inside a step defers them.

static void backtrack (kissat *solver, expected *e, unsigned level) {
  for (all_stack (unsigned, lit, solver->trail))
    if (LEVEL (lit) > level) {
      const unsigned idx = IDX (lit), c = class_of (solver, idx);
      if (e->analyzing)
        e->deferred[idx] = c + 1;
      else
        close_expected (e, idx, c);
    }
  kissat_backtrack_without_updating_phases (solver, level);
}

static void check_sums (kissat *solver, const expected *e, unsigned vars) {
  const feedback *const fb = &solver->policy.feedback;
  for (unsigned c = 0; c < 2; c++) {
    for (unsigned idx = 0; idx < vars; idx++) {
      assert (near (fb->n[c][idx], e->n[c][idx]));
      assert (near (fb->r[c][idx], e->r[c][idx]));
    }
    for (unsigned ended = 0; ended < 2; ended++)
      assert (fb->m1.bumps[ended][c] == e->bumps[ended][c]);
  }
  assert (fb->m1.unobserved == e->unobserved);
}

// The counts by class and the bumps by class against the steps, outside
// analysis steps: variables bumped after a backtrack unassigned them, which
// fall in no interval, an interval without bump rounds, a rescale inside
// intervals, and leaving and entering stable mode.  The sum of the classes
// is UCB's count, which outside steps is the same with either count.

static void test_feedback_vsids_sums (void) {
  kissat *solver = new_solver (TEST_VARS, "ucb", 1, "ucbc", 0);
  const feedback *const fb = &solver->policy.feedback;
  assert (fb->started), assert (!fb->chb);
  assert (fb->size == solver->size);
  expected e;
  memset (&e, 0, sizeof e);
  kissat_internal_assume (solver, LIT (1));
  imply (solver, 2);
  bump_round (solver, &e, (unsigned[]){1, 2}, 2);
  kissat_internal_assume (solver, LIT (3));
  imply (solver, 4);
  bump_round (solver, &e, (unsigned[]){3, 5}, 2);
  backtrack (solver, &e, 1);
  check_sums (solver, &e, TEST_VARS);
  // Variables 3 and 4 are unassigned now, outside a step: their bumps fall
  // in no interval, as 5's did.
  bump_round (solver, &e, (unsigned[]){3, 4, 1}, 3);
  check_sums (solver, &e, TEST_VARS);
  assert (e.unobserved == 3);
  // A rescale, here forced, inside the intervals of 1 and 2.
  const double inc = solver->scinc;
  kissat_rescale_scores (solver);
  const double factor = solver->scinc / inc;
  assert (factor < 1);
  for (unsigned idx = 0; idx < TEST_VARS; idx++) {
    e.open[idx] *= factor;
    for (unsigned c = 0; c < 2; c++)
      e.n[c][idx] *= factor, e.r[c][idx] *= factor;
  }
  check_sums (solver, &e, TEST_VARS);
  bump_round (solver, &e, (unsigned[]){2}, 1);
  // An interval without a bump round adds nothing.
  imply (solver, 6);
  backtrack (solver, &e, 0);
  check_sums (solver, &e, TEST_VARS);
  assert (fb->m1.intervals[FEEDBACK_DEC] == 2);
  assert (fb->m1.intervals[FEEDBACK_IMP] == 3);
  // Leaving stable mode closes the open intervals, entering it opens one
  // for every assigned variable at the next record.
  kissat_internal_assume (solver, LIT (0));
  imply (solver, 7);
  bump_round (solver, &e, (unsigned[]){0, 7}, 2);
  kissat_leave_stable_intervals (solver);
  close_expected (&e, 0, FEEDBACK_DEC), close_expected (&e, 7, FEEDBACK_IMP);
  check_sums (solver, &e, TEST_VARS);
  solver->stable = false;
  imply (solver, 5);
  solver->stable = true;
  kissat_update_scores (solver);
  bump_round (solver, &e, (unsigned[]){5}, 1);
  bump_round (solver, &e, (unsigned[]){0}, 1);
  backtrack (solver, &e, 0);
  check_sums (solver, &e, TEST_VARS);
  // UCB's count is the sum of the classes.
  const keys *const keys = &solver->policy.keys;
  for (unsigned idx = 0; idx < TEST_VARS; idx++)
    assert (near (keys->count[idx], fb->n[0][idx] + fb->n[1][idx]));
  kissat_release (solver);
}

// The policy's search picks: M1's events with their frozen predictors and
// errors, and M2's outcomes by kind, age and count.  Variable 5 has the
// largest score, so Argmax picks it.

static double round_error (double p, uint64_t k, uint64_t b) {
  return b * (1 - p) * (1 - p) + (k - b) * p * p;
}

static double interval_error (double p, uint64_t k, uint64_t b) {
  const double error = (double) b / k - p;
  return error * error;
}

static void test_feedback_vsids_events (void) {
  kissat *solver = new_solver (6, 0, 0, 0, 0);
  const feedback *const fb = &solver->policy.feedback;
  for (unsigned idx = 0; idx < 6; idx++)
    kissat_update_score (solver, idx, idx < 5 ? idx + 1 : 100);
  // A first pick of 5: no predictor is defined, nor p_const.  Its interval
  // spans two rounds and is bumped in the first.
  kissat_decide (solver);
  assert (IDX (PEEK_ARRAY (solver->trail, 0)) == 5);
  assert (fb->state[5] & FEEDBACK_PENDING);
  const double inc_a = solver->scinc;
  expected e;
  memset (&e, 0, sizeof e);
  bump_round (solver, &e, (unsigned[]){5}, 1);
  const double inc_b = solver->scinc;
  bump_round (solver, &e, (unsigned[]){0}, 1);
  backtrack (solver, &e, 0);
  const feedback_sums *const no_const =
      fb->m1.group + FEEDBACK_GROUP_NO_CONST;
  assert (no_const->n == 1 && no_const->k == 2 && no_const->b == 1);
  assert (fb->m1.events == 1);
  const feedback_sums *const never =
      &fb->m2.age[FEEDBACK_POLICY][FEEDBACK_AGE_NEVER];
  assert (never->n == 1 && never->k == 2 && never->b == 1);
  assert (never->bumped == 1);
  assert (fb->m2.count[FEEDBACK_POLICY][FEEDBACK_COUNT_ZERO].n == 1);
  assert (fb->last[5] == 2);
  // An assumed decision, not a pick, under which 5 is implied for three
  // rounds, bumped in the first and the third.  The decided interval of 0
  // adds to the sums of p_const.
  kissat_internal_assume (solver, LIT (0));
  imply (solver, 5);
  const double inc_c = solver->scinc;
  bump_round (solver, &e, (unsigned[]){5}, 1);
  const double inc_d = solver->scinc;
  bump_round (solver, &e, (unsigned[]){1}, 1);
  const double inc_e = solver->scinc;
  bump_round (solver, &e, (unsigned[]){5}, 1);
  backtrack (solver, &e, 0);
  assert (fb->m1.events == 1);
  assert (fb->m1.sum_k == 5 && fb->m1.sum_b == 1);
  // The second pick of 5 has every predictor, and its variable was last
  // observed in the current round.
  kissat_decide (solver);
  assert (IDX (PEEK_ARRAY (solver->trail, 0)) == 5);
  const double p_dec = inc_a / (inc_a + inc_b);
  const double p_imp = (inc_c + inc_e) / (inc_c + inc_d + inc_e);
  const double p_all =
      (inc_a + inc_c + inc_e) / (inc_a + inc_b + inc_c + inc_d + inc_e);
  const double p_const = 1.0 / 5;
  const double *const frozen = fb->frozen + FEEDBACK_PREDICTORS * 5;
  assert (near (frozen[FEEDBACK_PREDICT_DEC], p_dec));
  assert (near (frozen[FEEDBACK_PREDICT_IMP], p_imp));
  assert (near (frozen[FEEDBACK_PREDICT_ALL], p_all));
  assert (near (frozen[FEEDBACK_PREDICT_CONST], p_const));
  const double count =
      (inc_a + inc_b + inc_c + inc_d + inc_e) / solver->scinc;
  assert (1 <= count && count < 5);
  for (unsigned round = 0; round < 4; round++)
    bump_round (solver, &e, (unsigned[]){round == 1 ? 5 : 2}, 1);
  backtrack (solver, &e, 0);
  const feedback_sums *const both = fb->m1.group + FEEDBACK_GROUP_BOTH;
  assert (both->n == 1 && both->k == 4 && both->b == 1);
  const double p[4] = {p_dec, p_imp, p_all, p_const};
  for (unsigned i = 0; i < 4; i++) {
    assert (near (both->round[i], round_error (p[i], 4, 1)));
    assert (near (both->interval[i], interval_error (p[i], 4, 1)));
  }
  const unsigned bin_dec = (unsigned) (10 * p_dec);
  const unsigned bin_imp = (unsigned) (10 * p_imp);
  assert (fb->m1.calibration[0][bin_dec].n == 1);
  assert (fb->m1.calibration[0][bin_dec].k == 4);
  assert (fb->m1.calibration[1][bin_imp].b == 1);
  const feedback_sums *const recent =
      &fb->m2.age[FEEDBACK_POLICY][FEEDBACK_AGE_RECENT];
  assert (recent->n == 1 && recent->k == 4 && recent->b == 1);
  assert (fb->m2.count[FEEDBACK_POLICY][FEEDBACK_COUNT_BELOW5].n == 1);
  // A pick undone before any bump round is an event with k = 0, and the
  // last pick is open at the end.
  kissat_decide (solver);
  backtrack (solver, &e, 0);
  assert (fb->m1.events == 3 && fb->m1.zero == 1);
  kissat_decide (solver);
  assert (fb->m2.picks[FEEDBACK_POLICY] == 4);
  assert (fb->state[5] & FEEDBACK_PENDING);
  uint64_t outcomes = 0;
  for (unsigned i = 0; i < FEEDBACK_AGES; i++)
    outcomes += fb->m2.age[FEEDBACK_POLICY][i].n;
  assert (outcomes == 3);
  check_sums (solver, &e, 6);
  kissat_release (solver);
  // With gamma one every pick is uniform.
  solver = new_solver (6, "gammappm", 1000000, 0, 0);
  kissat_decide (solver);
  const unsigned idx = IDX (PEEK_ARRAY (solver->trail, 0));
  assert (solver->policy.feedback.state[idx] & FEEDBACK_PENDING);
  kissat_backtrack_without_updating_phases (solver, 0);
  const feedback *const mixed = &solver->policy.feedback;
  assert (mixed->m2.picks[FEEDBACK_UNIFORM] == 1);
  assert (!mixed->m2.picks[FEEDBACK_POLICY]);
  assert (mixed->m2.age[FEEDBACK_UNIFORM][FEEDBACK_AGE_NEVER].n == 1);
  kissat_release (solver);
}

// LRB's interval: inside an analysis step, the intervals the backtrack ends
// count the step's bump round and take its bumps of their variables, the
// re-asserted literal's bump going to its old, decided interval; the
// literal assigned after the backtrack opens its interval after the round;
// a step without a bump round closes its intervals without one.  The pick's
// event and outcome close with them.  UCB counting LRB's interval keeps the
// same counts.

static void test_feedback_vsids_steps (void) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, "ucb", 1);
  kissat_set_option (solver, "ucbinterval", 1);
  for (unsigned i = 1; i <= 6; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  const feedback *const fb = &solver->policy.feedback;
  const intervals *const intervals = &solver->policy.intervals;
  kissat_update_score (solver, 5, 1e100);
  expected e;
  memset (&e, 0, sizeof e);
  kissat_decide (solver);
  assert (IDX (PEEK_ARRAY (solver->trail, 0)) == 5);
  imply (solver, 2);
  kissat_internal_assume (solver, LIT (3));
  imply (solver, 4);
  bump_round (solver, &e, (unsigned[]){5}, 1);
  // A step: the backtrack ends the intervals of 3 (decided) and 4
  // (implied), 3 is asserted again, now implied, and the round bumps 3, 4
  // and 5.
  begin_step (solver, &e);
  backtrack (solver, &e, 1);
  assert (intervals->deferring);
  assert (SIZE_STACK (intervals->deferred) == 2);
  imply (solver, 3);
  bump_round (solver, &e, (unsigned[]){3, 4, 5}, 3);
  assert (!intervals->deferring);
  end_step (solver, &e);
  assert (e.bumps[1][FEEDBACK_DEC] == 1 && e.bumps[1][FEEDBACK_IMP] == 1);
  assert (fb->m1.intervals[FEEDBACK_DEC] == 1);
  assert (fb->m1.intervals[FEEDBACK_IMP] == 1);
  assert (intervals->state[3] & INTERVALS_OPEN);
  assert (intervals->start[3] == solver->estimator.rounds);
  check_sums (solver, &e, 6);
  // A round outside steps, then a step without a round: its backtrack
  // closes 5's interval (the pick's) and the others without a round.
  bump_round (solver, &e, (unsigned[]){2}, 1);
  begin_step (solver, &e);
  backtrack (solver, &e, 0);
  kissat_internal_assume (solver, LIT (1));
  end_step (solver, &e);
  check_sums (solver, &e, 6);
  assert (!fb->m1.unobserved);
  const feedback_sums *const no_const =
      fb->m1.group + FEEDBACK_GROUP_NO_CONST;
  assert (fb->m1.events == 1);
  assert (no_const->n == 1 && no_const->k == 3 && no_const->b == 2);
  const feedback_sums *const never =
      &fb->m2.age[FEEDBACK_POLICY][FEEDBACK_AGE_NEVER];
  assert (never->n == 1 && never->k == 3 && never->b == 2);
  // UCB counting LRB's interval has the classes' sums.
  const keys *const keys = &solver->policy.keys;
  for (unsigned idx = 0; idx < 6; idx++)
    assert (near (keys->count[idx], fb->n[0][idx] + fb->n[1][idx]));
  kissat_release (solver);
}

// Ages: bump rounds since the close of the variable's last interval with
// a round, binned below W, from W to 10 W, and from 10 W.

static void test_feedback_vsids_ages (void) {
  kissat *solver = new_solver (4, 0, 0, 0, 0);
  const feedback *const fb = &solver->policy.feedback;
  kissat_update_score (solver, 3, 1e100); // above every bumped score
  expected e;
  memset (&e, 0, sizeof e);
  kissat_internal_assume (solver, LIT (3));
  bump_round (solver, &e, (unsigned[]){0}, 1);
  backtrack (solver, &e, 0);
  const unsigned ages[3] = {FEEDBACK_WINDOW - 1, 10 * FEEDBACK_WINDOW - 1,
                            10 * FEEDBACK_WINDOW};
  const unsigned bins[3] = {FEEDBACK_AGE_RECENT, FEEDBACK_AGE_STALE,
                            FEEDBACK_AGE_OLD};
  uint64_t done = 0;
  for (unsigned i = 0; i < 3; i++) {
    kissat_internal_assume (solver, LIT (0));
    while (done < ages[i]) {
      bump_round (solver, &e, (unsigned[]){0}, 1);
      done++;
    }
    backtrack (solver, &e, 0);
    assert (solver->estimator.rounds - fb->last[3] == ages[i]);
    kissat_decide (solver);
    assert (IDX (PEEK_ARRAY (solver->trail, 0)) == 3);
    assert (((fb->state[3] >> FEEDBACK_AGE_SHIFT) & 3) == bins[i]);
    bump_round (solver, &e, (unsigned[]){0}, 1);
    backtrack (solver, &e, 0);
    done = 0;
  }
  check_sums (solver, &e, 4);
  kissat_release (solver);
}

// Compaction with a pending pick and implied variables: sums, intervals
// and the pick move with their variables, so the event closes with the
// rounds spent before it.  Variable 1 is eliminated, so 2 to 7 move down.

static void test_feedback_compact (void) {
  kissat *solver = kissat_init ();
#ifndef NDEBUG
  kissat_set_option (solver, "check", 0);
#endif
  for (unsigned i = 1; i <= TEST_VARS; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  const feedback *const fb = &solver->policy.feedback;
  kissat_update_score (solver, 5, 100);
  kissat_decide (solver);
  assert (IDX (PEEK_ARRAY (solver->trail, 0)) == 5);
  imply (solver, 3);
  expected e;
  memset (&e, 0, sizeof e);
  bump_round (solver, &e, (unsigned[]){5, 3}, 2);
  bump_round (solver, &e, (unsigned[]){3}, 1);
  for (all_clauses (c))
    kissat_mark_clause_as_garbage (solver, c);
  kissat_mark_eliminated_variable (solver, 1);
  kissat_sparse_collect (solver, true, 0);
  assert (VARS == 7);
  for (unsigned idx = 1; idx + 1 < 8; idx++) {
    e.open[idx] = e.open[idx + 1];
    for (unsigned c = 0; c < 2; c++)
      e.n[c][idx] = e.n[c][idx + 1], e.r[c][idx] = e.r[c][idx + 1];
  }
  assert (fb->state[4] & FEEDBACK_PENDING);
  assert (VALUE (LIT (4)) && VALUE (LIT (2)));
  bump_round (solver, &e, (unsigned[]){4}, 1);
  backtrack (solver, &e, 0);
  check_sums (solver, &e, 7);
  const feedback_sums *const no_const =
      fb->m1.group + FEEDBACK_GROUP_NO_CONST;
  assert (no_const->n == 1 && no_const->k == 3 && no_const->b == 2);
  kissat_release (solver);
}

// The CHB line: per class the ERWA from zero and the payments, UCB's count
// with its increment, and M1's events, the payments of decided variables,
// with predictors read before the update.  A payment's reward is
// multiplier / (conflicts - last conflict + 1), here without analyses.

typedef struct chb_expected chb_expected;

struct chb_expected {
  double q[2][6], count[6], increment, sum_r;
  uint64_t paid[2][6], sum_n;
  unsigned played;
  feedback_sums sums[FEEDBACK_GROUPS];
};

// Pays what CHB pays, everything assigned since the last payment, and
// follows it here.

static void pay (kissat *solver, chb_expected *x, bool conflict) {
  const uint64_t conflicts = solver->estimator.chb.conflicts;
  const double alpha = kissat_chb_alpha (conflicts);
  const double multiplier = conflict ? 1.0 : 0.9;
  for (unsigned i = x->played; i < SIZE_ARRAY (solver->trail); i++) {
    const unsigned idx = IDX (PEEK_ARRAY (solver->trail, i));
    const unsigned c = class_of (solver, idx);
    const double reward =
        multiplier / (conflicts - solver->last_conflict[idx] + 1);
    if (c == FEEDBACK_DEC) {
      double p[4];
      p[0] = x->paid[0][idx] ? x->q[0][idx] : NAN;
      p[1] = x->paid[1][idx] ? x->q[1][idx] : NAN;
      p[2] = kissat_get_score (solver, idx);
      p[3] = x->sum_n ? x->sum_r / x->sum_n : NAN;
      unsigned group;
      if (isnan (p[3]))
        group = FEEDBACK_GROUP_NO_CONST;
      else if (!isnan (p[0]) && !isnan (p[1]))
        group = FEEDBACK_GROUP_BOTH;
      else if (!isnan (p[0]))
        group = FEEDBACK_GROUP_NO_IMP;
      else if (!isnan (p[1]))
        group = FEEDBACK_GROUP_NO_DEC;
      else
        group = FEEDBACK_GROUP_NEITHER;
      feedback_sums *const sums = x->sums + group;
      sums->n++;
      sums->r += reward;
      if (group != FEEDBACK_GROUP_NO_CONST)
        for (unsigned j = 0; j < 4; j++)
          if (!isnan (p[j]))
            sums->interval[j] += (reward - p[j]) * (reward - p[j]);
      x->sum_n++, x->sum_r += reward;
    }
    x->q[c][idx] = (1 - alpha) * x->q[c][idx] + alpha * reward;
    x->paid[c][idx]++;
    x->count[idx] += x->increment;
  }
  x->played = SIZE_ARRAY (solver->trail);
  kissat_chb_assign (solver, conflict);
  if (conflict)
    x->increment *= 1 / 0.95;
}

// Three rounds of a pick, an implied variable, a payment, an assumed
// decision and a payment ending in a conflict, which give events in every
// group: without Q_const, without either class, with one, and with both.

static void check_chb (bool ucb) {
  kissat *solver = new_solver (6, "chb", 1, ucb ? "ucb" : 0, 1);
  const feedback *const fb = &solver->policy.feedback;
  assert (fb->started && fb->chb);
  chb_expected x;
  memset (&x, 0, sizeof x);
  x.increment = 1;
  const unsigned picked[3] = {0, 2, 2};
  const unsigned implied[3] = {1, 0, 3};
  const unsigned assumed[3] = {2, 1, 0};
  for (unsigned round = 0; round < 3; round++) {
    kissat_decide (solver);
    assert (IDX (PEEK_ARRAY (solver->trail, 0)) == picked[round]);
    imply (solver, implied[round]);
    pay (solver, &x, false);
    kissat_internal_assume (solver, LIT (assumed[round]));
    pay (solver, &x, true);
    kissat_backtrack_without_updating_phases (solver, 0);
    x.played = 0;
  }
  for (unsigned idx = 0; idx < 6; idx++) {
    for (unsigned c = 0; c < 2; c++) {
      assert (near (fb->q[c][idx], x.q[c][idx]));
      assert (fb->paid[c][idx] == x.paid[c][idx]);
    }
    assert (near (fb->count[idx], x.count[idx]));
    if (ucb)
      assert (kissat_same_double (fb->count[idx],
                                  solver->policy.keys.count[idx]));
  }
  assert (near (fb->increment, x.increment));
  assert (fb->m1.sum_n == x.sum_n && near (fb->m1.sum_r, x.sum_r));
  assert (fb->m1.events == 6);
  for (unsigned g = 0; g < FEEDBACK_GROUPS; g++) {
    assert (fb->m1.group[g].n == x.sums[g].n);
    assert (x.sums[g].n);
    assert (near (fb->m1.group[g].r, x.sums[g].r));
    for (unsigned j = 0; j < 4; j++)
      assert (near (fb->m1.group[g].interval[j], x.sums[g].interval[j]));
  }
  // Every pick had its payment, the outcome of M2.
  uint64_t outcomes = 0;
  for (unsigned i = 0; i < FEEDBACK_AGES; i++)
    outcomes += fb->m2.age[FEEDBACK_POLICY][i].n;
  assert (fb->m2.picks[FEEDBACK_POLICY] == 3 && outcomes == 3);
  kissat_release (solver);
}

static void test_feedback_chb (void) {
  check_chb (false);
  check_chb (true);
}

// M3.  An implied assignment at 'level' below the current one, placed on
// the trail at its end, in the current level's segment, as chronological
// backtracking leaves such variables.

static void imply_at (kissat *solver, unsigned idx, unsigned level) {
  assert (level < solver->level);
  imply (solver, idx);
  FRAME (solver->level).assigned--;
  solver->assigned[idx].level = level;
  FRAME (level).assigned++;
}

// A step's analyzed variables, recorded as CHB's participants (CHB) or
// bumped (VSIDS) without the expectations of M1.

static void record (kissat *solver, unsigned idx) {
  PUSH_STACK (solver->analyzed, idx);
  kissat_bump_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
}

static const feedback_yields *yields (const feedback *fb, unsigned kind,
                                      unsigned bin) {
  return &fb->m3.yield[kind][bin];
}

// On the VSIDS line: a pick whose propagation assigns two variables at its
// level; three conflicts in its interval, the first with a variable of its
// level in the next level's trail segment, the second after the level
// gained the asserted literal, and the third ending the interval, which it
// observes too; then picks with 'Y_v' defined, one closed when stable mode
// is left.

static void test_feedback_yield_vsids (void) {
  kissat *solver = new_solver (TEST_VARS, 0, 0, 0, 0);
  const feedback *const fb = &solver->policy.feedback;
  kissat_update_score (solver, 5, 100);
  expected e;
  memset (&e, 0, sizeof e);
  kissat_decide (solver);
  assert (IDX (PEEK_ARRAY (solver->trail, 0)) == 5);
  assert (fb->yielding == 6);
  assert (fb->state[5] & FEEDBACK_YIELD);
  assert (((fb->state[5] >> FEEDBACK_YIELD_SHIFT) & 7) ==
          FEEDBACK_YIELD_NONE);
  imply (solver, 2);
  imply (solver, 3);
  kissat_feedback_propagated (solver);
  assert (!fb->yielding);
  assert (fb->propagated[5] == 3);
  // Level 2: an assumed decision, not a pick, an implied variable, and a
  // variable of level 1 in level 2's segment.
  kissat_internal_assume (solver, LIT (0));
  imply (solver, 1);
  imply_at (solver, 4, 1);
  assert (FRAME (1).assigned == 4 && FRAME (2).assigned == 2);
  // The first conflict: its backtrack to level 1 keeps 4, and level 1
  // gains the asserted literal 6.
  begin_step (solver, &e);
  backtrack (solver, &e, 1);
  assert (VALUE (LIT (4)) && LEVEL (LIT (4)) == 1);
  imply (solver, 6);
  bump_round (solver, &e, (unsigned[]){5}, 1);
  end_step (solver, &e);
  assert (fb->observed[5] == 4);
  assert (fb->m3.levels == 4 && fb->m3.segments == 3);
  // The second conflict, with five variables at level 1.
  assert (FRAME (1).assigned == 5);
  begin_step (solver, &e);
  bump_round (solver, &e, (unsigned[]){2}, 1);
  end_step (solver, &e);
  assert (fb->observed[5] == 9);
  // The third ends the interval and counts.
  begin_step (solver, &e);
  backtrack (solver, &e, 0);
  assert (fb->state[5] & FEEDBACK_YIELD);
  bump_round (solver, &e, (unsigned[]){5}, 1);
  end_step (solver, &e);
  assert (!(fb->state[5] & FEEDBACK_YIELD));
  const feedback_yields *const none =
      yields (fb, FEEDBACK_POLICY, FEEDBACK_YIELD_NONE);
  assert (none->n == 1 && none->k == 3 && none->b == 2);
  assert (none->bumped == 1 && none->prop == 3 && none->obs == 14);
  const feedback_yields *const never =
      &fb->m3.age[FEEDBACK_POLICY][FEEDBACK_AGE_NEVER];
  assert (never->n == 1 && never->prop == 3 && never->obs == 14);
  assert (fb->m3.count[FEEDBACK_POLICY][FEEDBACK_COUNT_ZERO].obs == 14);
  assert (fb->m3.levels == 14 && fb->m3.segments == 13);
  assert (fb->yield[5] == 3);
  assert (!fb->propagated[5] && !fb->observed[5]);
  // A pick with 'Y_v' defined, closed without a conflict: its propagation
  // assigns nothing more.
  kissat_decide (solver);
  assert (IDX (PEEK_ARRAY (solver->trail, 0)) == 5);
  assert (((fb->state[5] >> FEEDBACK_YIELD_SHIFT) & 7) ==
          FEEDBACK_YIELD_BELOW4);
  kissat_feedback_propagated (solver);
  backtrack (solver, &e, 0);
  const feedback_yields *const below4 =
      yields (fb, FEEDBACK_POLICY, FEEDBACK_YIELD_BELOW4);
  assert (below4->n == 1 && below4->k == 0 && below4->prop == 1);
  assert (!below4->obs);
  assert (near (fb->yield[5], 0.9 * 3 + 0.1 * 1));
  // Another, still open when stable mode is left, which closes it.
  kissat_decide (solver);
  imply (solver, 2);
  kissat_feedback_propagated (solver);
  kissat_leave_stable_intervals (solver);
  close_expected (&e, 5, FEEDBACK_DEC), close_expected (&e, 2, FEEDBACK_IMP);
  assert (below4->n == 2 && below4->prop == 3 && !below4->obs);
  assert (near (fb->yield[5], 0.9 * (0.9 * 3 + 0.1 * 1) + 0.1 * 2));
  assert (fb->m3.picks[FEEDBACK_POLICY] == 3);
  assert (!fb->m3.picks[FEEDBACK_UNIFORM]);
  check_sums (solver, &e, TEST_VARS);
  kissat_release (solver);
}

// Uniform picks crossed with stale against recent: with gamma one and a
// single unassigned variable, its pick when never observed, and again
// right after its interval spanned a conflict.

static void test_feedback_yield_crossed (void) {
  kissat *solver = new_solver (3, "gammappm", 1000000, 0, 0);
  const feedback *const fb = &solver->policy.feedback;
  expected e;
  memset (&e, 0, sizeof e);
  for (unsigned round = 0; round < 2; round++) {
    kissat_internal_assume (solver, LIT (0));
    kissat_internal_assume (solver, LIT (1));
    kissat_decide (solver);
    assert (IDX (PEEK_ARRAY (solver->trail, 2)) == 2);
    const unsigned state = fb->state[2];
    assert ((state >> FEEDBACK_KIND_SHIFT) & 1);
    assert (((state >> FEEDBACK_AGE_SHIFT) & 3) ==
            (round ? FEEDBACK_AGE_RECENT : FEEDBACK_AGE_NEVER));
    kissat_feedback_propagated (solver);
    if (round)
      backtrack (solver, &e, 0);
    else {
      begin_step (solver, &e);
      backtrack (solver, &e, 0);
      bump_round (solver, &e, (unsigned[]){2}, 1);
      end_step (solver, &e);
    }
  }
  const feedback_yields *const stale =
      &fb->m3.crossed[FEEDBACK_STALE][FEEDBACK_YIELD_NONE];
  assert (stale->n == 1 && stale->k == 1 && stale->b == 1);
  assert (stale->prop == 1 && stale->obs == 1);
  const feedback_yields *const recent =
      &fb->m3.crossed[FEEDBACK_RECENT][FEEDBACK_YIELD_BELOW2];
  assert (recent->n == 1 && recent->k == 0 && recent->prop == 1);
  assert (!recent->obs);
  for (unsigned bin = 0; bin < FEEDBACK_YIELDS; bin++) {
    const feedback_yields *const all = yields (fb, FEEDBACK_UNIFORM, bin);
    assert (all->n == fb->m3.crossed[0][bin].n + fb->m3.crossed[1][bin].n);
    assert (!yields (fb, FEEDBACK_POLICY, bin)->n);
  }
  assert (fb->m3.picks[FEEDBACK_UNIFORM] == 2);
  kissat_release (solver);
}

// On the CHB line: a pick paid at its propagation, whose interval a
// conflict's backtrack ends, closing at the step's end with the conflict
// counted; a pick whose interval ends at a step without participants; and
// a pick closed when stable mode is left.  M2's outcome is the payment,
// which M3 adds when the interval closes.

static void test_feedback_yield_chb (void) {
  kissat *solver = new_solver (6, "chb", 1, 0, 0);
  const feedback *const fb = &solver->policy.feedback;
  chb_expected x;
  memset (&x, 0, sizeof x);
  x.increment = 1;
  expected e;
  memset (&e, 0, sizeof e);
  double rewards[3];
  for (unsigned round = 0; round < 3; round++) {
    kissat_decide (solver);
    assert (IDX (PEEK_ARRAY (solver->trail, 0)) == 0);
    for (unsigned i = 0; i < round; i++)
      imply (solver, 1 + i);
    if (!round)
      imply (solver, 3);
    kissat_feedback_propagated (solver);
    const double paid = fb->m2.age[FEEDBACK_POLICY][0].r +
                        fb->m2.age[FEEDBACK_POLICY][1].r +
                        fb->m2.age[FEEDBACK_POLICY][2].r +
                        fb->m2.age[FEEDBACK_POLICY][3].r;
    pay (solver, &x, round != 1);
    rewards[round] = fb->m2.age[FEEDBACK_POLICY][0].r +
                     fb->m2.age[FEEDBACK_POLICY][1].r +
                     fb->m2.age[FEEDBACK_POLICY][2].r +
                     fb->m2.age[FEEDBACK_POLICY][3].r - paid;
    assert (!(fb->state[0] & FEEDBACK_PENDING));
    assert (fb->state[0] & FEEDBACK_YIELD);
    if (round < 2) {
      begin_step (solver, &e);
      kissat_backtrack_without_updating_phases (solver, 0);
      x.played = 0;
      assert (solver->policy.intervals.state[0] & INTERVALS_DEFERRED);
      if (!round)
        record (solver, 3);
      kissat_policy_end_analysis (solver);
      e.analyzing = false;
    } else {
      begin_step (solver, &e);
      record (solver, 0);
      kissat_policy_end_analysis (solver);
      e.analyzing = false;
      kissat_leave_stable_intervals (solver);
    }
    assert (!fb->state[0]);
  }
  const feedback_yields *const none =
      yields (fb, FEEDBACK_POLICY, FEEDBACK_YIELD_NONE);
  assert (none->n == 1 && none->prop == 2 && none->obs == 2);
  assert (near (none->r, rewards[0]));
  const feedback_yields *const below4 =
      yields (fb, FEEDBACK_POLICY, FEEDBACK_YIELD_BELOW4);
  assert (below4->n == 2 && below4->prop == 2 + 3 && below4->obs == 3);
  assert (near (below4->r, rewards[1] + rewards[2]));
  assert (near (fb->yield[0], 0.9 * (0.9 * 2 + 0.1 * 2) + 0.1 * 3));
  assert (fb->m3.picks[FEEDBACK_POLICY] == 3);
  assert (fb->m2.picks[FEEDBACK_POLICY] == 3);
  kissat_release (solver);
}

// Through the solver's own propagation and analysis: deciding 1 implies 2
// and 3 by binary clauses and 4 by a ternary one, and (-2 -4) is falsified.
// The conflict is on the pick's level, which the analysis backtracks, so
// the pick closes with the conflict counted.

static void test_feedback_yield_search (void) {
  kissat *solver = kissat_init ();
#ifndef NDEBUG
  kissat_set_option (solver, "check", 0);
#endif
  const int clauses[][4] = {{-1, 2, 0}, {-1, 3, 0}, {-2, -3, 4, 0},
                            {-2, -4, 0}, {1, 5, 6, 0}};
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
  const feedback *const fb = &solver->policy.feedback;
  kissat_update_score (solver, 0, 100);
  kissat_decide (solver);
  assert (PEEK_ARRAY (solver->trail, 0) == LIT (0));
  clause *const conflict = kissat_search_propagate (solver);
  assert (conflict);
  assert (fb->propagated[0] == 4);
  assert (FRAME (1).assigned == 4);
  kissat_analyze (solver, conflict);
  assert (!solver->level);
  assert (!(fb->state[0] & FEEDBACK_YIELD));
  const feedback_yields *const none =
      yields (fb, FEEDBACK_POLICY, FEEDBACK_YIELD_NONE);
  assert (none->n == 1 && none->prop == 4 && none->obs == 4);
  assert (none->k == 1);
  assert (fb->yield[0] == 4);
  kissat_release (solver);
}

#endif

void tissat_schedule_feedback (void) {
#if defined(FEEDBACK) && !defined(NOPTIONS)
  SCHEDULE_FUNCTION (test_feedback_vsids_sums);
  SCHEDULE_FUNCTION (test_feedback_vsids_events);
  SCHEDULE_FUNCTION (test_feedback_vsids_steps);
  SCHEDULE_FUNCTION (test_feedback_vsids_ages);
  SCHEDULE_FUNCTION (test_feedback_compact);
  SCHEDULE_FUNCTION (test_feedback_chb);
  SCHEDULE_FUNCTION (test_feedback_yield_vsids);
  SCHEDULE_FUNCTION (test_feedback_yield_crossed);
  SCHEDULE_FUNCTION (test_feedback_yield_chb);
  SCHEDULE_FUNCTION (test_feedback_yield_search);
#endif
}
