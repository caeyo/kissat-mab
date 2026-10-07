#include "feedback.h"

#ifdef FEEDBACK

#include "allocate.h"
#include "bump.h"
#include "chb.h"
#include "error.h"
#include "inline.h"
#include "print.h"

#include <inttypes.h>
#include <math.h>
#include <string.h>

// The arrays of a line, of 'size' entries each, zero beyond 'old'.

static void *resize_array (kissat *solver, void *array, size_t bytes,
                           unsigned old_size, unsigned new_size) {
  void *res = kissat_calloc (solver, new_size, bytes);
  const unsigned kept = old_size < new_size ? old_size : new_size;
  if (kept)
    memcpy (res, array, (size_t) kept * bytes);
  if (array)
    kissat_dealloc (solver, array, old_size, bytes);
  return res;
}

#define RESIZE(P, ENTRIES) \
  (P) = resize_array (solver, (P), (ENTRIES) * sizeof *(P), old_size, \
                      new_size)

void kissat_resize_feedback (kissat *solver, unsigned new_size) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  const unsigned old_size = fb->size;
  if (old_size == new_size)
    return;
  RESIZE (fb->state, 1);
  if (fb->chb) {
    for (unsigned c = 0; c < 2; c++) {
      RESIZE (fb->q[c], 1);
      RESIZE (fb->paid[c], 1);
    }
    RESIZE (fb->count, 1);
    RESIZE (fb->latest, 1);
#ifdef SHADOW
    RESIZE (fb->repaid, 1);
#endif
  } else {
    for (unsigned c = 0; c < 2; c++) {
      RESIZE (fb->n[c], 1);
      RESIZE (fb->r[c], 1);
    }
    RESIZE (fb->opened, 1);
    RESIZE (fb->frozen, FEEDBACK_PREDICTORS);
    RESIZE (fb->start, 1);
    RESIZE (fb->bumps, 1);
    RESIZE (fb->last, 1);
#ifndef NDEBUG
    RESIZE (fb->check.rounds, 1);
    RESIZE (fb->check.bumped, 1);
    RESIZE (fb->check.marked, 1);
#endif
  }
  fb->size = new_size;
}

#define RELEASE(P, ENTRIES) \
  do { \
    if (P) \
      kissat_dealloc (solver, (P), size, (ENTRIES) * sizeof *(P)); \
    (P) = 0; \
  } while (0)

void kissat_release_feedback (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  const unsigned size = fb->size;
  RELEASE (fb->state, 1);
  for (unsigned c = 0; c < 2; c++) {
    RELEASE (fb->n[c], 1);
    RELEASE (fb->r[c], 1);
    RELEASE (fb->q[c], 1);
    RELEASE (fb->paid[c], 1);
  }
  RELEASE (fb->opened, 1);
  RELEASE (fb->frozen, FEEDBACK_PREDICTORS);
  RELEASE (fb->start, 1);
  RELEASE (fb->bumps, 1);
  RELEASE (fb->last, 1);
  RELEASE (fb->count, 1);
  RELEASE (fb->latest, 1);
#ifdef SHADOW
  RELEASE (fb->repaid, 1);
#endif
#ifndef NDEBUG
  RELEASE (fb->check.rounds, 1);
  RELEASE (fb->check.bumped, 1);
  RELEASE (fb->check.marked, 1);
  RELEASE_STACK (fb->check.listed);
#endif
  RELEASE_STACK (fb->deferred);
  fb->size = 0;
}

// At the start of the search: the line, the decay of the counts (the score
// decay, as for UCB's counts, so that their increments are the scores'),
// and the arrays.  A later search keeps them.

void kissat_start_feedback (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (fb->started)
    return;
  fb->started = true;
  fb->chb = kissat_chb (solver);
  const double decay = GET_OPTION (decay) * 1e-3;
  fb->growth = 1.0 / (1.0 - decay);
  fb->increment = 1;
  fb->counted = 0;
  kissat_resize_feedback (solver, solver->size);
  kissat_very_verbose (solver, "measuring the decision's feedback on %s "
                               "scores",
                       fb->chb ? "CHB" : "VSIDS");
}

void kissat_move_feedback (kissat *solver, unsigned from, unsigned to) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  fb->state[to] = fb->state[from];
  if (fb->chb) {
    for (unsigned c = 0; c < 2; c++) {
      fb->q[c][to] = fb->q[c][from];
      fb->paid[c][to] = fb->paid[c][from];
    }
    fb->count[to] = fb->count[from];
    fb->latest[to] = fb->latest[from];
#ifdef SHADOW
    fb->repaid[to] = fb->repaid[from];
#endif
    return;
  }
  for (unsigned c = 0; c < 2; c++) {
    fb->n[c][to] = fb->n[c][from];
    fb->r[c][to] = fb->r[c][from];
  }
  fb->opened[to] = fb->opened[from];
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++)
    fb->frozen[FEEDBACK_PREDICTORS * to + i] =
        fb->frozen[FEEDBACK_PREDICTORS * from + i];
  fb->start[to] = fb->start[from];
  fb->bumps[to] = fb->bumps[from];
  fb->last[to] = fb->last[from];
#ifndef NDEBUG
  fb->check.rounds[to] = fb->check.rounds[from];
  fb->check.bumped[to] = fb->check.bumped[from];
  fb->check.marked[to] = fb->check.marked[from];
#endif
}

void kissat_clear_feedback (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  fb->state[idx] = 0;
  if (fb->chb) {
    for (unsigned c = 0; c < 2; c++) {
      fb->q[c][idx] = 0;
      fb->paid[c][idx] = 0;
    }
    fb->count[idx] = 0;
    fb->latest[idx] = 0;
#ifdef SHADOW
    fb->repaid[idx] = 0;
#endif
    return;
  }
  for (unsigned c = 0; c < 2; c++)
    fb->n[c][idx] = fb->r[c][idx] = 0;
  fb->opened[idx] = 0;
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++)
    fb->frozen[FEEDBACK_PREDICTORS * idx + i] = 0;
  fb->start[idx] = fb->bumps[idx] = fb->last[idx] = 0;
#ifndef NDEBUG
  fb->check.rounds[idx] = 0;
  fb->check.bumped[idx] = 0;
  fb->check.marked[idx] = 0;
#endif
}

static inline unsigned class_of (kissat *solver, unsigned idx) {
  return solver->assigned[idx].reason == DECISION_REASON ? FEEDBACK_DEC
                                                         : FEEDBACK_IMP;
}

// VSIDS line: every active literal assigned since the last record opens an
// interval, at the current increment and round counter, which it was
// assigned at: neither changes between records (see 'keys.h').  While a
// step's closes are deferred, the literals assigned since its backtrack
// wait for the step's bump round, which records them after it.

void kissat_record_feedback (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started || fb->chb || !solver->stable || fb->deferring)
    return;
  const unsigned size = SIZE_ARRAY (solver->trail);
  unsigned counted = fb->counted;
  if (counted >= size)
    return;
  const unsigned *const trail = BEGIN_ARRAY (solver->trail);
  const flags *const flags = solver->flags;
  const double inc = solver->scinc;
  const uint64_t round = solver->estimator.rounds;
  while (counted < size) {
    const unsigned lit = trail[counted++];
    const unsigned idx = IDX (lit);
    if (!flags[idx].active)
      continue;
    fb->opened[idx] = inc;
    fb->start[idx] = round;
    fb->bumps[idx] = 0;
    fb->state[idx] |= FEEDBACK_OPEN;
  }
  fb->counted = size;
}

#ifndef NDEBUG

// The checks of assertion builds (see 'feedback.h').  An interval's rounds
// and bumped rounds against those counted at every bump round from the
// trail and the analyzed variables.

static void check_interval (kissat *solver, unsigned idx, uint64_t k,
                            uint64_t b) {
  feedback *const fb = &solver->policy.feedback;
  uint64_t *const rounds = fb->check.rounds + idx;
  uint64_t *const bumped = fb->check.bumped + idx;
  if (*rounds != k || *bumped != b)
    kissat_fatal ("feedback: interval of variable %u closed after %" PRIu64
                  " bump rounds, %" PRIu64 " with a bump, but %" PRIu64
                  " and %" PRIu64 " counted (bump round %" PRIu64 ")",
                  idx, k, b, *rounds, *bumped, solver->estimator.rounds);
  *rounds = *bumped = 0;
  fb->check.intervals++;
}

#endif

// VSIDS line: a bump round starts.  The intervals of the variables assigned
// since the last record are opened first, so that their bumps in this
// round find them, and the round counted in them, unless the step's closes
// are deferred: then the literals assigned since its backtrack wait for
// the round's end.

void kissat_feedback_round (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (!fb->chb);
  assert (solver->stable);
  kissat_record_feedback (solver);
}

// VSIDS line: the bump of the active variable 'idx' in the current round,
// before its score, in the interval it falls in: the one a backtrack of
// this step ended, if any, whose class is kept with it, since the
// variable may be assigned again (the asserted literal); else the open
// one of the assigned variable.  A bump in no interval happens only in
// the unit tests, which bump outside analysis steps.

void kissat_feedback_bump (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (!fb->chb);
  const unsigned state = fb->state[idx];
  unsigned c;
  if (state & FEEDBACK_DEFERRED) {
    c = state & FEEDBACK_DEFERRED_IMP ? FEEDBACK_IMP : FEEDBACK_DEC;
    fb->m1.bumps[1][c]++;
  } else if (VALUE (LIT (idx)) && state & FEEDBACK_OPEN) {
    assert (solver->assigned[idx].trail < fb->counted);
    c = class_of (solver, idx);
    fb->m1.bumps[0][c]++;
  } else {
    fb->m1.unobserved++;
    return;
  }
  fb->r[c][idx] += solver->scinc;
  fb->bumps[idx]++;
}

// Bins and sums.

static unsigned age_bin (uint64_t age) {
  if (age >= 10 * FEEDBACK_WINDOW)
    return FEEDBACK_AGE_OLD;
  if (age >= FEEDBACK_WINDOW)
    return FEEDBACK_AGE_STALE;
  return FEEDBACK_AGE_RECENT;
}

static unsigned count_bin (double count) {
  assert (count >= 0);
  if (!(count > 0))
    return FEEDBACK_COUNT_ZERO;
  if (count < 1)
    return FEEDBACK_COUNT_BELOW1;
  if (count < 5)
    return FEEDBACK_COUNT_BELOW5;
  return FEEDBACK_COUNT_ABOVE5;
}

static unsigned calibration_bin (double p) {
  assert (p >= 0);
  const double tenths = FEEDBACK_BINS * p;
  return tenths < FEEDBACK_BINS - 1 ? (unsigned) tenths : FEEDBACK_BINS - 1;
}

// The predictors defined in each group, by line.

#define BIT(I) (1u << (I))
#define DEC_BIT BIT (FEEDBACK_PREDICT_DEC)
#define IMP_BIT BIT (FEEDBACK_PREDICT_IMP)
#define ALL_BIT BIT (FEEDBACK_PREDICT_ALL)
#define CONST_BIT BIT (FEEDBACK_PREDICT_CONST)

static const unsigned group_mask[2][FEEDBACK_GROUPS] = {
    // VSIDS: p_all is undefined exactly when both counts are zero.
    {DEC_BIT | IMP_BIT | ALL_BIT | CONST_BIT, DEC_BIT | ALL_BIT | CONST_BIT,
     IMP_BIT | ALL_BIT | CONST_BIT, CONST_BIT, 0},
    // CHB: CHB's own Q is always defined.
    {DEC_BIT | IMP_BIT | ALL_BIT | CONST_BIT, DEC_BIT | ALL_BIT | CONST_BIT,
     IMP_BIT | ALL_BIT | CONST_BIT, ALL_BIT | CONST_BIT, 0},
};

static unsigned group_of (const double *p, bool chb) {
  unsigned res;
  if (isnan (p[FEEDBACK_PREDICT_CONST]))
    res = FEEDBACK_GROUP_NO_CONST;
  else {
    const bool dec = !isnan (p[FEEDBACK_PREDICT_DEC]);
    const bool imp = !isnan (p[FEEDBACK_PREDICT_IMP]);
    res = dec && imp ? FEEDBACK_GROUP_BOTH
          : dec      ? FEEDBACK_GROUP_NO_IMP
          : imp      ? FEEDBACK_GROUP_NO_DEC
                     : FEEDBACK_GROUP_NEITHER;
#ifndef NDEBUG
    for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++)
      assert (!isnan (p[i]) == !!(group_mask[chb][res] & BIT (i)));
#endif
  }
  (void) chb;
  return res;
}

// An interval of 'k' rounds, 'b' of them with a bump, and the errors of
// the predictors in 'mask'.

static void add_interval (feedback_sums *sums, const double *p,
                          unsigned mask, uint64_t k, uint64_t b) {
  assert (k), assert (b <= k);
  sums->n++;
  sums->k += k;
  sums->b += b;
  const double rate = (double) b / k;
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++) {
    if (!(mask & BIT (i)))
      continue;
    const double q = p[i], miss = 1 - q, error = rate - q;
    sums->round[i] += b * miss * miss + (k - b) * q * q;
    sums->interval[i] += error * error;
  }
}

// A decided payment of 'reward', and the errors of the predictors in
// 'mask'.

static void add_payment (feedback_sums *sums, const double *p,
                         unsigned mask, double reward) {
  sums->n++;
  sums->r += reward;
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++) {
    if (!(mask & BIT (i)))
      continue;
    const double error = reward - p[i];
    sums->interval[i] += error * error;
  }
}

// M2: a pending pick that was not followed by its decision, which happens
// only when the unit tests pick without deciding, is void: it is taken back
// from the picks, so that picks stay outcomes plus open picks.  In a run
// every pick is decided at once, and the analysis checks that the picks
// of both kinds are the policy's search picks ('policy-picks').

static void void_pick (feedback *fb, unsigned state) {
  assert (state & FEEDBACK_PENDING);
  const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
  assert (fb->m2.picks[kind]);
  fb->m2.picks[kind]--;
}

// M2: the outcome of a pending pick, 'k' and 'b' of its interval (VSIDS)
// or its payment 'reward' (CHB).

static void add_outcome (feedback *fb, unsigned state, uint64_t k,
                         uint64_t b, double reward) {
  assert (state & FEEDBACK_PENDING);
  const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
  const unsigned age = (state >> FEEDBACK_AGE_SHIFT) & 3;
  const unsigned count = (state >> FEEDBACK_COUNT_SHIFT) & 3;
  feedback_sums *const sums[2] = {&fb->m2.age[kind][age],
                                  &fb->m2.count[kind][count]};
  for (unsigned i = 0; i < 2; i++) {
    feedback_sums *const s = sums[i];
    s->n++;
    s->k += k;
    s->b += b;
    s->bumped += b > 0;
    s->r += reward;
  }
}

// VSIDS line: the interval of the active variable 'idx', of class 'c',
// closes: at its unassignment in stable mode, after the bump round of the
// analysis step whose backtrack ended it, or when stable mode is left.
// Its rounds go to the count of its class, as UCB's do; a decided interval
// adds to the sums of p_const; the interval of a pending pick is an event
// of M1 and the pick's outcome in M2.  Every variable on the trail has its
// interval open when it closes, except in the unit tests, which assign
// some variables off the trail; for those there is nothing to close.

static void close_interval (kissat *solver, unsigned idx, unsigned c) {
  feedback *const fb = &solver->policy.feedback;
  assert (!fb->chb);
  if (!(fb->state[idx] & FEEDBACK_OPEN))
    return;
  const double inc = solver->scinc;
  fb->n[c][idx] += (inc - fb->opened[idx]) / (fb->growth - 1);
  const uint64_t round = solver->estimator.rounds;
  assert (fb->start[idx] <= round);
  const uint64_t k = round - fb->start[idx];
  const uint64_t b = fb->bumps[idx];
  assert (b <= k);
#ifndef NDEBUG
  check_interval (solver, idx, k, b);
#endif
  fb->m1.intervals[c]++;
  if (k)
    fb->last[idx] = round;
  if (c == FEEDBACK_DEC) {
    fb->m1.sum_k += k;
    fb->m1.sum_b += b;
  }
  const unsigned state = fb->state[idx];
  if (state & FEEDBACK_PENDING && c != FEEDBACK_DEC)
    void_pick (fb, state);
  else if (state & FEEDBACK_PENDING) {
    fb->m1.events++;
    if (!k)
      fb->m1.zero++;
    else {
      const double *const p = fb->frozen + FEEDBACK_PREDICTORS * idx;
      const unsigned group = group_of (p, false);
      add_interval (fb->m1.group + group, p, group_mask[0][group], k, b);
      if (group == FEEDBACK_GROUP_BOTH)
        for (unsigned d = 0; d < 2; d++) {
          const double q = p[d ? FEEDBACK_PREDICT_IMP : FEEDBACK_PREDICT_DEC];
          add_interval (&fb->m1.calibration[d][calibration_bin (q)], p, 0,
                        k, b);
        }
    }
    add_outcome (fb, state, k, b, 0);
  }
  fb->state[idx] = 0;
  fb->opened[idx] = inc;
  fb->start[idx] = round;
  fb->bumps[idx] = 0;
}

// Stable-mode backtracking unassigned 'idx'.  Inside an analysis step the
// close waits for the step's bump round, or its end (LRB's interval).

void kissat_feedback_unassign (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started || fb->chb)
    return;
  assert (solver->stable);
  const unsigned c = class_of (solver, idx);
  uint16_t *const state = fb->state + idx;
  if (!fb->analyzing || !(*state & FEEDBACK_OPEN)) {
    close_interval (solver, idx, c);
    return;
  }
  assert (solver->assigned[idx].trail < fb->counted);
  assert (!(*state & FEEDBACK_DEFERRED));
  *state |= FEEDBACK_DEFERRED;
  if (c == FEEDBACK_IMP)
    *state |= FEEDBACK_DEFERRED_IMP;
  PUSH_STACK (fb->deferred, idx);
  fb->deferring = true;
}

// The intervals deferred in the current step close, with the increment and
// round counter of now: after its bump round, they count it.

static void finish_deferred (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  assert (fb->deferring);
  for (all_stack (unsigned, idx, fb->deferred)) {
    const unsigned state = fb->state[idx];
    assert (state & FEEDBACK_DEFERRED);
    const unsigned c =
        state & FEEDBACK_DEFERRED_IMP ? FEEDBACK_IMP : FEEDBACK_DEC;
    close_interval (solver, idx, c);
  }
  CLEAR_STACK (fb->deferred);
  fb->deferring = false;
}

// VSIDS line: a step of conflict analysis starts, before its backtracks.
// Assertion builds list the active variables assigned now, which the
// step's bump round observes.

void kissat_feedback_begin_analysis (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started || fb->chb || !solver->stable)
    return;
  assert (!fb->analyzing), assert (!fb->deferring);
  assert (EMPTY_STACK (fb->deferred));
  fb->analyzing = true;
#ifndef NDEBUG
  unsigneds *const listed = &fb->check.listed;
  CLEAR_STACK (*listed);
  const flags *const flags = solver->flags;
  for (all_stack (unsigned, lit, solver->trail))
    if (flags[IDX (lit)].active)
      PUSH_STACK (*listed, IDX (lit));
#endif
}

// The step ends, after its bump round if it had one: closes still deferred
// (no round) happen now, without a round.

void kissat_feedback_end_analysis (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->analyzing)
    return;
  if (fb->deferring)
    finish_deferred (solver);
  fb->analyzing = false;
#ifndef NDEBUG
  CLEAR_STACK (fb->check.listed);
#endif
}

// VSIDS line: a bump round ends, after the increment grew.  Assertion
// builds count the round and the bumps of the variables it observes, the
// step's listed ones (outside a step, in the unit tests, those on the
// trail).  Then the deferred closes happen, counting the round, and the
// literals assigned since the step's backtrack open their intervals.

void kissat_feedback_round_end (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (!fb->chb);
  assert (solver->stable);
#ifndef NDEBUG
  const uint64_t round = solver->estimator.rounds;
  const flags *const flags = solver->flags;
  uint64_t *const marked = fb->check.marked;
  for (all_stack (unsigned, idx, solver->analyzed))
    if (flags[idx].active)
      marked[idx] = round;
  uint64_t *const rounds = fb->check.rounds;
  uint64_t *const bumped = fb->check.bumped;
  if (fb->analyzing) {
    for (all_stack (unsigned, idx, fb->check.listed)) {
      rounds[idx]++;
      if (marked[idx] == round)
        bumped[idx]++;
    }
    CLEAR_STACK (fb->check.listed);
  } else
    for (all_stack (unsigned, lit, solver->trail)) {
      const unsigned idx = IDX (lit);
      if (!flags[idx].active)
        continue;
      rounds[idx]++;
      if (marked[idx] == round)
        bumped[idx]++;
    }
#endif
  if (!fb->deferring)
    return;
  finish_deferred (solver);
  kissat_record_feedback (solver);
}

// Every variable still assigned when stable mode is left closes its
// interval.  Entering stable mode opens one for every assigned variable at
// the next record.

void kissat_leave_stable_feedback (kissat *solver) {
  const feedback *const fb = &solver->policy.feedback;
  if (!fb->started || fb->chb)
    return;
  assert (solver->stable);
  assert (!fb->analyzing);
  kissat_record_feedback (solver);
  const flags *const flags = solver->flags;
  const unsigned *const begin = BEGIN_ARRAY (solver->trail);
  const unsigned *const end = END_ARRAY (solver->trail);
  for (const unsigned *p = begin; p != end; p++) {
    const unsigned idx = IDX (*p);
    if (flags[idx].active)
      close_interval (solver, idx, class_of (solver, idx));
  }
}

void kissat_enter_stable_feedback (kissat *solver) {
  solver->policy.feedback.counted = 0;
}

// The sums in units of the increment and the increments at assignment
// follow the scores' rescale, after the literals assigned since the last
// record were recorded at the old increment.

void kissat_rescale_feedback (kissat *solver, double factor) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started || fb->chb)
    return;
  kissat_record_feedback (solver);
  for (all_variables (idx)) {
    for (unsigned c = 0; c < 2; c++) {
      fb->n[c][idx] *= factor;
      fb->r[c][idx] *= factor;
    }
    fb->opened[idx] *= factor;
  }
}

// CHB line: a payment.  If its variable is decided it is an event of M1,
// whose predictors are read before the update; the ERWA of its class,
// its payments, UCB's count and its latest payment follow; and a pending
// pick of the variable has its outcome.

void kissat_feedback_paid (kissat *solver, unsigned idx, double reward,
                           double alpha, double old_q,
                           uint64_t conflicts) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (fb->chb);
  assert (VALUE (LIT (idx)));
  const unsigned c = class_of (solver, idx);
  if (c == FEEDBACK_DEC) {
    double p[FEEDBACK_PREDICTORS];
    p[FEEDBACK_PREDICT_DEC] =
        fb->paid[FEEDBACK_DEC][idx] ? fb->q[FEEDBACK_DEC][idx] : NAN;
    p[FEEDBACK_PREDICT_IMP] =
        fb->paid[FEEDBACK_IMP][idx] ? fb->q[FEEDBACK_IMP][idx] : NAN;
    p[FEEDBACK_PREDICT_ALL] = old_q;
    p[FEEDBACK_PREDICT_CONST] =
        fb->m1.sum_n ? fb->m1.sum_r / fb->m1.sum_n : NAN;
    const unsigned group = group_of (p, true);
    add_payment (fb->m1.group + group, p, group_mask[1][group], reward);
    if (group == FEEDBACK_GROUP_BOTH)
      for (unsigned d = 0; d < 2; d++) {
        const double q = p[d ? FEEDBACK_PREDICT_IMP : FEEDBACK_PREDICT_DEC];
        add_payment (&fb->m1.calibration[d][calibration_bin (q)], p, 0,
                     reward);
      }
    fb->m1.events++;
    fb->m1.sum_n++;
    fb->m1.sum_r += reward;
  }
  fb->m1.intervals[c]++;
  double *const q = fb->q[c] + idx;
  *q = (1 - alpha) * *q + alpha * reward;
  fb->paid[c][idx]++;
  fb->count[idx] += fb->increment;
  fb->latest[idx] = conflicts;
  const unsigned state = fb->state[idx];
  if (state & FEEDBACK_PENDING) {
    if (c == FEEDBACK_DEC)
      add_outcome (fb, state, 0, 0, reward);
    else
      void_pick (fb, state);
    fb->state[idx] = 0;
  }
}

// CHB line: the counts' increment grows by 1/d after the payments of
// every stable-mode conflict, and the counts are rescaled with it when it
// exceeds 'MAX_SCORE', as UCB's are ('kissat_keys_chb_conflict').

void kissat_feedback_chb_conflict (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (fb->chb);
  fb->increment *= fb->growth;
  if (fb->increment <= MAX_SCORE)
    return;
  const double factor = 1.0 / fb->increment;
  double *const count = fb->count;
  for (all_variables (idx))
    count[idx] *= factor;
  fb->increment *= factor;
}

#ifdef SHADOW

// Shadow mode's count of the payments, for the complete check.

void kissat_shadow_feedback_paid (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (fb->started)
    fb->repaid[idx]++;
}

#endif

#ifndef NDEBUG

// Every 1000 picks: the counts against UCB's (see 'feedback.h'), on VSIDS
// scores those of UCB counting LRB's interval ('ucbinterval=1').

#define FEEDBACK_CHECK_TOLERANCE 1e-12

static void complete_check (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  fb->check.complete++;
  const keys *const keys = &solver->policy.keys;
  const flags *const flags = solver->flags;
  const uint64_t pick = fb->check.picks;
  if (!fb->chb) {
    if (!keys->interval)
      return;
    const double inc = solver->scinc;
    const double geometric = fb->growth - 1;
    const value *const values = solver->values;
    const assigned *const assigned = solver->assigned;
    for (all_variables (idx)) {
      if (!flags[idx].active)
        continue;
      double mine = fb->n[FEEDBACK_DEC][idx] + fb->n[FEEDBACK_IMP][idx];
      double ucb = keys->count[idx];
      if (values[LIT (idx)]) {
        const unsigned trail = assigned[idx].trail;
        const bool recorded = trail < fb->counted;
        const bool ucb_recorded = trail < keys->counted;
        if (recorded)
          mine += (inc - fb->opened[idx]) / geometric;
        if (ucb_recorded)
          ucb += (inc - keys->opened[idx]) / geometric;
        if (recorded && ucb_recorded &&
            !kissat_same_double (fb->opened[idx], keys->opened[idx]))
          kissat_fatal ("feedback: pick %" PRIu64 ": increment %.17g at "
                        "the assignment of variable %u differs from "
                        "UCB's %.17g",
                        pick, fb->opened[idx], idx, keys->opened[idx]);
      }
      const double n = mine / inc, expected = ucb / inc;
      const double error = fabs (n - expected) / (1 + expected);
      fb->check.counts++;
      if (error > fb->check.error)
        fb->check.error = error;
      if (!(error <= FEEDBACK_CHECK_TOLERANCE))
        kissat_fatal ("feedback: pick %" PRIu64 ": count %.17g of variable "
                      "%u differs from UCB's %.17g",
                      pick, n, idx, expected);
    }
    return;
  }
  if (keys->counts) {
    if (!kissat_same_double (fb->increment, keys->increment))
      kissat_fatal ("feedback: pick %" PRIu64 ": CHB counts' increment "
                    "%.17g differs from UCB's %.17g",
                    pick, fb->increment, keys->increment);
    for (all_variables (idx)) {
      if (!flags[idx].active)
        continue;
      if (!kissat_same_double (fb->count[idx], keys->count[idx]))
        kissat_fatal ("feedback: pick %" PRIu64 ": CHB count %.17g of "
                      "variable %u differs from UCB's %.17g",
                      pick, fb->count[idx], idx, keys->count[idx]);
      fb->check.chb++;
    }
  }
#ifdef SHADOW
  for (all_variables (idx)) {
    if (!flags[idx].active)
      continue;
    const uint64_t paid =
        fb->paid[FEEDBACK_DEC][idx] + fb->paid[FEEDBACK_IMP][idx];
    if (paid != fb->repaid[idx])
      kissat_fatal ("feedback: pick %" PRIu64 ": %" PRIu64 " payments of "
                    "variable %u by class, %" PRIu64 " in shadow mode",
                    pick, paid, idx, fb->repaid[idx]);
    fb->check.payments++;
  }
#endif
}

#endif

// A pick of the policy.  In search, in stable mode, it is pending until
// its outcome, with its kind and its variable's age and count bins, and on
// the VSIDS line the four predictors of M1 are frozen: the variable is
// assigned as a decision right after the pick, and its counts and the sums
// of p_const do not change before its interval opens.

void kissat_feedback_pick (kissat *solver, unsigned idx, bool uniform) {
  feedback *const fb = &solver->policy.feedback;
#ifndef NDEBUG
  if (!(++fb->check.picks % 1000))
    complete_check (solver);
#endif
  if (!fb->started || solver->warming)
    return;
  assert (solver->stable);
  assert (!VALUE (LIT (idx)));
  const unsigned old_state = fb->state[idx];
  assert (!(old_state & FEEDBACK_OPEN));
  if (old_state & FEEDBACK_PENDING)
    void_pick (fb, old_state);
  const unsigned kind = uniform ? FEEDBACK_UNIFORM : FEEDBACK_POLICY;
  fb->m2.picks[kind]++;
  unsigned age;
  double count;
  if (fb->chb) {
    const uint64_t paid =
        fb->paid[FEEDBACK_DEC][idx] + fb->paid[FEEDBACK_IMP][idx];
    assert (fb->latest[idx] <= solver->estimator.chb.conflicts);
    age = paid ? age_bin (solver->estimator.chb.conflicts - fb->latest[idx])
               : FEEDBACK_AGE_NEVER;
    count = fb->count[idx] / fb->increment;
  } else {
    const uint64_t last = fb->last[idx];
    assert (last <= solver->estimator.rounds);
    age = last ? age_bin (solver->estimator.rounds - last)
               : FEEDBACK_AGE_NEVER;
    const double n_dec = fb->n[FEEDBACK_DEC][idx];
    const double n_imp = fb->n[FEEDBACK_IMP][idx];
    const double r_dec = fb->r[FEEDBACK_DEC][idx];
    const double r_imp = fb->r[FEEDBACK_IMP][idx];
    const double n = n_dec + n_imp;
    count = n / solver->scinc;
    double *const p = fb->frozen + FEEDBACK_PREDICTORS * idx;
    p[FEEDBACK_PREDICT_DEC] = n_dec > 0 ? r_dec / n_dec : NAN;
    p[FEEDBACK_PREDICT_IMP] = n_imp > 0 ? r_imp / n_imp : NAN;
    p[FEEDBACK_PREDICT_ALL] = n > 0 ? (r_dec + r_imp) / n : NAN;
    p[FEEDBACK_PREDICT_CONST] =
        fb->m1.sum_k ? (double) fb->m1.sum_b / fb->m1.sum_k : NAN;
  }
  fb->state[idx] = FEEDBACK_PENDING | kind << FEEDBACK_KIND_SHIFT |
                   age << FEEDBACK_AGE_SHIFT |
                   count_bin (count) << FEEDBACK_COUNT_SHIFT;
}

#ifndef QUIET

static const char *const predictor_names[2][FEEDBACK_PREDICTORS] = {
    {"dec", "imp", "all", "const"}, {"dec", "imp", "q", "const"}};
static const char *const group_names[FEEDBACK_GROUPS] = {
    "", "imp-undefined-", "dec-undefined-", "both-undefined-",
    "const-undefined-"};
static const char *const class_names[2] = {"dec", "imp"};
static const char *const kind_names[FEEDBACK_KINDS] = {"policy", "uniform"};
static const char *const age_names[FEEDBACK_AGES] = {"never", "old",
                                                     "stale", "recent"};
static const char *const count_names[FEEDBACK_COUNTS] = {
    "zero", "below1", "below5", "above5"};

static void print_count (kissat *solver, const char *prefix,
                         const char *name, uint64_t value) {
  kissat_message (solver, "%s%s %" PRIu64, prefix, name, value);
}

static void print_double (kissat *solver, const char *prefix,
                          const char *name, double value) {
  kissat_message (solver, "%s%s %.17g", prefix, name, value);
}

// The sums of a set of intervals (VSIDS) or payments (CHB): 'n', 'k' and
// 'b' or 'r', 'bumped' with 'outcomes', and the errors in 'mask'.

static void print_sums (kissat *solver, const char *prefix,
                        const feedback_sums *sums, bool chb, bool outcomes,
                        unsigned mask) {
  print_count (solver, prefix, "n", sums->n);
  if (chb)
    print_double (solver, prefix, "r", sums->r);
  else {
    print_count (solver, prefix, "k", sums->k);
    print_count (solver, prefix, "b", sums->b);
    if (outcomes)
      print_count (solver, prefix, "bumped", sums->bumped);
  }
  char name[32];
  for (unsigned i = 0; i < FEEDBACK_PREDICTORS; i++) {
    if (!(mask & BIT (i)))
      continue;
    const char *const predictor = predictor_names[chb][i];
    if (chb) {
      snprintf (name, sizeof name, "error-%s", predictor);
      print_double (solver, prefix, name, sums->interval[i]);
    } else {
      snprintf (name, sizeof name, "round-error-%s", predictor);
      print_double (solver, prefix, name, sums->round[i]);
      snprintf (name, sizeof name, "interval-error-%s", predictor);
      print_double (solver, prefix, name, sums->interval[i]);
    }
  }
}

#endif

// The 'feedback' section (see 'docs/feedback.md' for every line).  M2's
// picks still open at the end are those pending, and every pick is an
// outcome or open (checked in assertion builds).

void kissat_print_feedback_statistics (kissat *solver) {
#ifndef QUIET
  const feedback *const fb = &solver->policy.feedback;
  const bool chb = fb->started ? fb->chb : kissat_chb (solver);
  const char *const line = chb ? "chb" : "vsids";
  uint64_t open[FEEDBACK_KINDS] = {0, 0};
  if (fb->started)
    for (all_variables (idx)) {
      const unsigned state = fb->state[idx];
      if (state & FEEDBACK_PENDING)
        open[(state >> FEEDBACK_KIND_SHIFT) & 1]++;
    }
  for (unsigned kind = 0; kind < FEEDBACK_KINDS; kind++) {
    uint64_t by_age = 0, by_count = 0;
    for (unsigned i = 0; i < FEEDBACK_AGES; i++)
      by_age += fb->m2.age[kind][i].n;
    for (unsigned i = 0; i < FEEDBACK_COUNTS; i++)
      by_count += fb->m2.count[kind][i].n;
    if (by_age != by_count || fb->m2.picks[kind] != by_age + open[kind]) {
#ifndef NDEBUG
      kissat_fatal ("feedback: %" PRIu64 " %s picks, %" PRIu64 " and "
                    "%" PRIu64 " outcomes by age and count, %" PRIu64
                    " open",
                    fb->m2.picks[kind], kind_names[kind], by_age, by_count,
                    open[kind]);
#endif
    }
  }
  char prefix[96], name[32];
  kissat_section (solver, "feedback");
  snprintf (prefix, sizeof prefix, "feedback-%s-", line);
  for (unsigned c = 0; c < 2; c++) {
    snprintf (name, sizeof name, "%s-%s", chb ? "payments" : "intervals",
              class_names[c]);
    print_count (solver, prefix, name, fb->m1.intervals[c]);
  }
  if (!chb) {
    for (unsigned ended = 0; ended < 2; ended++)
      for (unsigned c = 0; c < 2; c++) {
        snprintf (name, sizeof name, "bumps-%s%s", ended ? "ended-" : "",
                  class_names[c]);
        print_count (solver, prefix, name, fb->m1.bumps[ended][c]);
      }
    print_count (solver, prefix, "bumps-unobserved", fb->m1.unobserved);
  }
  snprintf (prefix, sizeof prefix, "feedback-m1-%s-", line);
  print_count (solver, prefix, "events", fb->m1.events);
  if (!chb)
    print_count (solver, prefix, "events-k0", fb->m1.zero);
  for (unsigned g = 0; g < FEEDBACK_GROUPS; g++) {
    snprintf (prefix, sizeof prefix, "feedback-m1-%s-%s", line,
              group_names[g]);
    print_sums (solver, prefix, fb->m1.group + g, chb, false,
                group_mask[chb][g]);
  }
  for (unsigned d = 0; d < 2; d++)
    for (unsigned i = 0; i < FEEDBACK_BINS; i++) {
      snprintf (prefix, sizeof prefix, "feedback-m1-%s-calibration-%s-%u-",
                line, class_names[d], i);
      print_sums (solver, prefix, &fb->m1.calibration[d][i], chb, false, 0);
    }
  for (unsigned kind = 0; kind < FEEDBACK_KINDS; kind++) {
    snprintf (prefix, sizeof prefix, "feedback-m2-%s-%s-", line,
              kind_names[kind]);
    print_count (solver, prefix, "picks", fb->m2.picks[kind]);
    print_count (solver, prefix, "open", open[kind]);
    for (unsigned i = 0; i < FEEDBACK_AGES; i++) {
      snprintf (prefix, sizeof prefix, "feedback-m2-%s-%s-age-%s-", line,
                kind_names[kind], age_names[i]);
      print_sums (solver, prefix, &fb->m2.age[kind][i], chb, true, 0);
    }
    for (unsigned i = 0; i < FEEDBACK_COUNTS; i++) {
      snprintf (prefix, sizeof prefix, "feedback-m2-%s-%s-count-%s-", line,
                kind_names[kind], count_names[i]);
      print_sums (solver, prefix, &fb->m2.count[kind][i], chb, true, 0);
    }
  }
#ifndef NDEBUG
  kissat_message (solver, "feedback-check-complete %" PRIu64,
                  fb->check.complete);
  kissat_message (solver, "feedback-check-counts %" PRIu64,
                  fb->check.counts);
  kissat_message (solver, "feedback-check-count-error %.3g",
                  fb->check.error);
  kissat_message (solver, "feedback-check-chb-counts %" PRIu64,
                  fb->check.chb);
  kissat_message (solver, "feedback-check-payments %" PRIu64,
                  fb->check.payments);
  kissat_message (solver, "feedback-check-intervals %" PRIu64,
                  fb->check.intervals);
#endif
#else
  (void) solver;
#endif
}

#else

int kissat_feedback_dummy_to_avoid_warning;

#endif
