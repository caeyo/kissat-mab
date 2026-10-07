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
  RESIZE (fb->yield, 1);
  RESIZE (fb->propagated, 1);
  RESIZE (fb->observed, 1);
#ifndef NDEBUG
  RESIZE (fb->check.propagated, 1);
  RESIZE (fb->check.observed, 1);
#endif
  if (fb->chb) {
    RESIZE (fb->reward, 1);
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
  RELEASE (fb->yield, 1);
  RELEASE (fb->propagated, 1);
  RELEASE (fb->observed, 1);
  RELEASE (fb->reward, 1);
#ifndef NDEBUG
  RELEASE (fb->check.rounds, 1);
  RELEASE (fb->check.bumped, 1);
  RELEASE (fb->check.marked, 1);
  RELEASE (fb->check.propagated, 1);
  RELEASE (fb->check.observed, 1);
  RELEASE_STACK (fb->check.listed);
  RELEASE_STACK (fb->check.staged);
  RELEASE_STACK (fb->check.levels);
#endif
  RELEASE_STACK (fb->deferred);
  RELEASE_STACK (fb->staged);
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
  fb->yield[to] = fb->yield[from];
  fb->propagated[to] = fb->propagated[from];
  fb->observed[to] = fb->observed[from];
  if (fb->yielding == from + 1)
    fb->yielding = to + 1;
#ifndef NDEBUG
  fb->check.propagated[to] = fb->check.propagated[from];
  fb->check.observed[to] = fb->check.observed[from];
#endif
  if (fb->chb) {
    fb->reward[to] = fb->reward[from];
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
  fb->yield[idx] = 0;
  fb->propagated[idx] = 0;
  fb->observed[idx] = 0;
  if (fb->yielding == idx + 1)
    fb->yielding = 0;
#ifndef NDEBUG
  fb->check.propagated[idx] = 0;
  fb->check.observed[idx] = 0;
#endif
  if (fb->chb) {
    fb->reward[idx] = 0;
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

// M3: the bin of 'Y_v', which is at least one once defined.

static unsigned yield_bin (double yield) {
  if (!(yield > 0))
    return FEEDBACK_YIELD_NONE;
  if (yield < 2)
    return FEEDBACK_YIELD_BELOW2;
  if (yield < 4)
    return FEEDBACK_YIELD_BELOW4;
  if (yield < 16)
    return FEEDBACK_YIELD_BELOW16;
  if (yield < 64)
    return FEEDBACK_YIELD_BELOW64;
  return FEEDBACK_YIELD_ABOVE64;
}

// M3: the pending pick of 'idx' is done with, its 'y_prop' and 'y_obs'
// reset.  A pick taken back is taken back from M3's picks as well.

static void reset_yield (feedback *fb, unsigned idx) {
  fb->propagated[idx] = 0;
  fb->observed[idx] = 0;
  if (fb->chb)
    fb->reward[idx] = 0;
  if (fb->yielding == idx + 1)
    fb->yielding = 0;
#ifndef NDEBUG
  fb->check.propagated[idx] = 0;
  fb->check.observed[idx] = 0;
#endif
}

static void void_yield (feedback *fb, unsigned idx, unsigned state) {
  assert (state & FEEDBACK_YIELD);
  const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
  assert (fb->m3.picks[kind]);
  fb->m3.picks[kind]--;
  reset_yield (fb, idx);
}

#ifndef NDEBUG

// Check (c) of M3: 'y_prop' and 'y_obs' against their shadow sums, counted
// from the trail.

static void check_yield (kissat *solver, unsigned idx, unsigned prop,
                         uint64_t obs) {
  feedback *const fb = &solver->policy.feedback;
  const unsigned counted_prop = fb->check.propagated[idx];
  const uint64_t counted_obs = fb->check.observed[idx];
  if (counted_prop != prop || counted_obs != obs)
    kissat_fatal ("feedback: pick of variable %u closed with y_prop %u "
                  "and y_obs %" PRIu64 ", but %u and %" PRIu64
                  " counted from the trail",
                  idx, prop, obs, counted_prop, counted_obs);
  fb->check.yields++;
}

#endif

// M3: the interval of the pending pick of 'idx' closed, with M2's outcome,
// 'k' and 'b' (VSIDS) or the payment 'reward' (CHB): its sums by age, by
// count and by the bin of 'Y_v' frozen at the pick, and for a uniform pick
// by that bin crossed with stale against recent.  Then 'Y_v' takes its
// 'y_prop', or starts from it.  A pick whose propagation's end was not
// seen, which only the unit tests make, is taken back.

static void add_yield (kissat *solver, unsigned idx, unsigned state,
                       uint64_t k, uint64_t b, double reward) {
  feedback *const fb = &solver->policy.feedback;
  assert (state & FEEDBACK_YIELD);
  const unsigned prop = fb->propagated[idx];
  const uint64_t obs = fb->observed[idx];
  if (!prop) {
    void_yield (fb, idx, state);
    return;
  }
#ifndef NDEBUG
  check_yield (solver, idx, prop, obs);
#endif
  reset_yield (fb, idx);
  const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
  const unsigned age = (state >> FEEDBACK_AGE_SHIFT) & 3;
  const unsigned count = (state >> FEEDBACK_COUNT_SHIFT) & 3;
  const unsigned bin = (state >> FEEDBACK_YIELD_SHIFT) & 7;
  assert (bin < FEEDBACK_YIELDS);
  feedback_yields *sums[4] = {&fb->m3.age[kind][age],
                              &fb->m3.count[kind][count],
                              &fb->m3.yield[kind][bin], 0};
  if (kind == FEEDBACK_UNIFORM)
    sums[3] = &fb->m3.crossed[age == FEEDBACK_AGE_RECENT][bin];
  for (unsigned i = 0; i < 4; i++) {
    feedback_yields *const s = sums[i];
    if (!s)
      continue;
    s->n++;
    s->k += k;
    s->b += b;
    s->bumped += b > 0;
    s->r += reward;
    s->prop += prop;
    s->obs += obs;
  }
  double *const yield = fb->yield + idx;
  const double alpha = FEEDBACK_YIELD_ALPHA;
  *yield = *yield > 0 ? (1 - alpha) * *yield + alpha * prop : prop;
}

// M3: when an analysis step starts, before its backtracks, every open
// pick's level with its variables now, and their trail segments, to be
// added when the step's analyzed variables are bumped or recorded.  A
// level's variables are its frame's count, which chronological
// backtracking may leave below its trail segment, or above.  Assertion
// builds count every level's variables from the trail and hold the
// frames' counts to them.

static void stage_yields (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  CLEAR_STACK (fb->staged);
  const unsigned level = solver->level;
  const unsigned size = SIZE_ARRAY (solver->trail);
  const uint16_t *const state = fb->state;
  uint64_t levels = 0, segments = 0;
  for (unsigned l = 1; l <= level; l++) {
    const frame *const frame = &FRAME (l);
    const unsigned idx = IDX (frame->decision);
    if (!(state[idx] & FEEDBACK_YIELD))
      continue;
    assert (solver->assigned[idx].level == l);
    const unsigned end = l < level ? FRAME (l + 1).trail : size;
    assert (frame->trail <= end);
    PUSH_STACK (fb->staged, idx);
    PUSH_STACK (fb->staged, frame->assigned);
    levels += frame->assigned;
    segments += end - frame->trail;
  }
  fb->staged_levels = levels;
  fb->staged_segments = segments;
#ifndef NDEBUG
  unsigneds *const counted = &fb->check.levels;
  CLEAR_STACK (*counted);
  for (unsigned l = 0; l <= level; l++)
    PUSH_STACK (*counted, 0);
  unsigned *const count = BEGIN_STACK (*counted);
  const assigned *const assigned = solver->assigned;
  for (all_stack (unsigned, lit, solver->trail)) {
    const unsigned l = assigned[IDX (lit)].level;
    assert (l <= level);
    count[l]++;
  }
  CLEAR_STACK (fb->check.staged);
  for (unsigned l = 1; l <= level; l++) {
    const frame *const frame = &FRAME (l);
    if (count[l] != frame->assigned)
      kissat_fatal ("feedback: %u variables assigned at level %u, %u "
                    "counted from the trail",
                    frame->assigned, l, count[l]);
    fb->check.steps++;
    const unsigned idx = IDX (frame->decision);
    if (!(state[idx] & FEEDBACK_YIELD))
      continue;
    PUSH_STACK (fb->check.staged, idx);
    PUSH_STACK (fb->check.staged, count[l]);
  }
#endif
}

// M3: a step's analyzed variables are bumped (VSIDS) or recorded as CHB's
// participants (CHB), so the step is a conflict of every open pick's
// interval, which observes its level's variables taken when the step
// started.  Outside a step, which only the unit tests make, they are
// taken now.

void kissat_feedback_observe (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (solver->stable);
  if (!fb->analyzing)
    stage_yields (solver);
  uint64_t *const observed = fb->observed;
  const unsigned *const end = END_STACK (fb->staged);
  for (const unsigned *p = BEGIN_STACK (fb->staged); p != end; p += 2)
    observed[p[0]] += p[1];
  CLEAR_STACK (fb->staged);
  fb->m3.levels += fb->staged_levels;
  fb->m3.segments += fb->staged_segments;
  fb->staged_levels = fb->staged_segments = 0;
#ifndef NDEBUG
  uint64_t *const counted = fb->check.observed;
  const unsigned *const check_end = END_STACK (fb->check.staged);
  for (const unsigned *p = BEGIN_STACK (fb->check.staged); p != check_end;
       p += 2)
    counted[p[0]] += p[1];
  CLEAR_STACK (fb->check.staged);
#endif
}

// M3: a search propagation ends.  If it is the one that follows a pick,
// the pick's 'y_prop' is its level's trail segment, which holds only that
// level, since every variable it assigned has the decision's level.

void kissat_feedback_propagated (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  const unsigned yielding = fb->yielding;
  if (!yielding)
    return;
  fb->yielding = 0;
  const unsigned idx = yielding - 1;
  assert (fb->started);
  assert (solver->stable);
  assert (fb->state[idx] & FEEDBACK_YIELD);
  const unsigned level = solver->level;
  const frame *const frame = &FRAME (level);
  assert (IDX (frame->decision) == idx);
  assert (solver->assigned[idx].level == level);
  const unsigned prop = SIZE_ARRAY (solver->trail) - frame->trail;
  assert (prop == frame->assigned);
  assert (prop >= 1);
  fb->propagated[idx] = prop;
#ifndef NDEBUG
  unsigned counted = 0;
  const assigned *const assigned = solver->assigned;
  for (all_stack (unsigned, lit, solver->trail))
    counted += assigned[IDX (lit)].level == level;
  fb->check.propagated[idx] = counted;
#endif
}

// VSIDS line: the interval of the active variable 'idx', of class 'c',
// closes: at its unassignment in stable mode, after the bump round of the
// analysis step whose backtrack ended it, or when stable mode is left.
// Its rounds go to the count of its class, as UCB's do; a decided interval
// adds to the sums of p_const; the interval of a pending pick is an event
// of M1 and the pick's outcome in M2 and M3.  Every variable on the trail
// has its interval open when it closes, except in the unit tests, which
// assign some variables off the trail; for those there is nothing to
// close.

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
  assert (!(state & FEEDBACK_YIELD) == !(state & FEEDBACK_PENDING));
  if (state & FEEDBACK_PENDING && c != FEEDBACK_DEC) {
    void_pick (fb, state);
    void_yield (fb, idx, state);
  } else if (state & FEEDBACK_PENDING) {
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
    add_yield (solver, idx, state, k, b, 0);
  }
  fb->state[idx] = 0;
  fb->opened[idx] = inc;
  fb->start[idx] = round;
  fb->bumps[idx] = 0;
}

// CHB line: the interval of the pending pick of 'idx' closes, for M3: at
// its unassignment in stable mode, at the end of the analysis step whose
// backtrack ended it, or when stable mode is left.  M2's outcome, its
// payment, came at the propagation after the pick; a pick without one,
// which only the unit tests make, is taken back from M2 and M3.

static void close_yield (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  assert (fb->chb);
  const unsigned state = fb->state[idx];
  assert (state & FEEDBACK_YIELD);
  if (state & FEEDBACK_PENDING) {
    void_pick (fb, state);
    void_yield (fb, idx, state);
  } else
    add_yield (solver, idx, state, 0, 0, fb->reward[idx]);
  fb->state[idx] = 0;
}

// Stable-mode backtracking unassigned 'idx'.  Inside an analysis step the
// close waits for the step's bump round, or its end (LRB's interval), and
// on the CHB line M3's close for the step's end.

void kissat_feedback_unassign (kissat *solver, unsigned idx) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (solver->stable);
  if (fb->chb) {
    uint16_t *const state = fb->state + idx;
    if (!(*state & FEEDBACK_YIELD))
      return;
    if (!fb->analyzing) {
      close_yield (solver, idx);
      return;
    }
    assert (!(*state & FEEDBACK_CLOSING));
    *state |= FEEDBACK_CLOSING;
    PUSH_STACK (fb->deferred, idx);
    fb->deferring = true;
    return;
  }
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
// round counter of now: after its bump round, they count it.  On the CHB
// line M3's picks deferred to the step's end close, after its conflict.

static void finish_deferred (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  assert (fb->deferring);
  for (all_stack (unsigned, idx, fb->deferred)) {
    const unsigned state = fb->state[idx];
    if (fb->chb) {
      assert (state & FEEDBACK_CLOSING);
      close_yield (solver, idx);
      continue;
    }
    assert (state & FEEDBACK_DEFERRED);
    const unsigned c =
        state & FEEDBACK_DEFERRED_IMP ? FEEDBACK_IMP : FEEDBACK_DEC;
    close_interval (solver, idx, c);
  }
  CLEAR_STACK (fb->deferred);
  fb->deferring = false;
}

// A step of conflict analysis starts, before its backtracks.  M3 takes the
// open picks' levels and their variables, on both lines.  On the VSIDS
// line assertion builds list the active variables assigned now, which the
// step's bump round observes.

void kissat_feedback_begin_analysis (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->started || !solver->stable)
    return;
  assert (!fb->analyzing), assert (!fb->deferring);
  assert (EMPTY_STACK (fb->deferred));
  fb->analyzing = true;
  stage_yields (solver);
#ifndef NDEBUG
  if (fb->chb)
    return;
  unsigneds *const listed = &fb->check.listed;
  CLEAR_STACK (*listed);
  const flags *const flags = solver->flags;
  for (all_stack (unsigned, lit, solver->trail))
    if (flags[IDX (lit)].active)
      PUSH_STACK (*listed, IDX (lit));
#endif
}

// The step ends, after its bump round if it had one: closes still deferred
// (no round) happen now, without a round, and M3's levels taken at its
// start are dropped if its analyzed variables were neither bumped nor
// recorded.

void kissat_feedback_end_analysis (kissat *solver) {
  feedback *const fb = &solver->policy.feedback;
  if (!fb->analyzing)
    return;
  CLEAR_STACK (fb->staged);
  fb->staged_levels = fb->staged_segments = 0;
#ifndef NDEBUG
  CLEAR_STACK (fb->check.staged);
#endif
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
// interval, and on the CHB line every pick still pending in M3.  Entering
// stable mode opens one for every assigned variable at the next record.

void kissat_leave_stable_feedback (kissat *solver) {
  const feedback *const fb = &solver->policy.feedback;
  if (!fb->started)
    return;
  assert (solver->stable);
  assert (!fb->analyzing);
  assert (!fb->yielding);
  if (fb->chb) {
    for (all_stack (unsigned, lit, solver->trail))
      if (fb->state[IDX (lit)] & FEEDBACK_YIELD)
        close_yield (solver, IDX (lit));
    return;
  }
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
// pick of the variable has its outcome in M2, which M3 keeps until the
// pick's interval closes.

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
    assert (state & FEEDBACK_YIELD);
    if (c == FEEDBACK_DEC) {
      add_outcome (fb, state, 0, 0, reward);
      fb->reward[idx] = reward;
      fb->state[idx] = state & ~FEEDBACK_PENDING;
    } else {
      void_pick (fb, state);
      void_yield (fb, idx, state);
      fb->state[idx] = 0;
    }
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
// of p_const do not change before its interval opens.  For M3 it is
// pending until its interval closes, with the bin of 'Y_v', and awaits the
// end of the propagation that follows its decision.

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
  if (old_state & FEEDBACK_YIELD)
    void_yield (fb, idx, old_state);
  assert (!fb->propagated[idx]), assert (!fb->observed[idx]);
  const unsigned kind = uniform ? FEEDBACK_UNIFORM : FEEDBACK_POLICY;
  fb->m2.picks[kind]++;
  fb->m3.picks[kind]++;
  fb->yielding = idx + 1;
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
                   count_bin (count) << FEEDBACK_COUNT_SHIFT |
                   FEEDBACK_YIELD |
                   yield_bin (fb->yield[idx]) << FEEDBACK_YIELD_SHIFT;
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
static const char *const yield_names[FEEDBACK_YIELDS] = {
    "none", "below2", "below4", "below16", "below64", "above64"};
static const char *const cross_names[2] = {"stale", "recent"};

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

// M3's sums of a set of picks: 'n', M2's outcome with 'outcomes' ('k', 'b'
// and 'bumped', or 'r'), and the sums of 'y_prop' and 'y_obs'.

static void print_yields (kissat *solver, const char *prefix,
                          const feedback_yields *sums, bool chb,
                          bool outcomes) {
  print_count (solver, prefix, "n", sums->n);
  if (outcomes && chb)
    print_double (solver, prefix, "r", sums->r);
  else if (outcomes) {
    print_count (solver, prefix, "k", sums->k);
    print_count (solver, prefix, "b", sums->b);
    print_count (solver, prefix, "bumped", sums->bumped);
  }
  print_count (solver, prefix, "prop", sums->prop);
  print_count (solver, prefix, "obs", sums->obs);
}

#endif

// The 'feedback' section (see 'docs/feedback.md' for every line).  M2's
// and M3's picks still open at the end are those pending, and every pick
// is an outcome or open; M3's outcomes by age, by count and by the bin of
// 'Y_v' are the same, and its uniform outcomes crossed with stale against
// recent are its uniform outcomes by that bin (checked in assertion
// builds).

void kissat_print_feedback_statistics (kissat *solver) {
#ifndef QUIET
  const feedback *const fb = &solver->policy.feedback;
  const bool chb = fb->started ? fb->chb : kissat_chb (solver);
  const char *const line = chb ? "chb" : "vsids";
  uint64_t open[FEEDBACK_KINDS] = {0, 0};
  uint64_t yielding[FEEDBACK_KINDS] = {0, 0};
  if (fb->started)
    for (all_variables (idx)) {
      const unsigned state = fb->state[idx];
      const unsigned kind = (state >> FEEDBACK_KIND_SHIFT) & 1;
      if (state & FEEDBACK_PENDING)
        open[kind]++;
      if (state & FEEDBACK_YIELD)
        yielding[kind]++;
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
    uint64_t m3_age = 0, m3_count = 0, m3_yield = 0;
    for (unsigned i = 0; i < FEEDBACK_AGES; i++)
      m3_age += fb->m3.age[kind][i].n;
    for (unsigned i = 0; i < FEEDBACK_COUNTS; i++)
      m3_count += fb->m3.count[kind][i].n;
    for (unsigned i = 0; i < FEEDBACK_YIELDS; i++)
      m3_yield += fb->m3.yield[kind][i].n;
    if (m3_age != m3_count || m3_age != m3_yield ||
        fb->m3.picks[kind] != m3_age + yielding[kind]) {
#ifndef NDEBUG
      kissat_fatal ("feedback: M3: %" PRIu64 " %s picks, %" PRIu64
                    ", %" PRIu64 " and %" PRIu64 " outcomes by age, count "
                    "and yield, %" PRIu64 " open",
                    fb->m3.picks[kind], kind_names[kind], m3_age, m3_count,
                    m3_yield, yielding[kind]);
#endif
    }
  }
  for (unsigned i = 0; i < FEEDBACK_YIELDS; i++) {
    const feedback_yields *const all = &fb->m3.yield[FEEDBACK_UNIFORM][i];
    const feedback_yields *const stale = &fb->m3.crossed[0][i];
    const feedback_yields *const recent = &fb->m3.crossed[1][i];
    if (all->n != stale->n + recent->n ||
        all->prop != stale->prop + recent->prop ||
        all->obs != stale->obs + recent->obs) {
#ifndef NDEBUG
      kissat_fatal ("feedback: M3: %" PRIu64 " uniform outcomes of yield "
                    "%s, %" PRIu64 " stale and %" PRIu64 " recent",
                    all->n, yield_names[i], stale->n, recent->n);
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
  for (unsigned kind = 0; kind < FEEDBACK_KINDS; kind++) {
    snprintf (prefix, sizeof prefix, "feedback-m3-%s-%s-", line,
              kind_names[kind]);
    print_count (solver, prefix, "picks", fb->m3.picks[kind]);
    print_count (solver, prefix, "open", yielding[kind]);
    for (unsigned i = 0; i < FEEDBACK_AGES; i++) {
      snprintf (prefix, sizeof prefix, "feedback-m3-%s-%s-age-%s-", line,
                kind_names[kind], age_names[i]);
      print_yields (solver, prefix, &fb->m3.age[kind][i], chb, false);
    }
    for (unsigned i = 0; i < FEEDBACK_COUNTS; i++) {
      snprintf (prefix, sizeof prefix, "feedback-m3-%s-%s-count-%s-", line,
                kind_names[kind], count_names[i]);
      print_yields (solver, prefix, &fb->m3.count[kind][i], chb, false);
    }
    for (unsigned i = 0; i < FEEDBACK_YIELDS; i++) {
      snprintf (prefix, sizeof prefix, "feedback-m3-%s-%s-yield-%s-", line,
                kind_names[kind], yield_names[i]);
      print_yields (solver, prefix, &fb->m3.yield[kind][i], chb, true);
    }
  }
  for (unsigned recent = 0; recent < 2; recent++)
    for (unsigned i = 0; i < FEEDBACK_YIELDS; i++) {
      snprintf (prefix, sizeof prefix, "feedback-m3-%s-uniform-%s-yield-%s-",
                line, cross_names[recent], yield_names[i]);
      print_yields (solver, prefix, &fb->m3.crossed[recent][i], chb, true);
    }
  snprintf (prefix, sizeof prefix, "feedback-m3-%s-", line);
  print_count (solver, prefix, "obs-levels", fb->m3.levels);
  print_count (solver, prefix, "obs-segments", fb->m3.segments);
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
  kissat_message (solver, "feedback-check-levels %" PRIu64,
                  fb->check.steps);
  kissat_message (solver, "feedback-check-yields %" PRIu64,
                  fb->check.yields);
#endif
#else
  (void) solver;
#endif
}

#else

int kissat_feedback_dummy_to_avoid_warning;

#endif
