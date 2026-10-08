#include "intervals.h"

#ifndef HEAPARGMAX

#include "allocate.h"
#include "error.h"
#include "inline.h"
#include "inlinepolicy.h"
#include "print.h"

#include <string.h>

// The arrays, of 'size' entries each, zero beyond 'old'.

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

#define RESIZE(P) \
  (P) = resize_array (solver, (P), sizeof *(P), old_size, new_size)

void kissat_resize_intervals (kissat *solver, unsigned new_size) {
  intervals *const intervals = &solver->policy.intervals;
  if (!intervals->started)
    return;
  const unsigned old_size = intervals->size;
  if (old_size == new_size)
    return;
  RESIZE (intervals->state);
  if (intervals->increments)
    RESIZE (intervals->opened);
  if (intervals->rounds) {
    RESIZE (intervals->start);
    RESIZE (intervals->bumps);
  }
  if (solver->policy.reward.locality) {
    RESIZE (intervals->multiplier);
    for (unsigned idx = old_size; idx < new_size; idx++)
      intervals->multiplier[idx] = 1;
  }
  intervals->size = new_size;
}

#define RELEASE(P) \
  do { \
    if (P) \
      kissat_dealloc (solver, (P), size, sizeof *(P)); \
    (P) = 0; \
  } while (0)

void kissat_release_intervals (kissat *solver) {
  intervals *const intervals = &solver->policy.intervals;
  const unsigned size = intervals->size;
  RELEASE (intervals->state);
  RELEASE (intervals->opened);
  RELEASE (intervals->start);
  RELEASE (intervals->bumps);
  RELEASE (intervals->multiplier);
  RELEASE_STACK (intervals->deferred);
  intervals->size = 0;
}

// UCB on VSIDS scores counts the intervals ('keys.h'), with LRB's interval
// unless 'ucbinterval=0', feedback builds measure them, always with LRB's
// interval ('feedback.h'), LRB pays its reward at their closes, on CHB
// scores with LRB's interval ('lrb.h'), and the reward, with LRB's
// interval, weights the bumps by their classes, pays the interval reward
// with their k and b, and moves its lazy values with the multiplier
// recorded at their start ('reward.h').  The reward runs without UCB and
// the feedback build, so without the increments at assignment, and its
// closes do something only under locality or the interval reward.  A later
// search keeps the bookkeeping.

void kissat_start_intervals (kissat *solver) {
  intervals *const intervals = &solver->policy.intervals;
  if (intervals->started)
    return;
  const bool ucb = solver->policy.keys.intervals;
  const bool lrb = solver->policy.lrb.started;
  assert (!ucb || !lrb);
  const bool interval = GET_OPTION (ucbinterval);
#ifdef FEEDBACK
  if (ucb && !interval)
    kissat_fatal ("feedback builds count LRB's interval: UCB on VSIDS "
                  "scores with stage 2's count ('ucbinterval=0') needs a "
                  "build without '--feedback'");
  const bool feedback = true;
#else
  const bool feedback = false;
#endif
  const reward *const reward = &solver->policy.reward;
  if (!ucb && !feedback && !lrb && !reward->started)
    return;
  intervals->started = true;
  intervals->vsids = !kissat_chb (solver);
  intervals->increments = intervals->vsids && (ucb || feedback);
  intervals->ucb = ucb;
  intervals->lrb = lrb;
  intervals->reward =
      intervals->vsids && (reward->locality || reward->interval);
  intervals->rounds = (feedback || reward->interval) && intervals->vsids;
  intervals->interval = !ucb || interval;
  intervals->counted = 0;
  kissat_resize_intervals (solver, solver->size);
  kissat_very_verbose (solver, "assignment intervals on %s scores%s",
                       intervals->vsids ? "VSIDS" : "CHB",
                       intervals->interval ? " counting LRB's interval"
                                           : "");
}

// The users' closes: UCB's count, LRB's reward, the reward on VSIDS
// scores, and the feedback's measurements.

void kissat_close_interval (kissat *solver, unsigned idx, unsigned c,
                            unsigned how) {
  const intervals *const intervals = &solver->policy.intervals;
  assert (intervals->started);
  if (intervals->ucb)
    kissat_close_keys_interval (solver, idx, how);
  if (intervals->lrb)
    kissat_close_lrb_interval (solver, idx, c, how);
  if (intervals->reward)
    kissat_close_reward_interval (solver, idx, c, how);
#ifdef FEEDBACK
  kissat_close_feedback_interval (solver, idx, c);
#endif
}

// LRB's interval: every interval a backtrack of the current step ended
// closes now, after the step's bump round if it had one, with the class
// kept with it.  A new assignment of its variable (the asserted literal)
// keeps its mark.

void kissat_finish_deferred_intervals (kissat *solver) {
  intervals *const intervals = &solver->policy.intervals;
  assert (intervals->interval);
  assert (intervals->deferring);
  uint8_t *const state = intervals->state;
  for (all_stack (unsigned, idx, intervals->deferred)) {
    const unsigned s = state[idx];
    assert (s & INTERVALS_DEFERRED);
    assert (!(s & INTERVALS_OPEN));
    const unsigned c = (s >> INTERVALS_DEFERRED_SHIFT) & INTERVALS_CLASS;
    state[idx] = s & ~(INTERVALS_DEFERRED | INTERVALS_DEFERRED_CLASS);
    kissat_close_interval (solver, idx, c, INTERVALS_CLOSE_DEFERRED);
  }
  CLEAR_STACK (intervals->deferred);
  intervals->deferring = false;
}

// Every variable still assigned when stable mode is left closes its
// interval, and its mark goes.  Entering stable mode opens new ones.

void kissat_leave_stable_intervals (kissat *solver) {
  intervals *const intervals = &solver->policy.intervals;
  if (!intervals->started)
    return;
  assert (solver->stable);
  assert (!intervals->analyzing);
  kissat_record_intervals (solver);
  uint8_t *const state = intervals->state;
  const flags *const flags = solver->flags;
  const unsigned *const begin = BEGIN_ARRAY (solver->trail);
  const unsigned *const end = END_ARRAY (solver->trail);
  for (const unsigned *p = begin; p != end; p++) {
    const unsigned idx = IDX (*p);
    if (!flags[idx].active)
      continue;
    const unsigned s = state[idx];
    state[idx] = 0;
    if (s & INTERVALS_OPEN)
      kissat_close_interval (solver, idx, s & INTERVALS_CLASS,
                             INTERVALS_CLOSE_LEFT);
  }
}

void kissat_rescale_intervals (kissat *solver, double factor) {
  intervals *const intervals = &solver->policy.intervals;
  assert (intervals->started);
  if (!intervals->increments)
    return;
  kissat_record_intervals (solver);
  double *const opened = intervals->opened;
  for (all_variables (idx))
    opened[idx] *= factor;
  if (intervals->ucb)
    kissat_rescale_keys (solver, factor);
#ifdef FEEDBACK
  kissat_rescale_feedback (solver, factor);
#endif
}

#else

int kissat_intervals_dummy_to_avoid_warning;

#endif
