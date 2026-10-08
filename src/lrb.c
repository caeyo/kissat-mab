#include "lrb.h"

#ifndef HEAPARGMAX

#include "allocate.h"
#include "chb.h"
#include "error.h"
#include "inline.h"
#include "inlinepolicy.h"
#include "intervals.h"
#include "logging.h"
#include "print.h"

#include <inttypes.h>
#include <limits.h>
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

static void close_all (uint64_t *start, unsigned begin, unsigned end) {
  for (unsigned idx = begin; idx < end; idx++)
    start[idx] = LRB_CLOSED;
}

void kissat_resize_lrb (kissat *solver, unsigned new_size) {
  lrb *const lrb = &solver->policy.lrb;
  if (!lrb->started)
    return;
  const unsigned old_size = lrb->size;
  if (old_size == new_size)
    return;
  RESIZE (lrb->start);
  RESIZE (lrb->participated);
  RESIZE (lrb->reasoned);
  close_all (lrb->start, old_size, new_size);
#ifndef NDEBUG
  RESIZE (lrb->check.start);
  RESIZE (lrb->check.participations);
  RESIZE (lrb->check.reasons);
  RESIZE (lrb->check.participations_at);
  RESIZE (lrb->check.reasons_at);
  RESIZE (lrb->check.decided);
  close_all (lrb->check.start, old_size, new_size);
#endif
  lrb->size = new_size;
}

#define RELEASE(P) \
  do { \
    if (P) \
      kissat_dealloc (solver, (P), size, sizeof *(P)); \
    (P) = 0; \
  } while (0)

void kissat_release_lrb (kissat *solver) {
  lrb *const lrb = &solver->policy.lrb;
  const unsigned size = lrb->size;
  RELEASE (lrb->start);
  RELEASE (lrb->participated);
  RELEASE (lrb->reasoned);
#ifndef NDEBUG
  RELEASE (lrb->check.start);
  RELEASE (lrb->check.participations);
  RELEASE (lrb->check.reasons);
  RELEASE (lrb->check.participations_at);
  RELEASE (lrb->check.reasons_at);
  RELEASE (lrb->check.decided);
#endif
  lrb->size = 0;
}

// LRB feeds CHB's ERWA and decides by Argmax over it (see 'lrb.h').

void kissat_start_lrb (kissat *solver) {
  lrb *const lrb = &solver->policy.lrb;
  if (lrb->started) {
    close_all (lrb->start, 0, lrb->size);
#ifndef NDEBUG
    close_all (lrb->check.start, 0, lrb->size);
#endif
    return;
  }
  if (!kissat_lrb (solver))
    return;
  if (!kissat_chb (solver))
    kissat_fatal ("'lrb' feeds CHB's ERWA: it needs 'chb=1'");
  if (GET_OPTION (softmax) || GET_OPTION (perturbed) ||
      GET_OPTION (thompson) || GET_OPTION (ucb) || GET_OPTION (gammappm))
    kissat_fatal ("'lrb' decides by Argmax: 'softmax', 'perturbed', "
                  "'thompson', 'ucb' and 'gammappm' must be zero");
  lrb->started = true;
  lrb->boundary = LRB_NO_BOUNDARY;
#ifndef NDEBUG
  lrb->check.boundary = LRB_NO_BOUNDARY;
#endif
  kissat_resize_lrb (solver, solver->size);
  kissat_very_verbose (solver, "LRB's reward on CHB's ERWA");
}

#ifndef NDEBUG

// The checks of assertion builds (see 'lrb.h').  The walk's record: the
// check's own start, and the log's counts then.

static void check_open (kissat *solver, unsigned idx, uint64_t conflicts) {
  lrb *const lrb = &solver->policy.lrb;
  if (lrb->check.start[idx] != LRB_CLOSED)
    kissat_fatal ("LRB check: the walk opens an interval of variable %u "
                  "at conflict %" PRIu64 " while the one opened at %" PRIu64
                  " is open",
                  idx, conflicts, lrb->check.start[idx]);
  lrb->check.start[idx] = conflicts;
  lrb->check.participations_at[idx] = lrb->check.participations[idx];
  lrb->check.reasons_at[idx] = lrb->check.reasons[idx];
  lrb->check.decided[idx] =
      solver->assigned[idx].reason == DECISION_REASON;
}

void kissat_check_lrb_boundary (kissat *solver) {
  lrb *const lrb = &solver->policy.lrb;
  if (lrb->started && solver->stable)
    lrb->check.boundary = SIZE_STACK (solver->analyzed);
}

// The log: a pass of its own over the step's analyzed set, split at the
// boundary taken before the reason-side pass was called.

static void check_analyzed (kissat *solver) {
  lrb *const lrb = &solver->policy.lrb;
  const size_t boundary = lrb->check.boundary;
  lrb->check.boundary = LRB_NO_BOUNDARY;
  size_t position = 0;
  for (all_stack (unsigned, idx, solver->analyzed)) {
    if (ACTIVE (idx)) {
      if (position < boundary) {
        lrb->check.participations[idx]++;
        lrb->check.logged[0]++;
      } else {
        lrb->check.reasons[idx]++;
        lrb->check.logged[1]++;
      }
    }
    position++;
  }
}

// A close against the log: the interval from the walk's conflict count,
// the participations of either kind since the walk, and the reward.  A
// close inside an analysis step is a deferred one, at the step's end,
// after its record of participants, and every other close is outside.
// Returns the log's reward, and its class at the walk in 'decided'.

static double check_close (kissat *solver, unsigned idx, unsigned how,
                           uint64_t interval, unsigned participated,
                           unsigned reasoned, double reward,
                           bool *decided) {
  lrb *const lrb = &solver->policy.lrb;
  const bool analyzing = solver->policy.intervals.analyzing;
  if (analyzing != (how == INTERVALS_CLOSE_DEFERRED))
    kissat_fatal ("LRB check: interval of variable %u closes %s an "
                  "analysis step, but %s",
                  idx, analyzing ? "inside" : "outside",
                  how == INTERVALS_CLOSE_DEFERRED ? "deferred"
                                                  : "not deferred");
  const uint64_t start = lrb->check.start[idx];
  if (start == LRB_CLOSED)
    kissat_fatal ("LRB check: interval of variable %u closes, but the walk "
                  "opened none",
                  idx);
  lrb->check.start[idx] = LRB_CLOSED;
  const uint64_t conflicts = solver->estimator.chb.conflicts;
  const uint64_t expected = conflicts - start;
  const uint64_t p =
      lrb->check.participations[idx] - lrb->check.participations_at[idx];
  const uint64_t q = lrb->check.reasons[idx] - lrb->check.reasons_at[idx];
  const double r = expected ? (double) (p + q) / (double) expected : 0;
  if (expected != interval || p != participated || q != reasoned ||
      !kissat_same_double (r, reward))
    kissat_fatal ("LRB check: interval of variable %u closes after %" PRIu64
                  " conflicts with %u participations and %u reason-side "
                  "ones, reward %.17g, where the log has %" PRIu64
                  ", %" PRIu64 ", %" PRIu64 " and %.17g (conflict %" PRIu64
                  ")",
                  idx, interval, participated, reasoned, reward, expected,
                  p, q, r, conflicts);
  lrb->check.closes++;
  *decided = lrb->check.decided[idx];
  return r;
}

// Under the reward's channel weighting (see 'reward.h') the class of a
// paid close against the reason at the walk, and its step against the
// weighting's, bitwise.

static void check_step (kissat *solver, unsigned idx, unsigned c,
                        bool decided, double alpha, double step) {
  const reward *const reward = &solver->policy.reward;
  if (decided != (c == INTERVALS_DECIDED))
    kissat_fatal ("LRB check: interval of variable %u closes in class %u "
                  "but its reason at the walk was %sa decision",
                  idx, c, decided ? "" : "not ");
  const double expected =
      kissat_lrb_weighted_step (alpha, decided, reward->wimp);
  if (!kissat_same_double (expected, step))
    kissat_fatal ("LRB check: interval of variable %u closes with step "
                  "%.17g, where its class gives %.17g",
                  idx, step, expected);
  solver->policy.reward.check.updates++;
}

#endif

void kissat_lrb_assign (kissat *solver, unsigned played, unsigned size,
                        uint64_t conflicts) {
  lrb *const lrb = &solver->policy.lrb;
  assert (lrb->started);
  assert (solver->stable);
  const unsigned *const trail = BEGIN_ARRAY (solver->trail);
  const flags *const flags = solver->flags;
  uint64_t *const start = lrb->start;
  unsigned *const participated = lrb->participated;
  unsigned *const reasoned = lrb->reasoned;
  uint64_t opened = 0;
  for (unsigned i = played; i < size; i++) {
    const unsigned idx = IDX (trail[i]);
    if (!flags[idx].active)
      continue;
    assert (start[idx] == LRB_CLOSED);
    start[idx] = conflicts;
    participated[idx] = reasoned[idx] = 0;
    LOG ("LRB opens the interval of %s at conflict %" PRIu64,
         LOGVAR (idx), conflicts);
#ifndef NDEBUG
    check_open (solver, idx, conflicts);
#endif
    opened++;
  }
  lrb->count.opened += opened;
}

void kissat_lrb_analyzed (kissat *solver) {
  lrb *const lrb = &solver->policy.lrb;
  assert (lrb->started);
  assert (solver->stable);
  const size_t size = SIZE_STACK (solver->analyzed);
  const size_t boundary = lrb->boundary;
  lrb->boundary = LRB_NO_BOUNDARY;
  assert (boundary == LRB_NO_BOUNDARY || boundary <= size);
  const size_t participants = boundary < size ? boundary : size;
  const unsigned *const analyzed = BEGIN_STACK (solver->analyzed);
  const flags *const flags = solver->flags;
  unsigned *const participated = lrb->participated;
  unsigned *const reasoned = lrb->reasoned;
  uint64_t counted = 0, reasons = 0;
  for (size_t i = 0; i < participants; i++) {
    const unsigned idx = analyzed[i];
    if (!flags[idx].active)
      continue;
    assert (participated[idx] < UINT_MAX);
    participated[idx]++;
    counted++;
  }
  for (size_t i = participants; i < size; i++) {
    const unsigned idx = analyzed[i];
    if (!flags[idx].active)
      continue;
    assert (reasoned[idx] < UINT_MAX);
    reasoned[idx]++;
    reasons++;
  }
  lrb->count.participations += counted;
  lrb->count.reasons += reasons;
  reward *const reward = &solver->policy.reward;
  if (reward->locality)
    reward->decay = true; // the step decays (see 'reward.h')
#ifndef NDEBUG
  check_analyzed (solver);
#endif
}

// The reward's locality (see 'reward.h'): Q of an interval closing, from
// the stored value, which its start's multiplier g_a scales, and the stored
// value of 'q' now, which g scales.  Without locality both are Q.

static double true_q (kissat *solver, unsigned idx) {
  const double score = solver->score[idx];
  if (!solver->policy.reward.locality)
    return score;
  return score / solver->policy.intervals.multiplier[idx];
}

static void store_q (kissat *solver, unsigned idx, double q) {
  const reward *const reward = &solver->policy.reward;
  const double score = reward->locality ? q * reward->g : q;
  if (VALUE (LIT (idx)))
    kissat_update_assigned_score (solver, idx, score);
  else
    kissat_update_score (solver, idx, score);
}

// Under the reward's locality a close that pays nothing still moves the
// stored value from g_a to g (see 'reward.h'), and the update of a paid
// one uses Q over g_a and stores the new Q times g; its channel weighting
// scales the step by the interval's class 'c'.

void kissat_close_lrb_interval (kissat *solver, unsigned idx, unsigned c,
                                unsigned how) {
  lrb *const lrb = &solver->policy.lrb;
  reward *const reward = &solver->policy.reward;
  assert (lrb->started);
  assert (how < sizeof lrb->count.closed / sizeof *lrb->count.closed);
  uint64_t *const p = lrb->start + idx;
  const uint64_t start = *p;
  if (start == LRB_CLOSED) {
#ifndef NDEBUG
    if (lrb->check.start[idx] != LRB_CLOSED)
      kissat_fatal ("LRB check: interval of variable %u is closed, but "
                    "the walk opened one at %" PRIu64,
                    idx, lrb->check.start[idx]);
#endif
    lrb->count.ignored++;
    if (reward->locality)
      store_q (solver, idx, true_q (solver, idx));
#ifdef FEEDBACK
    kissat_feedback_lrb_close (solver, FEEDBACK_LRB_IGNORED, 0, 0);
#endif
    return;
  }
  *p = LRB_CLOSED;
  lrb->count.closed[how]++;
  const uint64_t conflicts = solver->estimator.chb.conflicts;
  assert (start <= conflicts);
  const uint64_t interval = conflicts - start;
  const unsigned participated = lrb->participated[idx];
  const unsigned reasoned = lrb->reasoned[idx];
  const uint64_t participations = (uint64_t) participated + reasoned;
  const double r =
      interval ? (double) participations / (double) interval : 0;
#ifndef NDEBUG
  bool decided;
  const double logged = check_close (solver, idx, how, interval,
                                     participated, reasoned, r, &decided);
#endif
  if (!interval) {
    LOG ("LRB closes the interval of %s without a conflict", LOGVAR (idx));
    lrb->count.skipped++;
    if (reward->locality)
      store_q (solver, idx, true_q (solver, idx));
#ifdef FEEDBACK
    kissat_feedback_lrb_close (solver, FEEDBACK_LRB_SKIPPED, 0, 0);
#endif
    return;
  }
  double alpha = kissat_chb_alpha (conflicts);
  if (reward->started) {
#ifndef NDEBUG
    const double unweighted = alpha;
#endif
    if (reward->weighted)
      alpha = kissat_lrb_weighted_step (alpha, c == INTERVALS_DECIDED,
                                        reward->wimp);
#ifndef NDEBUG
    if (reward->weighted)
      check_step (solver, idx, c, decided, unweighted, alpha);
    if (reward->locality)
      kissat_check_reward_lrb (
          solver, idx,
          reward->weighted ? kissat_lrb_weighted_step (unweighted, decided,
                                                       reward->wimp)
                           : unweighted,
          logged);
#endif
    assert (c < sizeof reward->count.updates /
                    sizeof *reward->count.updates);
    reward->count.updates[c]++;
  }
  const double old_q = true_q (solver, idx);
  const double new_q = (1 - alpha) * old_q + alpha * r;
  LOG ("LRB pays %s reward %g interval %" PRIu64 " Q %g -> %g",
       LOGVAR (idx), r, interval, old_q, new_q);
  lrb->count.updates++;
  lrb->count.above += r > 1;
  store_q (solver, idx, new_q);
#ifdef FEEDBACK
  kissat_feedback_lrb_close (solver, FEEDBACK_LRB_PAID, r, alpha);
#endif
}

void kissat_print_lrb_statistics (kissat *solver) {
#ifndef QUIET
  const lrb *const lrb = &solver->policy.lrb;
  const estimator *const estimator = &solver->estimator;
  kissat_message (solver, "estimator-lrb-conflicts %" PRIu64,
                  estimator->chb.conflicts);
  kissat_message (solver, "estimator-lrb-analyzed %" PRIu64,
                  estimator->chb.analyzed);
  kissat_message (solver, "estimator-lrb-opened %" PRIu64,
                  lrb->count.opened);
  kissat_message (solver, "estimator-lrb-participations %" PRIu64,
                  lrb->count.participations);
  kissat_message (solver, "estimator-lrb-reason-participations %" PRIu64,
                  lrb->count.reasons);
  kissat_message (solver, "estimator-lrb-closed-step %" PRIu64,
                  lrb->count.closed[INTERVALS_CLOSE_DEFERRED]);
  kissat_message (solver, "estimator-lrb-closed-unassigned %" PRIu64,
                  lrb->count.closed[INTERVALS_CLOSE_UNASSIGNED]);
  kissat_message (solver, "estimator-lrb-closed-left %" PRIu64,
                  lrb->count.closed[INTERVALS_CLOSE_LEFT]);
  kissat_message (solver, "estimator-lrb-updates %" PRIu64,
                  lrb->count.updates);
  kissat_message (solver, "estimator-lrb-above-one %" PRIu64,
                  lrb->count.above);
  kissat_message (solver, "estimator-lrb-skipped %" PRIu64,
                  lrb->count.skipped);
  kissat_message (solver, "estimator-lrb-ignored %" PRIu64,
                  lrb->count.ignored);
  kissat_message (solver, "estimator-lrb-alpha %.17g",
                  kissat_chb_alpha (estimator->chb.conflicts));
#ifndef NDEBUG
  kissat_message (solver, "estimator-lrb-check-closes %" PRIu64,
                  lrb->check.closes);
  kissat_message (solver, "estimator-lrb-check-participations %" PRIu64,
                  lrb->check.logged[0]);
  kissat_message (solver,
                  "estimator-lrb-check-reason-participations %" PRIu64,
                  lrb->check.logged[1]);
#endif
#else
  (void) solver;
#endif
}

#else

int kissat_lrb_dummy_to_avoid_warning;

#endif
