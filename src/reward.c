#include "reward.h"

#ifndef HEAPARGMAX

#include "allocate.h"
#include "bump.h"
#include "error.h"
#include "inline.h"
#include "inlinepolicy.h"
#include "logging.h"
#include "print.h"

#include <float.h>
#include <inttypes.h>
#include <math.h>
#include <string.h>

#ifndef NDEBUG

// The arrays of the checks, of 'size' entries each, zero beyond 'old'.

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

#define RELEASE(P) \
  do { \
    if (P) \
      kissat_dealloc (solver, (P), size, sizeof *(P)); \
    (P) = 0; \
  } while (0)

#endif

void kissat_resize_reward (kissat *solver, unsigned new_size) {
#ifndef NDEBUG
  reward *const reward = &solver->policy.reward;
  if (!reward->started)
    return;
  const unsigned old_size = reward->check.size;
  if (old_size == new_size)
    return;
  RESIZE (reward->check.eager);
  RESIZE (reward->check.listed_at);
  RESIZE (reward->check.decided);
  RESIZE (reward->check.marked);
  RESIZE (reward->check.rounds);
  RESIZE (reward->check.bumped);
  RESIZE (reward->check.asserted);
  reward->check.size = new_size;
  reward->check.dirty = true;
#else
  (void) solver, (void) new_size;
#endif
}

void kissat_release_reward (kissat *solver) {
#ifndef NDEBUG
  reward *const reward = &solver->policy.reward;
  const unsigned size = reward->check.size;
  RELEASE (reward->check.eager);
  RELEASE (reward->check.listed_at);
  RELEASE (reward->check.decided);
  RELEASE (reward->check.marked);
  RELEASE (reward->check.rounds);
  RELEASE (reward->check.bumped);
  RELEASE (reward->check.asserted);
  RELEASE_STACK (reward->check.listed);
  reward->check.size = 0;
#else
  (void) solver;
#endif
}

// The components and what they exclude (see 'reward.h').  The policy is
// Argmax; 'wimp' and 'locality' run on VSIDS scores or on LRB's estimator,
// 'intervalreward' on VSIDS scores only, and none in feedback builds.  In
// assertion builds the eager form starts from the scores, every variable
// unassigned or its interval not yet recorded, at g = 1.

void kissat_start_reward (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  if (reward->started)
    return;
  const unsigned wimp = GET_OPTION (wimp);
  const bool locality = GET_OPTION (locality);
  const bool interval = GET_OPTION (intervalreward);
  if (wimp == 1000 && !locality && !interval)
    return;
#ifdef FEEDBACK
  kissat_fatal ("feedback builds measure the published rewards: 'wimp', "
                "'locality' and 'intervalreward' need a build without "
                "'--feedback'");
#endif
  if (GET_OPTION (softmax) || GET_OPTION (perturbed) ||
      GET_OPTION (thompson) || GET_OPTION (ucb) || GET_OPTION (gammappm))
    kissat_fatal ("the reward ('wimp', 'locality', 'intervalreward') "
                  "decides by Argmax: 'softmax', 'perturbed', 'thompson', "
                  "'ucb' and 'gammappm' must be zero");
  const bool chb = kissat_chb (solver);
  if (chb && interval)
    kissat_fatal ("'intervalreward' needs VSIDS scores ('chb=0')");
  if (chb && !kissat_lrb (solver))
    kissat_fatal ("'wimp' and 'locality' need VSIDS scores or LRB's "
                  "reward ('chb=1' needs 'lrb=1')");
  reward->started = true;
  reward->lrb = chb;
  reward->weighted = wimp != 1000;
  reward->locality = locality;
  reward->interval = interval;
  reward->wimp = wimp / 1000.0;
  reward->lambda = GET_OPTION (localitydecay) / 1000.0;
  reward->growth = 1 / reward->lambda;
  reward->g = 1;
#ifndef NDEBUG
  kissat_resize_reward (solver, solver->size);
  for (all_variables (idx))
    reward->check.eager[idx] = solver->score[idx];
#endif
  kissat_very_verbose (solver,
                       "reward on %s: implied weight %g, locality %s "
                       "(lambda %g), interval reward %s",
                       chb ? "LRB's estimator" : "VSIDS scores",
                       reward->wimp, locality ? "on" : "off",
                       reward->lambda, interval ? "on" : "off");
}

// The interval reward's payment, inc (b / k) w g_a, and the weight of a
// class (see 'reward.h').

static inline double payment (double inc, uint64_t b, uint64_t k, double w,
                              double scale) {
  return inc * ((double) b / (double) k) * w * scale;
}

static inline double weight (const reward *reward, unsigned c) {
  return c == INTERVALS_DECIDED || c == REWARD_NONE ? 1 : reward->wimp;
}

#ifndef NDEBUG

// The checks of assertion builds (see 'reward.h').

#define FATAL(...) kissat_fatal ("reward check: " __VA_ARGS__)

static double relative_error (double lazy, double eager) {
  return fabs (lazy - eager) / (fabs (eager) + DBL_MIN);
}

// The lazy value of 'idx' in true units: its stored value over the
// multiplier of its interval's start, open or deferred, or over g.

static double lazy_value (kissat *solver, unsigned idx) {
  const reward *const reward = &solver->policy.reward;
  const intervals *const intervals = &solver->policy.intervals;
  const unsigned state = intervals->state[idx];
  const double scale = state & (INTERVALS_OPEN | INTERVALS_DEFERRED)
                           ? intervals->multiplier[idx]
                           : reward->g;
  return solver->score[idx] / scale;
}

// The candidates for the eager pick: the unassigned active variables of
// the largest eager values, the smaller index first among ties, offered
// in index order to 'select_candidate'.

static void select_candidate (reward *reward, unsigned idx) {
  const double *const eager = reward->check.eager;
  unsigned *const candidate = reward->check.candidate;
  unsigned n = reward->check.candidates;
  const double value = eager[idx];
  if (n == REWARD_CANDIDATES &&
      !(value > eager[candidate[REWARD_CANDIDATES - 1]]))
    return;
  if (n < REWARD_CANDIDATES)
    n++;
  unsigned i = n - 1;
  while (i && value > eager[candidate[i - 1]]) {
    candidate[i] = candidate[i - 1];
    i--;
  }
  candidate[i] = idx;
  reward->check.candidates = n;
}

static void select_candidates (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  reward->check.candidates = 0;
  for (all_variables (idx))
    if (ACTIVE (idx) && !VALUE (LIT (idx)))
      select_candidate (reward, idx);
  reward->check.dirty = false;
}

// The eager pick: the first candidate still active and unassigned,
// selected again if every one was assigned or deactivated since (or none
// is left).  Only assignments and deactivations (elimination, a unit)
// take candidates away between two selections; every other change selects
// again.

static unsigned eager_pick (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  if (reward->check.dirty)
    select_candidates (solver);
  for (unsigned round = 0; round < 2; round++) {
    const unsigned *const candidate = reward->check.candidate;
    for (unsigned i = 0; i < reward->check.candidates; i++) {
      const unsigned idx = candidate[i];
      if (ACTIVE (idx) && !VALUE (LIT (idx)))
        return idx;
    }
    select_candidates (solver);
  }
  return INVALID_IDX;
}

// Every active variable's lazy value against its eager one.

static void complete_check (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  const double *const eager = reward->check.eager;
  const uint64_t pick = reward->check.picks;
  reward->check.complete++;
  for (all_variables (idx)) {
    if (!ACTIVE (idx))
      continue;
    const double lazy = lazy_value (solver, idx);
    const double error = relative_error (lazy, eager[idx]);
    reward->check.values++;
    if (error > reward->check.error)
      reward->check.error = error;
    if (!(error <= REWARD_TOLERANCE))
      FATAL ("pick %" PRIu64 ": the lazy value %.17g of %s variable %u "
             "differs from its eager value %.17g (relative %.3g)",
             pick, lazy, VALUE (LIT (idx)) ? "assigned" : "unassigned",
             idx, eager[idx], error);
  }
}

// The pick against the variable of largest eager value among the
// unassigned ones, the smallest index among ties; a pick of another
// variable must be at a tie, its eager value within the tolerance.

void kissat_check_reward_pick (kissat *solver, unsigned res) {
  reward *const reward = &solver->policy.reward;
  assert (reward->locality);
  const unsigned top = eager_pick (solver);
  const uint64_t pick = ++reward->check.picks;
  if (top == INVALID_IDX)
    FATAL ("pick %" PRIu64 ": no unassigned variable for the eager pick",
           pick);
  if (top != res) {
    const double *const eager = reward->check.eager;
    const double a = eager[res], b = eager[top];
    const double error =
        fabs (a - b) / (fmax (fabs (a), fabs (b)) + DBL_MIN);
    if (!(error <= REWARD_TOLERANCE))
      FATAL ("pick %" PRIu64 ": variable %u of eager value %.17g, where "
             "the eager pick is %u of eager value %.17g",
             pick, res, a, top, b);
    if (a == b)
      reward->check.eager_ties++;
    else if (solver->score[res] == solver->score[top])
      reward->check.lazy_ties++;
    if (reward->check.ties++ < REWARD_LOGGED)
      kissat_message (solver,
                      "reward-check-tie pick %" PRIu64 " lazy %u eager %u "
                      "eager-values %.17g %.17g lazy-values %.17g %.17g",
                      pick, res, top, a, b, lazy_value (solver, res),
                      lazy_value (solver, top));
  }
  if (!(pick % 1000))
    complete_check (solver);
}

// When a step of conflict analysis starts (VSIDS scores): the active
// variables on the trail, which its bump round observes, and whether their
// reason is a decision.

void kissat_check_reward_step (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  assert (reward->started && !reward->lrb);
  const uint64_t step = ++reward->check.step;
  unsigneds *const listed = &reward->check.listed;
  CLEAR_STACK (*listed);
  const assigned *const assigned = solver->assigned;
  for (all_stack (unsigned, lit, solver->trail)) {
    const unsigned idx = IDX (lit);
    if (!ACTIVE (idx))
      continue;
    PUSH_STACK (*listed, idx);
    reward->check.listed_at[idx] = step;
    reward->check.decided[idx] = assigned[idx].reason == DECISION_REASON;
  }
}

// A bump's weight against the one the reason gives at the step's start (a
// bump outside a step, which only the unit tests make, against the
// current reason, or none), and its class.

static void check_bump (kissat *solver, unsigned idx, unsigned c,
                        double w) {
  reward *const reward = &solver->policy.reward;
  bool decided;
  if (solver->policy.intervals.analyzing) {
    if (reward->check.listed_at[idx] != reward->check.step)
      FATAL ("bump of variable %u, unassigned when the step started", idx);
    decided = reward->check.decided[idx];
  } else if (VALUE (LIT (idx)))
    decided = solver->assigned[idx].reason == DECISION_REASON;
  else
    decided = true;
  if (c != REWARD_NONE && decided != (c == INTERVALS_DECIDED))
    FATAL ("bump of variable %u in an interval of class %u, but its "
           "reason was %sa decision",
           idx, c, decided ? "" : "not ");
  const double expected = c == REWARD_NONE || decided ? 1 : reward->wimp;
  if (!kissat_same_double (expected, w))
    FATAL ("bump of variable %u with weight %.17g, where its class gives "
           "%.17g",
           idx, w, expected);
  reward->check.bumps++;
}

// The end of a bump round (the interval reward): every variable the round
// observes, the step's listed ones (outside a step, in the unit tests,
// those on the trail), counts it, and its bump if it was analyzed.

void kissat_check_reward_round (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  if (!reward->interval)
    return;
  const uint64_t round = solver->estimator.rounds;
  uint64_t *const marked = reward->check.marked;
  for (all_stack (unsigned, idx, solver->analyzed))
    if (ACTIVE (idx))
      marked[idx] = round;
  uint64_t *const rounds = reward->check.rounds;
  uint64_t *const bumped = reward->check.bumped;
  if (solver->policy.intervals.analyzing) {
    for (all_stack (unsigned, idx, reward->check.listed)) {
      rounds[idx]++;
      if (marked[idx] == round)
        bumped[idx]++;
    }
  } else
    for (all_stack (unsigned, lit, solver->trail)) {
      const unsigned idx = IDX (lit);
      if (!ACTIVE (idx))
        continue;
      rounds[idx]++;
      if (marked[idx] == round)
        bumped[idx]++;
    }
}

// An interval's k and b against the brute force's counts.

static void check_interval (kissat *solver, unsigned idx, uint64_t k,
                            uint64_t b) {
  reward *const reward = &solver->policy.reward;
  uint64_t *const rounds = reward->check.rounds + idx;
  uint64_t *const bumped = reward->check.bumped + idx;
  if (*rounds != k || *bumped != b)
    FATAL ("interval of variable %u closes after %" PRIu64 " bump rounds, "
           "%" PRIu64 " with a bump, but %" PRIu64 " and %" PRIu64
           " counted (bump round %" PRIu64 ")",
           idx, k, b, *rounds, *bumped, solver->estimator.rounds);
  *rounds = *bumped = 0;
  reward->check.intervals++;
}

// The score after the interval reward's payment against the score before
// it and the payment that k and b, now the brute force's, give, bitwise;
// the eager value takes the payment in true units.

static void check_payment (kissat *solver, unsigned idx, unsigned c,
                           uint64_t k, uint64_t b, double old_score,
                           double new_score) {
  reward *const reward = &solver->policy.reward;
  const double w = weight (reward, c);
  const double scale =
      reward->locality ? solver->policy.intervals.multiplier[idx] : 1;
  const double inc = solver->scinc;
  const double expected = old_score + payment (inc, b, k, w, scale);
  if (!kissat_same_double (expected, new_score))
    FATAL ("interval of variable %u pays %.17g to %.17g, where %" PRIu64
           " bumped of %" PRIu64 " rounds give %.17g",
           idx, new_score - old_score, new_score, b, k, expected);
  reward->check.payments++;
  if (reward->locality) {
    reward->check.eager[idx] += payment (inc, b, k, w, 1);
    reward->check.dirty = true;
  }
}

// The class of a record against the reason, decided, and the literal an
// analysis step asserted, noted there with its trail position.

void kissat_check_reward_record (kissat *solver, unsigned idx, unsigned c) {
  reward *const reward = &solver->policy.reward;
  const assigned *const a = solver->assigned + idx;
  unsigned *const asserted = reward->check.asserted + idx;
  unsigned expected = INTERVALS_PROPAGATED;
  if (a->reason == DECISION_REASON)
    expected = INTERVALS_DECIDED;
  else if (*asserted == a->trail + 1)
    expected = INTERVALS_ASSERTED;
  *asserted = 0;
  if (c != expected)
    FATAL ("interval of variable %u at trail position %u recorded in class "
           "%u, where its assignment gives %u",
           idx, a->trail, c, expected);
  reward->check.classes++;
}

// The literal an analysis step asserts, with the learned clause or the
// reused conflict as its reason: the last assignment, and not a decision.

void kissat_check_reward_asserted (kissat *solver, unsigned idx) {
  reward *const reward = &solver->policy.reward;
  const assigned *const a = solver->assigned + idx;
  assert (!EMPTY_ARRAY (solver->trail));
  if (IDX (END_ARRAY (solver->trail)[-1]) != idx)
    FATAL ("asserted variable %u is not the last assignment", idx);
  if (a->reason == DECISION_REASON || a->reason == UNIT_REASON)
    FATAL ("asserted variable %u has no clause as its reason", idx);
  reward->check.asserted[idx] = a->trail + 1;
  reward->check.assertions++;
}

// A score written in true units while 'idx' is unassigned: its eager value
// is the score, or with 'added' (reorder's weight) grows by it.

void kissat_check_reward_true_score (kissat *solver, unsigned idx,
                                     double score, bool added) {
  reward *const reward = &solver->policy.reward;
  assert (reward->locality);
  double *const eager = reward->check.eager + idx;
  *eager = added ? *eager + score : score;
  reward->check.dirty = true;
}

// LRB's update of 'idx', from the check's step and the log's reward.

void kissat_check_reward_lrb (kissat *solver, unsigned idx, double alpha,
                              double r) {
  reward *const reward = &solver->policy.reward;
  assert (reward->locality && reward->lrb);
  double *const eager = reward->check.eager + idx;
  *eager = (1 - alpha) * *eager + alpha * r;
  reward->check.dirty = true;
}

#endif

// VSIDS scores: a bump round's bumps.  A bump falls in the interval of
// 'kissat_interval_bumped', which counts it in b under the interval reward,
// and adds inc w_c, times g_a under locality, or under the interval reward
// nothing until the close.

void kissat_reward_bumps (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  assert (reward->started);
  assert (!reward->lrb);
  const intervals *const intervals = &solver->policy.intervals;
  const flags *const flags = solver->flags;
  const bool locality = reward->locality;
  const bool interval = reward->interval;
  if (locality)
    reward->decay = true;
  for (all_stack (unsigned, idx, solver->analyzed)) {
    if (!flags[idx].active)
      continue;
    const unsigned bumped = kissat_interval_bumped (solver, idx);
    const unsigned c =
        bumped == INTERVALS_NONE ? REWARD_NONE : bumped & INTERVALS_CLASS;
    reward->count.bumps[c]++;
    const double w = weight (reward, c);
#ifndef NDEBUG
    check_bump (solver, idx, c, w);
#endif
    if (interval)
      continue;
    const double inc = solver->scinc;
    double delta = inc * w;
    if (locality)
      delta *= c == REWARD_NONE ? reward->g : intervals->multiplier[idx];
#ifndef NDEBUG
    if (locality) {
      reward->check.eager[idx] += inc * w;
      reward->check.dirty = true;
    }
#endif
    const double new_score = solver->score[idx] + delta;
    LOG ("reward bumps %s in class %u weight %g by %g", LOGVAR (idx), c, w,
         delta);
    kissat_update_score (solver, idx, new_score);
    if (new_score > MAX_SCORE)
      kissat_rescale_scores (solver);
  }
}

// VSIDS scores: the interval of 'idx' closes.  The interval reward pays
// inc (b / k) w_c g_a, and locality moves the stored value from g_a to g.
// A payment that takes the stored value above 'MAX_SCORE' rescales after
// the write.

void kissat_close_reward_interval (kissat *solver, unsigned idx,
                                   unsigned c, unsigned how) {
  reward *const reward = &solver->policy.reward;
  const intervals *const intervals = &solver->policy.intervals;
  assert (reward->started);
  assert (!reward->lrb);
  assert (how < sizeof reward->count.closed / sizeof *reward->count.closed);
  reward->count.closed[how]++;
  double score = solver->score[idx];
  const double scale = reward->locality ? intervals->multiplier[idx] : 1;
  bool overflow = false;
  if (reward->interval) {
    const uint64_t k = solver->estimator.rounds - intervals->start[idx];
    const uint64_t b = intervals->bumps[idx];
    assert (b <= k);
#ifndef NDEBUG
    check_interval (solver, idx, k, b);
#endif
    if (!k)
      reward->count.empty++;
    else {
      reward->count.paid++;
      if (!b)
        reward->count.unbumped++;
      else {
        const double old_score = score;
        score += payment (solver->scinc, b, k, weight (reward, c), scale);
        overflow = score > MAX_SCORE;
        LOG ("reward pays %s in class %u for %" PRIu64 " of %" PRIu64
             " rounds: %g -> %g",
             LOGVAR (idx), c, b, k, old_score, score);
#ifndef NDEBUG
        check_payment (solver, idx, c, k, b, old_score, score);
#else
        (void) old_score;
#endif
      }
    }
  }
  if (reward->locality)
    score *= reward->g / scale;
  kissat_update_score (solver, idx, score);
  if (overflow)
    kissat_rescale_scores (solver);
}

// Locality: every open or deferred interval takes the current g, its
// stored value multiplied by g / g_a, as if it were recorded now.  The
// writes go to the estimator (and the heap of shadow builds) only, since a
// rebuild of the tree follows.

static void rerecord (kissat *solver) {
  const reward *const reward = &solver->policy.reward;
  const intervals *const intervals = &solver->policy.intervals;
  const uint8_t *const state = intervals->state;
  double *const multiplier = intervals->multiplier;
  double *const score = solver->score;
  const double g = reward->g;
  for (all_variables (idx)) {
    if (!(state[idx] & (INTERVALS_OPEN | INTERVALS_DEFERRED)))
      continue;
    const double g_a = multiplier[idx];
    if (g_a == g)
      continue;
    score[idx] *= g / g_a;
#ifdef SHADOW
    kissat_update_heap (solver, SCORES, idx, score[idx]);
#endif
    multiplier[idx] = g;
  }
}

// g and every multiplier at the intervals' start back to one.

static void reset_multipliers (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  double *const multiplier = solver->policy.intervals.multiplier;
  for (all_variables (idx))
    multiplier[idx] = 1;
  reward->g = 1;
}

double kissat_begin_locality_rescale (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  if (!reward->locality)
    return 1;
  assert (!reward->lrb);
  kissat_record_intervals (solver);
  rerecord (solver);
  return reward->g;
}

void kissat_end_locality_rescale (kissat *solver, double unit) {
  reward *const reward = &solver->policy.reward;
  if (!reward->locality)
    return;
  LOG ("locality rescaled with g %g", reward->g);
  reset_multipliers (solver);
#ifndef NDEBUG
  double *const eager = reward->check.eager;
  for (all_variables (idx))
    eager[idx] *= unit;
  reward->check.dirty = true;
#else
  (void) unit;
#endif
}

// LRB's estimator: g above 'MAX_SCORE' divides every stored value by g,
// after the open intervals took the current g; the Q's do not change.

static void rescale_lrb (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  assert (reward->lrb);
  kissat_record_intervals (solver);
  rerecord (solver);
  const double g = reward->g;
  LOG ("locality on LRB rescaled with g %g", g);
  kissat_scale_scores (solver, 1 / g, 1);
  reset_multipliers (solver);
}

// Locality: the step ends, after its closes.  The literals assigned since
// its backtrack are recorded at the current g first, then every
// unassigned variable decays, by g growing, which rescales above
// 'MAX_SCORE'.

void kissat_decay_locality (kissat *solver) {
  reward *const reward = &solver->policy.reward;
  assert (reward->locality);
  assert (reward->decay);
  assert (solver->stable);
  reward->decay = false;
  kissat_record_intervals (solver);
#ifndef NDEBUG
  double *const eager = reward->check.eager;
  const double lambda = reward->lambda;
  reward->check.candidates = 0;
  for (all_variables (idx))
    if (ACTIVE (idx) && !VALUE (LIT (idx))) {
      eager[idx] *= lambda;
      select_candidate (reward, idx);
    }
  reward->check.dirty = false;
#endif
  reward->g *= reward->growth;
  reward->count.steps++;
  if (reward->g <= MAX_SCORE)
    return;
  reward->count.rescales++;
  if (reward->lrb)
    rescale_lrb (solver);
  else
    kissat_rescale_scores (solver);
}

void kissat_print_reward_statistics (kissat *solver) {
#ifndef QUIET
  const reward *const reward = &solver->policy.reward;
  if (!reward->lrb) {
    kissat_message (solver, "estimator-reward-bumps-decided %" PRIu64,
                    reward->count.bumps[INTERVALS_DECIDED]);
    kissat_message (solver, "estimator-reward-bumps-asserted %" PRIu64,
                    reward->count.bumps[INTERVALS_ASSERTED]);
    kissat_message (solver, "estimator-reward-bumps-propagated %" PRIu64,
                    reward->count.bumps[INTERVALS_PROPAGATED]);
    kissat_message (solver, "estimator-reward-bumps-unobserved %" PRIu64,
                    reward->count.bumps[REWARD_NONE]);
    kissat_message (solver, "estimator-reward-closed-step %" PRIu64,
                    reward->count.closed[INTERVALS_CLOSE_DEFERRED]);
    kissat_message (solver, "estimator-reward-closed-unassigned %" PRIu64,
                    reward->count.closed[INTERVALS_CLOSE_UNASSIGNED]);
    kissat_message (solver, "estimator-reward-closed-left %" PRIu64,
                    reward->count.closed[INTERVALS_CLOSE_LEFT]);
    kissat_message (solver, "estimator-reward-interval-paid %" PRIu64,
                    reward->count.paid);
    kissat_message (solver, "estimator-reward-interval-unbumped %" PRIu64,
                    reward->count.unbumped);
    kissat_message (solver, "estimator-reward-interval-empty %" PRIu64,
                    reward->count.empty);
  } else {
    kissat_message (solver, "estimator-reward-updates-decided %" PRIu64,
                    reward->count.updates[INTERVALS_DECIDED]);
    kissat_message (solver, "estimator-reward-updates-asserted %" PRIu64,
                    reward->count.updates[INTERVALS_ASSERTED]);
    kissat_message (solver, "estimator-reward-updates-propagated %" PRIu64,
                    reward->count.updates[INTERVALS_PROPAGATED]);
  }
  kissat_message (solver, "estimator-reward-locality-steps %" PRIu64,
                  reward->count.steps);
  kissat_message (solver, "estimator-reward-locality-rescales %" PRIu64,
                  reward->count.rescales);
  kissat_message (solver, "estimator-reward-locality-g %.17g",
                  reward->locality ? reward->g : 1);
#ifndef NDEBUG
  kissat_message (solver, "estimator-reward-check-picks %" PRIu64,
                  reward->check.picks);
  kissat_message (solver, "estimator-reward-check-ties %" PRIu64,
                  reward->check.ties);
  kissat_message (solver, "estimator-reward-check-ties-eager %" PRIu64,
                  reward->check.eager_ties);
  kissat_message (solver, "estimator-reward-check-ties-lazy %" PRIu64,
                  reward->check.lazy_ties);
  kissat_message (solver, "estimator-reward-check-complete %" PRIu64,
                  reward->check.complete);
  kissat_message (solver, "estimator-reward-check-values %" PRIu64,
                  reward->check.values);
  kissat_message (solver, "estimator-reward-check-error %.3g",
                  reward->check.error);
  kissat_message (solver, "estimator-reward-check-bumps %" PRIu64,
                  reward->check.bumps);
  kissat_message (solver, "estimator-reward-check-classes %" PRIu64,
                  reward->check.classes);
  kissat_message (solver, "estimator-reward-check-updates %" PRIu64,
                  reward->check.updates);
  kissat_message (solver, "estimator-reward-check-assertions %" PRIu64,
                  reward->check.assertions);
  kissat_message (solver, "estimator-reward-check-intervals %" PRIu64,
                  reward->check.intervals);
  kissat_message (solver, "estimator-reward-check-payments %" PRIu64,
                  reward->check.payments);
#endif
#else
  (void) solver;
#endif
}

#else

int kissat_reward_dummy_to_avoid_warning;

#endif
