#include "chb.h"

#ifndef HEAPARGMAX

#include "inline.h"
#include "inlinepolicy.h"

#include <inttypes.h>

// Under UCB and TS (see 'keys.h') every payment is also an observation of
// the variable, and the counts' increment grows at every conflict after
// its payments.  Feedback builds measure every payment, and keep UCB's
// counts whatever the options (see 'feedback.h').  Under LRB, which runs
// with none of them, the walk opens the variables' intervals at the
// conflict count before this propagation's conflict, and pays nothing
// (see 'lrb.h').

void kissat_chb_assign (kissat *solver, bool conflict) {
  estimator *const estimator = &solver->estimator;
  const unsigned size = SIZE_ARRAY (solver->trail);
  const unsigned played = estimator->chb.played;
  assert (played <= size);
  estimator->chb.played = size;
  if (!solver->stable)
    return;
  const uint64_t conflicts = estimator->chb.conflicts;
  if (conflict)
    estimator->chb.conflicts = conflicts + 1;
  if (solver->policy.lrb.started) {
    assert (!solver->policy.keys.counts);
    if (played < size)
      kissat_lrb_assign (solver, played, size, conflicts);
    return;
  }
  const bool counts = solver->policy.keys.counts;
  if (played >= size) {
    if (conflict && counts)
      kissat_keys_chb_conflict (solver);
#ifdef FEEDBACK
    if (conflict)
      kissat_feedback_chb_conflict (solver);
#endif
    return;
  }
  const double alpha = kissat_chb_alpha (conflicts);
  const double multiplier =
      conflict ? CHB_MULTIPLIER_CONFLICT : CHB_MULTIPLIER_NO_CONFLICT;
  const unsigned *const trail = BEGIN_ARRAY (solver->trail);
  const flags *const flags = solver->flags;
  const uint64_t *const last_conflict = solver->last_conflict;
  const double *const score = solver->score;
  uint64_t plays = 0;
  for (unsigned i = played; i < size; i++) {
    const unsigned idx = IDX (trail[i]);
    if (!flags[idx].active)
      continue;
    assert (last_conflict[idx] <= conflicts);
    const uint64_t age = conflicts - last_conflict[idx] + 1;
    const double reward = multiplier / (double) age;
    const double old_q = score[idx];
    const double new_q = (1 - alpha) * old_q + alpha * reward;
    LOG ("CHB pays %s reward %g age %" PRIu64 " Q %g -> %g", LOGVAR (idx),
         reward, age, old_q, new_q);
    kissat_update_assigned_score (solver, idx, new_q);
    if (counts)
      kissat_keys_paid (solver, idx);
#ifdef FEEDBACK
    kissat_feedback_paid (solver, idx, reward, alpha, old_q, conflicts);
#endif
#ifdef SHADOW
    if (counts)
      kissat_shadow_paid (solver, idx, conflicts); // recounts observations
#ifdef FEEDBACK
    kissat_shadow_feedback_paid (solver, idx); // counts payments
#endif
#endif
    plays++;
  }
  estimator->chb.plays += plays;
  if (conflict && counts)
    kissat_keys_chb_conflict (solver);
#ifdef FEEDBACK
  if (conflict)
    kissat_feedback_chb_conflict (solver);
#endif
}

// On-the-fly strengthening analyses one conflict in several rounds, each
// recording its analyzed variables, so a conflict is counted in 'analyzed'
// by its first round only.  A conflict that Kissat reuses as the reason of
// its single literal on the conflict level is not analyzed and records
// nothing, as it bumps nothing on the VSIDS line.  Under LRB every round
// counts the participations of its variables, the reason-side ones apart,
// and 'last_conflict' is not kept (see 'lrb.h').

void kissat_chb_analyzed (kissat *solver) {
  assert (solver->stable);
  estimator *const estimator = &solver->estimator;
  const uint64_t conflicts = estimator->chb.conflicts;
  if (solver->policy.lrb.started)
    kissat_lrb_analyzed (solver);
  else {
    uint64_t *const last_conflict = solver->last_conflict;
    const flags *const flags = solver->flags;
    for (all_stack (unsigned, idx, solver->analyzed))
      if (flags[idx].active)
        last_conflict[idx] = conflicts;
  }
  if (estimator->chb.recorded != conflicts) {
    estimator->chb.recorded = conflicts;
    estimator->chb.analyzed++;
  }
}

#else

int kissat_chb_dummy_to_avoid_warning;

#endif
