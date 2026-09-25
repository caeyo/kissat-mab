#include "chb.h"

#ifndef HEAPARGMAX

#include "inline.h"
#include "inlinepolicy.h"

#include <inttypes.h>

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
  if (played >= size)
    return;
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
    kissat_update_score (solver, idx, new_q);
    plays++;
  }
  estimator->chb.plays += plays;
}

// On-the-fly strengthening analyses one conflict in several rounds, each
// recording its analyzed variables, so a conflict is counted in 'analyzed'
// by its first round only.  A conflict that Kissat reuses as the reason of
// its single literal on the conflict level is not analyzed and records
// nothing, as it bumps nothing on the VSIDS line.

void kissat_chb_analyzed (kissat *solver) {
  assert (solver->stable);
  estimator *const estimator = &solver->estimator;
  const uint64_t conflicts = estimator->chb.conflicts;
  uint64_t *const last_conflict = solver->last_conflict;
  const flags *const flags = solver->flags;
  for (all_stack (unsigned, idx, solver->analyzed))
    if (flags[idx].active)
      last_conflict[idx] = conflicts;
  if (estimator->chb.recorded != conflicts) {
    estimator->chb.recorded = conflicts;
    estimator->chb.analyzed++;
  }
}

#else

int kissat_chb_dummy_to_avoid_warning;

#endif
