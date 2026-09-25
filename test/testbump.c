#include "../src/bump.h"
#include "../src/inlinepolicy.h"

#include "test.h"

#include <inttypes.h>
#include <math.h>

void kissat_update_scores (kissat *);

static void test_bump_rescale (void) {
  kissat *solver = kissat_init ();
  kissat_add (solver, 1);
  kissat_add (solver, 2);
  kissat_add (solver, 0);
  kissat_add (solver, -1);
  kissat_add (solver, -2);
  kissat_add (solver, 0);
  if (!solver->stable) {
    tissat_verbose ("forced switching to stable mode");
    solver->stable = true;
  }
  tissat_verbose ("forced updating of scores");
  kissat_update_scores (solver);
  assert (solver->scinc > 0);
  tissat_verbose ("initial score increment %g", solver->scinc);
  ACTIVE (0) = ACTIVE (1) = true;
  unsigned count = 0;
  for (unsigned i = 1; i <= 5; i++) {
    double prev = 0;
    assert (prev < solver->scinc);
    while (prev < solver->scinc) {
      prev = solver->scinc;
      if (i != 3) {
        PUSH_STACK (solver->analyzed, 0);
        if (count++ & 1)
          PUSH_STACK (solver->analyzed, 1);
      }
      kissat_bump_analyzed (solver);
      CLEAR_STACK (solver->analyzed);
      if (prev >= solver->scinc || solver->scinc >= MAX_SCORE * 0.7 ||
          kissat_get_score (solver, 0) >= MAX_SCORE * 0.7 ||
          kissat_get_score (solver, 1) >= MAX_SCORE * 0.7)
        tissat_verbose ("%u.%u: score[0]=%g score[1]=%g scinc=%g", i, count,
                        kissat_get_score (solver, 0),
                        kissat_get_score (solver, 1), solver->scinc);
    }
  }
  kissat_release (solver);
}

// The pseudo-activity: added to Kissat's initial scores 1 - 1/k at
// activation, and rescaled with the scores, so that it stays the current
// value of a bump of the initial increment at time zero, which is the
// increment times 0.95 to the power of the bump rounds.

static void test_bump_pseudo_activity (bool pseudo) {
  kissat *solver = kissat_init ();
#ifndef NOPTIONS
  kissat_set_option (solver, "pseudoactivity", pseudo);
#else
  if (!pseudo) {
    kissat_release (solver);
    return;
  }
#endif
  assert (solver->estimator.pseudo == 1.0);
  kissat_add (solver, 1);
  kissat_add (solver, 2);
  kissat_add (solver, 3);
  kissat_add (solver, 0);
  kissat_add (solver, -1);
  kissat_add (solver, -2);
  kissat_add (solver, 0);
  const double offset = pseudo ? 1.0 : 0.0;
  assert (kissat_get_score (solver, 0) == 0.0 + offset);
  assert (kissat_get_score (solver, 1) == 0.5 + offset);
  assert (kissat_get_score (solver, 2) == 1.0 - 1.0 / 3 + offset);
  if (!solver->stable)
    solver->stable = true;
  kissat_update_scores (solver);
  while (solver->estimator.rescales < 3) {
    PUSH_STACK (solver->analyzed, 0);
    kissat_bump_analyzed (solver);
    CLEAR_STACK (solver->analyzed);
  }
  const estimator *const estimator = &solver->estimator;
  tissat_verbose ("%" PRIu64 " rounds %" PRIu64 " rescales pseudo %g "
                  "scinc %g",
                  estimator->rounds, estimator->rescales, estimator->pseudo,
                  solver->scinc);
  assert (estimator->rounds > 13000);
  assert (!estimator->pseudo);
  assert (estimator->zero.rescale == 3);
  assert (estimator->zero.round == estimator->rounds);
  assert (!kissat_get_score (solver, 1));
  assert (kissat_get_score (solver, 0) > 0);
  kissat_release (solver);
}

static void test_bump_pseudo_activity_rescaled (void) {
  kissat *solver = kissat_init ();
  kissat_add (solver, 1);
  kissat_add (solver, 2);
  kissat_add (solver, 0);
  if (!solver->stable)
    solver->stable = true;
  kissat_update_scores (solver);
  const estimator *const estimator = &solver->estimator;
  unsigned checked = 0;
  while (estimator->rescales < 2) {
    const uint64_t rescales = estimator->rescales;
    PUSH_STACK (solver->analyzed, 0);
    kissat_bump_analyzed (solver);
    CLEAR_STACK (solver->analyzed);
    if (estimator->rescales == rescales)
      continue;
    const double expected =
        solver->scinc * pow (0.95, (double) estimator->rounds);
    assert (fabs (estimator->pseudo - expected) <= 1e-9 * expected);
    assert (!estimator->zero.rescale);
    checked++;
  }
  assert (checked == 2);
  kissat_release (solver);
}

static void test_bump_pseudo_activity_on (void) {
  test_bump_pseudo_activity (true);
}

static void test_bump_pseudo_activity_off (void) {
  test_bump_pseudo_activity (false);
}

void tissat_schedule_bump (void) {
  SCHEDULE_FUNCTION (test_bump_rescale);
  SCHEDULE_FUNCTION (test_bump_pseudo_activity_on);
  SCHEDULE_FUNCTION (test_bump_pseudo_activity_off);
  SCHEDULE_FUNCTION (test_bump_pseudo_activity_rescaled);
}
