#include "../src/chb.h"
#include "../src/inlinepolicy.h"

#include "test.h"

#include <math.h>

#if !defined(HEAPARGMAX) && !defined(NOPTIONS)

// A solver with one clause over 'vars' variables, in stable mode with CHB
// scores and the policy started as the search starts it.

static kissat *new_solver (unsigned vars, bool softmax, int etalog2) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, "chb", 1);
  kissat_set_option (solver, "softmax", softmax);
  kissat_set_option (solver, "etalog2", etalog2);
  for (unsigned i = 1; i <= vars; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  return solver;
}

// Puts 'idx' on the trail as if propagation had assigned it.

static void assign (kissat *solver, unsigned idx) {
  const unsigned lit = LIT (idx);
  solver->values[lit] = 1;
  solver->values[NOT (lit)] = -1;
  PUSH_ARRAY (solver->trail, lit);
}

// Takes the trail back to its first 'size' literals, as backtracking does.

static void shrink (kissat *solver, unsigned size) {
  while (SIZE_ARRAY (solver->trail) > size) {
    const unsigned lit = *--solver->trail.end;
    solver->values[lit] = solver->values[NOT (lit)] = 0;
    kissat_policy_unassign (solver, IDX (lit));
  }
  kissat_chb_shrink_trail (solver, size);
}

static double erwa (double q, double alpha, double reward) {
  return (1 - alpha) * q + alpha * reward;
}

// The step size: 0.4, less 10^-6 per conflict, down to 0.06.

static void test_chb_alpha (void) {
  assert (kissat_chb_alpha (0) == 0.4);
  assert (kissat_chb_alpha (1) == 0.4 - 1e-6);
  assert (fabs (kissat_chb_alpha (100000) - 0.3) < 1e-12);
  assert (kissat_chb_alpha (339000) > 0.06);
  assert (kissat_chb_alpha (340001) == 0.06);
  assert (kissat_chb_alpha (UINT64_MAX) == 0.06);
}

// Q starts at zero, and there is no pseudo-activity.  The VSIDS line keeps
// Kissat's 1 - 1/k plus the pseudo-activity.

static void test_chb_initial_scores (void) {
  kissat *solver = new_solver (5, false, 0);
  assert (!kissat_pseudo_activity (solver));
  for (unsigned idx = 0; idx < 5; idx++)
    assert (kissat_get_score (solver, idx) == 0);
  assert (!solver->policy.tree.weighted);
  assert (kissat_policy_pick (solver) == 0);
  kissat_release (solver);
  solver = kissat_init ();
  for (unsigned i = 1; i <= 5; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  for (unsigned idx = 0; idx < 5; idx++)
    assert (kissat_get_score (solver, idx) ==
            (1.0 - 1.0 / (idx + 1)) + solver->estimator.pseudo);
  kissat_release (solver);
}

// Rewards per propagation: the multiplier, the age since the last conflict
// a variable took part in, the step size, and the paid trail position,
// which backtracking moves down so that kept literals are not paid again.

static void test_chb_rewards (void) {
  kissat *solver = new_solver (4, false, 0);
  const tree *const tree = &solver->policy.tree;
  estimator *const estimator = &solver->estimator;

  assign (solver, 0), assign (solver, 1);
  kissat_chb_assign (solver, false);
  assert (kissat_get_score (solver, 0) == erwa (0, 0.4, 0.9));
  assert (kissat_get_score (solver, 1) == erwa (0, 0.4, 0.9));
  assert (estimator->chb.played == 2);
  assert (estimator->chb.conflicts == 0);

  assign (solver, 2);
  kissat_chb_assign (solver, true);
  assert (kissat_get_score (solver, 2) == erwa (0, 0.4, 1.0));
  assert (kissat_get_score (solver, 1) == erwa (0, 0.4, 0.9));
  assert (estimator->chb.conflicts == 1);

  // Two rounds of analysis (on-the-fly strengthening) of one conflict.
  PUSH_STACK (solver->analyzed, 1);
  kissat_chb_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
  PUSH_STACK (solver->analyzed, 2);
  kissat_chb_analyzed (solver);
  CLEAR_STACK (solver->analyzed);
  assert (solver->last_conflict[0] == 0);
  assert (solver->last_conflict[1] == 1);
  assert (solver->last_conflict[2] == 1);
  assert (estimator->chb.analyzed == 1);

  shrink (solver, 1);
  assert (estimator->chb.played == 1);
  const double q0 = kissat_get_score (solver, 0);
  const double q2 = kissat_get_score (solver, 2);
  assign (solver, 2), assign (solver, 3);
  kissat_chb_assign (solver, false);
  const double alpha = kissat_chb_alpha (1);
  assert (kissat_get_score (solver, 0) == q0);
  assert (kissat_get_score (solver, 2) == erwa (q2, alpha, 0.9 / 1));
  assert (kissat_get_score (solver, 3) == erwa (0, alpha, 0.9 / 2));
  assert (estimator->chb.plays == 5);

  // Focused mode pays nothing but moves past what it assigned.
  shrink (solver, 1);
  solver->stable = false;
  assign (solver, 1);
  const double q1 = kissat_get_score (solver, 1);
  kissat_chb_assign (solver, true);
  assert (kissat_get_score (solver, 1) == q1);
  assert (estimator->chb.played == 2);
  assert (estimator->chb.conflicts == 1);
  solver->stable = true;

  for (unsigned idx = 0; idx < 4; idx++)
    if (kissat_tree_contains (tree, idx))
      assert (kissat_tree_key (tree, idx) == kissat_get_score (solver, idx));
  assert (!kissat_tree_inconsistent_node (tree));
  kissat_release (solver);
}

// Sample's weights are exp (eta * Q), at least one, so a pick never falls
// back, even when the only unassigned variable has Q = 0.

static void test_chb_sample (void) {
  kissat *solver = new_solver (6, true, 3);
  const tree *const tree = &solver->policy.tree;
  assert (tree->weighted);
  assert (solver->policy.chb);
  for (unsigned idx = 1; idx < 6; idx++)
    kissat_update_score (solver, idx, idx / 5.0);
  for (unsigned idx = 0; idx < 6; idx++) {
    const double q = kissat_get_score (solver, idx);
    const double log2_weight =
        kissat_tree_log2_of_weight (kissat_tree_weight (tree, idx));
    assert (fabs (log2_weight - 8 * q / log (2)) < 1e-12);
  }
  for (unsigned idx = 1; idx < 6; idx++) {
    const unsigned lit = LIT (idx);
    solver->values[lit] = 1;
    solver->values[NOT (lit)] = -1;
  }
  for (unsigned i = 0; i < 100; i++)
    assert (kissat_policy_pick (solver) == 0);
  assert (!solver->policy.count.fallbacks[0]);
  kissat_release (solver);
}

#endif

void tissat_schedule_chb (void) {
#if !defined(HEAPARGMAX) && !defined(NOPTIONS)
  SCHEDULE_FUNCTION (test_chb_alpha);
  SCHEDULE_FUNCTION (test_chb_initial_scores);
  SCHEDULE_FUNCTION (test_chb_rewards);
  SCHEDULE_FUNCTION (test_chb_sample);
#endif
}
