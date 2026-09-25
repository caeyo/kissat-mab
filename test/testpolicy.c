#include "../src/inlinepolicy.h"

#include "test.h"

#if !defined(HEAPARGMAX) && !defined(NOPTIONS)

// A solver with one clause over 'vars' variables, in stable mode with the
// policy started as the search starts it.  Without the pseudo-activity the
// first variable has Kissat's initial score zero.

static kissat *new_solver (unsigned vars, bool softmax, int etalog2,
                           bool pseudo) {
  kissat *solver = kissat_init ();
  kissat_set_option (solver, "softmax", softmax);
  kissat_set_option (solver, "etalog2", etalog2);
  kissat_set_option (solver, "pseudoactivity", pseudo);
  for (unsigned i = 1; i <= vars; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  return solver;
}

static void assign (kissat *solver, unsigned idx) {
  const unsigned lit = LIT (idx);
  solver->values[lit] = 1;
  solver->values[NOT (lit)] = -1;
}

static void unassign (kissat *solver, unsigned idx) {
  const unsigned lit = LIT (idx);
  solver->values[lit] = solver->values[NOT (lit)] = 0;
  kissat_policy_unassign (solver, idx);
}

// Argmax keeps an unweighted tree; Sample weighs it with score^eta.

static void test_policy_start (void) {
  kissat *solver = new_solver (5, false, 0, true);
  assert (!solver->policy.tree.weighted);
  kissat_release (solver);
  solver = new_solver (5, true, 3, true);
  const tree *const tree = &solver->policy.tree;
  assert (tree->weighted);
  for (unsigned idx = 0; idx < 5; idx++) {
    const double score = kissat_get_score (solver, idx);
    const tree_weight w = kissat_tree_weight (tree, idx);
    assert (fabs (kissat_tree_log2_of_weight (w) - 8 * log2 (score)) <
            1e-12);
  }
  kissat_release (solver);
}

// Sample never picks an assigned variable, removes those its draws meet,
// and backtracking puts them back.

static void test_policy_sample (void) {
  kissat *solver = new_solver (20, true, 0, true);
  const tree *const tree = &solver->policy.tree;
  for (unsigned idx = 0; idx < 20; idx += 2)
    assign (solver, idx);
  for (unsigned i = 0; i < 1000; i++) {
    const unsigned res = kissat_policy_pick (solver);
    assert (res % 2);
  }
  assert (!solver->policy.count.fallbacks[0]);
  unsigned removed = 0;
  for (unsigned idx = 0; idx < 20; idx += 2)
    removed += !kissat_tree_contains (tree, idx);
  assert (removed == 10);
  for (unsigned idx = 0; idx < 20; idx += 2)
    unassign (solver, idx);
  for (unsigned idx = 0; idx < 20; idx++)
    assert (kissat_tree_contains (tree, idx));
  assert (!kissat_tree_inconsistent_node (tree));
  kissat_release (solver);
}

// Without the pseudo-activity the first variable has score zero, hence
// weight zero.  Once every other variable is assigned no draw can reach
// it, and the pick falls back to Argmax's choice.

static void test_policy_fallback (void) {
  kissat *solver = new_solver (4, true, 0, false);
  assert (!kissat_get_score (solver, 0));
  assert (!kissat_tree_weight (&solver->policy.tree, 0).mantissa);
  for (unsigned idx = 1; idx < 4; idx++)
    assign (solver, idx);
  assert (kissat_policy_pick (solver) == 0);
  assert (solver->policy.count.picks[0] == 1);
  assert (solver->policy.count.fallbacks[0] == 1);
  assert (!solver->policy.count.fallbacks[1]);
  unassign (solver, 2);
  assert (kissat_policy_pick (solver) == 2);
  assert (solver->policy.count.fallbacks[0] == 1);
  kissat_release (solver);
  solver = new_solver (4, true, 0, true);
  assert (kissat_get_score (solver, 0) == 1.0);
  for (unsigned idx = 1; idx < 4; idx++)
    assign (solver, idx);
  assert (kissat_policy_pick (solver) == 0);
  assert (!solver->policy.count.fallbacks[0]);
  kissat_release (solver);
}

#endif

void tissat_schedule_policy (void) {
#if !defined(HEAPARGMAX) && !defined(NOPTIONS)
  SCHEDULE_FUNCTION (test_policy_start);
  SCHEDULE_FUNCTION (test_policy_sample);
  SCHEDULE_FUNCTION (test_policy_fallback);
#endif
}
