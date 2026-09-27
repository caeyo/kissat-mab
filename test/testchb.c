#include "../src/backtrack.h"
#include "../src/chb.h"
#include "../src/decide.h"
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
  solver->assigned[idx].trail = SIZE_ARRAY (solver->trail);
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

  // Variable 0, paid while it stayed assigned, still has the leaf of its
  // initial Q = 0, and backtracking refreshes it.
  assert (kissat_tree_key (tree, 0) == 0);
  assert (kissat_get_score (solver, 0) == q0);
  shrink (solver, 0);
  for (unsigned idx = 0; idx < 4; idx++) {
    assert (kissat_tree_contains (tree, idx));
    assert (kissat_tree_key (tree, idx) == kissat_get_score (solver, idx));
  }
  assert (!kissat_tree_inconsistent_node (tree));
  kissat_release (solver);
}

// Every leaf of the tree is present, has its variable's score as key and,
// in a weighted tree, the weight that score gives, and every internal node
// is what its children give: the tree is bitwise the one a rebuild makes.

static void check_fresh_tree (kissat *solver) {
  const policy *const policy = &solver->policy;
  const tree *const tree = &policy->tree;
  for (all_variables (idx)) {
    assert (kissat_tree_contains (tree, idx));
    const double score = kissat_get_score (solver, idx);
    assert (kissat_same_double (kissat_tree_key (tree, idx), score));
    if (!tree->weighted)
      continue;
    const tree_weight expected = kissat_tree_weight_of_log2 (
        kissat_policy_log2_weight (policy, score));
    assert (kissat_tree_same_weight (kissat_tree_weight (tree, idx),
                                     expected));
  }
  assert (!kissat_tree_inconsistent_node (tree));
}

// A payment changes the score of an assigned variable but not its leaf,
// which lags until backtracking unassigns the variable.  Argmax meets a
// lagging leaf only as an assigned variable, which it removes, so it picks
// the largest score among the unassigned variables as before, and the
// removed variable comes back with its current score.

static void test_chb_lagging_argmax (void) {
  kissat *solver = new_solver (4, false, 0);
  const tree *const tree = &solver->policy.tree;
  const double initial[4] = {0.1, 0.2, 0.95, 0.3};
  for (unsigned idx = 0; idx < 4; idx++)
    kissat_update_score (solver, idx, initial[idx]);
  check_fresh_tree (solver);

  // Paid without a conflict at age 1: Q = 0.6 * 0.95 + 0.4 * 0.9.
  kissat_internal_assume (solver, LIT (2));
  kissat_chb_assign (solver, false);
  const double q2 = erwa (0.95, 0.4, 0.9);
  assert (kissat_get_score (solver, 2) == q2);
  assert (q2 < 0.95);
  assert (kissat_tree_key (tree, 2) == 0.95);
  assert (kissat_tree_max (tree) == 2);
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (kissat_tree_key (tree, 2) == q2);
  check_fresh_tree (solver);

  // Paid again, and met by a pick while assigned: removed, and put back
  // with its score when backtracking unassigns it.
  kissat_internal_assume (solver, LIT (2));
  kissat_chb_assign (solver, true);
  const double q2_again = erwa (q2, 0.4, 1.0);
  assert (kissat_get_score (solver, 2) == q2_again);
  assert (kissat_tree_key (tree, 2) == q2);
  assert (kissat_policy_pick (solver) == 3);
  assert (!kissat_tree_contains (tree, 2));
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (kissat_tree_key (tree, 2) == q2_again);
  check_fresh_tree (solver);
  assert (kissat_policy_pick (solver) == 2);
  kissat_release (solver);
}

// Sample-CHB through the solver's backtracking: 45 decisions paid with
// different rewards, picks whose draws meet and remove paid variables, a
// backtrack of 5 literals, which updates every path at once, and one of
// 40, which defers its sums.  Afterwards the tree is bitwise the one a
// rebuild makes.

static void test_chb_lagging_sample (void) {
  kissat *solver = new_solver (64, true, 4);
  const tree *const tree = &solver->policy.tree;
  assert (tree->weighted);
  for (unsigned idx = 0; idx < 45; idx++) {
    kissat_internal_assume (solver, LIT (idx));
    kissat_chb_assign (solver, !(idx % 3));
  }
  for (unsigned idx = 0; idx < 45; idx++) {
    assert (kissat_get_score (solver, idx) > 0);
    assert (kissat_tree_key (tree, idx) == 0);
  }
  for (unsigned i = 0; i < 3; i++)
    assert (kissat_policy_pick (solver) >= 45);
  unsigned removed = 0;
  for (unsigned idx = 0; idx < 45; idx++)
    removed += !kissat_tree_contains (tree, idx);
  assert (removed > 0), assert (removed < 45);
  kissat_backtrack_without_updating_phases (solver, 40);
  for (unsigned idx = 0; idx < 45; idx++)
    if (idx >= 40)
      assert (kissat_tree_key (tree, idx) == kissat_get_score (solver, idx));
    else if (kissat_tree_contains (tree, idx))
      assert (kissat_tree_key (tree, idx) == 0);
  assert (!kissat_tree_inconsistent_node (tree));
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (!tree->deferring);
  check_fresh_tree (solver);
  kissat_release (solver);
}

// Chronological backtracking keeps a literal of a lower level that lies
// above the new level's trail and moves it down.  A paid literal so kept
// stays below the paid trail position, its leaf lags until it is
// unassigned, and then it is refreshed.

static void test_chb_lagging_kept (void) {
  kissat *solver = new_solver (4, true, 4);
  const tree *const tree = &solver->policy.tree;
  kissat_internal_assume (solver, LIT (0)); // level 1, trail position 0
  kissat_internal_assume (solver, LIT (1)); // level 2, trail position 1
  kissat_internal_assume (solver, LIT (2)); // trail position 2
  solver->assigned[2].level = 1;            // out of order on level 1
  kissat_chb_assign (solver, false);
  assert (solver->estimator.chb.played == 3);
  kissat_backtrack_without_updating_phases (solver, 1);
  assert (!VALUE (LIT (1)) && VALUE (LIT (2)));
  assert (solver->assigned[2].trail == 1);
  assert (solver->estimator.chb.played == 2);
  assert (kissat_tree_key (tree, 1) == kissat_get_score (solver, 1));
  assert (kissat_tree_key (tree, 2) == 0);
  assert (kissat_get_score (solver, 2) > 0);
  kissat_backtrack_without_updating_phases (solver, 0);
  check_fresh_tree (solver);
  kissat_release (solver);
}

// Focused mode unassigns without the policy's hooks, so a leaf that lagged
// when stable mode was left belongs to an unassigned variable afterwards.
// Entering stable mode rebuilds the tree, though no variable is added.

static void test_chb_lagging_modes (void) {
  kissat *solver = new_solver (4, true, 2);
  const tree *const tree = &solver->policy.tree;
  kissat_internal_assume (solver, LIT (1));
  kissat_chb_assign (solver, true);
  solver->stable = false;
  kissat_backtrack_without_updating_phases (solver, 0);
  assert (kissat_tree_contains (tree, 1));
  assert (kissat_tree_key (tree, 1) == 0);
  assert (kissat_get_score (solver, 1) == erwa (0, 0.4, 1.0));
  solver->stable = true;
  kissat_update_scores (solver);
  check_fresh_tree (solver);
  kissat_release (solver);
}

// Backtracks defer their sums only under CHB, only in a weighted tree
// (Sample) and only from 'POLICY_DEFER_SUMS' literals on.

static void test_chb_defer_condition (void) {
  kissat *solver = new_solver (40, true, 4);
  tree *const tree = &solver->policy.tree;
  kissat_defer_policy_sums (solver, POLICY_DEFER_SUMS - 1);
  assert (!tree->deferring);
  kissat_defer_policy_sums (solver, POLICY_DEFER_SUMS);
  assert (tree->deferring);
  kissat_flush_policy_sums (solver);
  assert (!tree->deferring);
  kissat_release (solver);

  solver = new_solver (40, false, 0);
  kissat_defer_policy_sums (solver, 40);
  assert (!solver->policy.tree.deferring);
  kissat_flush_policy_sums (solver);
  kissat_release (solver);

  solver = kissat_init ();
  kissat_set_option (solver, "softmax", 1);
  for (unsigned i = 1; i <= 40; i++)
    kissat_add (solver, (int) i);
  kissat_add (solver, 0);
  solver->stable = true;
  kissat_update_scores (solver);
  kissat_start_policy (solver);
  assert (solver->policy.tree.weighted);
  kissat_defer_policy_sums (solver, 40);
  assert (!solver->policy.tree.deferring);
  kissat_flush_policy_sums (solver);
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
  SCHEDULE_FUNCTION (test_chb_lagging_argmax);
  SCHEDULE_FUNCTION (test_chb_lagging_sample);
  SCHEDULE_FUNCTION (test_chb_lagging_kept);
  SCHEDULE_FUNCTION (test_chb_lagging_modes);
  SCHEDULE_FUNCTION (test_chb_defer_condition);
  SCHEDULE_FUNCTION (test_chb_sample);
#endif
}
