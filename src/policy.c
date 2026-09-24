#include "policy.h"
#include "inlinepolicy.h"
#include "logging.h"

#ifdef HEAPARGMAX

static unsigned heap_argmax_pick (kissat *solver) {
  heap *scores = SCORES;
  unsigned res = kissat_max_heap (scores);
  const value *const values = solver->values;
  while (values[LIT (res)]) {
    kissat_pop_max_heap (solver, scores);
    res = kissat_max_heap (scores);
  }
#if defined(LOGGING) || defined(CHECK_HEAP)
  const double score = kissat_get_heap_score (scores, res);
#endif
  LOG ("largest score unassigned %s score %g", LOGVAR (res), score);
#ifdef CHECK_HEAP
  for (all_variables (idx)) {
    if (!ACTIVE (idx))
      continue;
    if (VALUE (LIT (idx)))
      continue;
    const double idx_score = kissat_get_heap_score (scores, idx);
    assert (score >= idx_score);
  }
#endif
  return res;
}

unsigned kissat_policy_pick (kissat *solver) {
  assert (solver->stable);
  assert (solver->unassigned);
  return heap_argmax_pick (solver);
}

unsigned kissat_policy_peek (kissat *solver) {
  assert (solver->stable);
  assert (solver->unassigned);
  return heap_argmax_pick (solver);
}

void kissat_update_scores (kissat *solver) {
  assert (solver->stable);
  heap *scores = SCORES;
  for (all_variables (idx))
    if (ACTIVE (idx) && !kissat_heap_contains (scores, idx))
      kissat_push_heap (solver, scores, idx);
}

#else

#include "error.h"
#include "print.h"

#include <inttypes.h>

// Argmax: the tree's maximum, removing assigned variables from the tree
// on the way.  Each assigned variable is removed at most once per
// assignment and put back when backtracking unassigns it.

static unsigned tree_argmax_pick (kissat *solver) {
  tree *const tree = &solver->policy.tree;
  const value *const values = solver->values;
  unsigned res = kissat_tree_max (tree);
  assert (res != INVALID_IDX);
  while (values[LIT (res)]) {
    kissat_tree_remove (tree, res);
    res = kissat_tree_max (tree);
    assert (res != INVALID_IDX);
  }
#if defined(LOGGING) || defined(CHECK_HEAP)
  const double score = kissat_tree_key (tree, res);
#endif
  LOG ("largest score unassigned %s score %g", LOGVAR (res), score);
#ifdef CHECK_HEAP
  // Brute-force check of the argmax and of its tie-breaking ('--check-heap'
  // checks the policy structure of tree builds too).
  for (all_variables (idx)) {
    if (!ACTIVE (idx))
      continue;
    if (VALUE (LIT (idx)))
      continue;
    const double idx_score = kissat_get_score (solver, idx);
    if (idx < res)
      assert (score > idx_score);
    else
      assert (score >= idx_score);
  }
#endif
  return res;
}

#ifdef SHADOW

static void shadow_check_tree (kissat *);

// HeapArgmax's pick on the shadow heap must find the largest score the
// tree finds.  The two may pick different variables of that score, since
// the heap breaks ties by its history and the tree by variable index.

static void shadow_pick (kissat *solver, unsigned res) {
  policy *const policy = &solver->policy;
  heap *const scores = SCORES;
  const value *const values = solver->values;
  const uint64_t pick = ++policy->shadow.picks;
  if (kissat_empty_heap (scores))
    kissat_fatal ("shadow mode: heap empty at pick %" PRIu64, pick);
  unsigned top = kissat_max_heap (scores);
  while (values[LIT (top)]) {
    kissat_pop_max_heap (solver, scores);
    if (kissat_empty_heap (scores))
      kissat_fatal ("shadow mode: heap empty at pick %" PRIu64, pick);
    top = kissat_max_heap (scores);
  }
  const double heap_score = kissat_get_heap_score (scores, top);
  const double tree_score = kissat_tree_max_key (&policy->tree);
  if (!kissat_same_double (heap_score, tree_score))
    kissat_fatal ("shadow mode: pick %" PRIu64 ": largest score on the "
                  "heap %.17g (variable %u) differs from the largest in "
                  "the tree %.17g (variable %u)",
                  pick, heap_score, top, tree_score, res);
  if (!kissat_same_double (tree_score, solver->score[res]))
    kissat_fatal ("shadow mode: pick %" PRIu64 ": tree maximum %.17g "
                  "differs from the score %.17g of its variable %u",
                  pick, tree_score, solver->score[res], res);
  if (top != res)
    policy->shadow.differ++;
  if (!(pick % 1000))
    shadow_check_tree (solver);
}

// Every leaf against the estimator, the heap and the assignment; every
// internal node against its children.

static void shadow_check_tree (kissat *solver) {
  policy *const policy = &solver->policy;
  const tree *const tree = &policy->tree;
  heap *const scores = SCORES;
  const double *const score = solver->score;
  const flags *const flags = solver->flags;
  const value *const values = solver->values;
  const uint64_t check = ++policy->shadow.checks;
  const uint64_t pick = policy->shadow.picks;
  if (policy->bulk)
    kissat_fatal ("shadow mode: check %" PRIu64 " during a bulk change",
                  check);
  const unsigned leaves = tree->leaves;
  if (leaves < VARS)
    kissat_fatal ("shadow mode: check %" PRIu64 ": %u leaves for %u "
                  "variables",
                  check, leaves, VARS);
  for (all_variables (idx)) {
    const double s = score[idx];
    const double h = kissat_get_heap_score (scores, idx);
    if (!kissat_same_double (s, h))
      kissat_fatal ("shadow mode: pick %" PRIu64 ": score %.17g of "
                    "variable %u differs from its heap score %.17g",
                    pick, s, idx, h);
    const bool active = flags[idx].active;
    const bool available = active && !values[LIT (idx)];
    if (kissat_tree_contains (tree, idx)) {
      if (!active)
        kissat_fatal ("shadow mode: pick %" PRIu64 ": inactive variable "
                      "%u in the tree",
                      pick, idx);
      const double k = kissat_tree_key (tree, idx);
      if (!kissat_same_double (k, s))
        kissat_fatal ("shadow mode: pick %" PRIu64 ": leaf key %.17g of "
                      "variable %u differs from its score %.17g",
                      pick, k, idx, s);
    } else if (available)
      kissat_fatal ("shadow mode: pick %" PRIu64 ": unassigned active "
                    "variable %u missing from the tree",
                    pick, idx);
    if (available && !kissat_heap_contains (scores, idx))
      kissat_fatal ("shadow mode: pick %" PRIu64 ": unassigned active "
                    "variable %u missing from the heap",
                    pick, idx);
  }
  for (unsigned idx = VARS; idx < leaves; idx++)
    if (kissat_tree_contains (tree, idx))
      kissat_fatal ("shadow mode: pick %" PRIu64 ": leaf %u beyond the "
                    "%u variables present",
                    pick, idx, VARS);
  const unsigned node = kissat_tree_inconsistent_node (tree);
  if (node)
    kissat_fatal ("shadow mode: pick %" PRIu64 ": tree node %u differs "
                  "from what its children give",
                  pick, node);
}

void kissat_print_shadow_statistics (kissat *solver) {
#ifndef QUIET
  const policy *const policy = &solver->policy;
  kissat_message (solver, "shadow-picks %" PRIu64, policy->shadow.picks);
  kissat_message (solver, "shadow-differ %" PRIu64, policy->shadow.differ);
  kissat_message (solver, "shadow-checks %" PRIu64, policy->shadow.checks);
  kissat_message (solver, "shadow-rebuilds %" PRIu64,
                  policy->shadow.rebuilds);
#else
  (void) solver;
#endif
}

#endif

unsigned kissat_policy_pick (kissat *solver) {
  assert (solver->stable);
  assert (solver->unassigned);
  assert (!solver->policy.bulk);
  const unsigned res = tree_argmax_pick (solver);
#ifdef SHADOW
  shadow_pick (solver, res);
#endif
  assert (ACTIVE (res));
  assert (!VALUE (LIT (res)));
  return res;
}

unsigned kissat_policy_peek (kissat *solver) {
  assert (solver->stable);
  assert (solver->unassigned);
  assert (!solver->policy.bulk);
  const unsigned res = tree_argmax_pick (solver);
  assert (ACTIVE (res));
  assert (!VALUE (LIT (res)));
  return res;
}

// Every active variable becomes available.  The heap's order of pushes
// does not matter to the tree, which is a function of its leaves.

void kissat_update_scores (kissat *solver) {
  assert (solver->stable);
#ifdef SHADOW
  heap *scores = SCORES;
  for (all_variables (idx))
    if (ACTIVE (idx) && !kissat_heap_contains (scores, idx))
      kissat_push_heap (solver, scores, idx);
#endif
  tree *const tree = &solver->policy.tree;
  bool added = false;
  for (all_variables (idx))
    if (ACTIVE (idx) && !kissat_tree_contains (tree, idx)) {
      kissat_tree_put (tree, idx, solver->score[idx], 0);
      added = true;
    }
  if (added)
    kissat_rebuild_policy (solver);
}

// Present leaves take their keys from the estimator again, then every
// internal node is recomputed.

void kissat_rebuild_policy (kissat *solver) {
  tree *const tree = &solver->policy.tree;
  const double *const score = solver->score;
  LOG ("rebuilding policy tree");
  for (all_variables (idx))
    if (kissat_tree_contains (tree, idx))
      kissat_tree_put (tree, idx, score[idx], 0);
  kissat_rebuild_tree (tree);
#ifdef SHADOW
  solver->policy.shadow.rebuilds++;
#endif
}

void kissat_seed_policy (kissat *solver) {
  const unsigned seed = GET_OPTION (policyseed);
  solver->policy.random = kissat_policy_generator (seed);
  LOG ("initialized policy random number generator with seed %u", seed);
}

#endif
