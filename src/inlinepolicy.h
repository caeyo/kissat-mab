#ifndef _inlinepolicy_h_INCLUDED
#define _inlinepolicy_h_INCLUDED

// Inline half of the interface between the solver and the stable-mode
// decision policy (see 'policy.h'), for the hot paths.
//
// Estimator: the score vector, one score per variable (Kissat's VSIDS
// activities).  Scores change by bumping and rescaling ('bump.c'),
// 'reorder', activation and bounded variable addition ('factor.c').  Code
// outside the estimator and the policy reads and writes scores only
// through 'kissat_get_score' and 'kissat_update_score', and rescales them
// only through 'kissat_max_score' and 'kissat_scale_scores'.  Every write
// reaches the live policy structure.
//
// Policy structure: the variables the policy may pick.  The solver reports
// every change of availability through the 'kissat_policy_*' hooks below
// and, on entering stable mode, through 'kissat_update_scores'.
// Assignment needs no hook: assigned variables are dropped lazily, when
// the policy meets them.
//
// A bulk score change ('reorder') is bracketed by
// 'kissat_begin_bulk_score_change' and 'kissat_end_bulk_score_change'.  In
// between, score writes, rescaling included, go to the estimator only, and
// the end rebuilds the policy structure once, in linear time.
//
// HeapArgmax builds: the scores are stored in the binary heap 'SCORES',
// and each function below performs the heap operation Kissat itself
// performs at that point.  Bulk changes go through the heap one write at a
// time, as in Kissat.
//
// Tree builds: the scores are stored in the estimator's array 'score',
// and the policy structure is the tree of 'policy.h', whose leaves hold a
// copy of the score of every available variable and, under Sample, its
// weight.  A rescale rebuilds the tree, since multiplying every score by
// the same factor can create ties and changes every weight.  Shadow
// builds apply every change to the heap 'SCORES' too.
//
// The pseudo-activity (all builds, see 'estimator' in 'policy.h') is
// added to a score where Kissat sets it at activation and after bounded
// variable addition.
//
// With CHB scores (tree builds, 'chb=1', see 'chb.h') a score is the
// variable's ERWA value Q: it starts at zero at activation, there is no
// pseudo-activity, and CHB pays it after every search propagation.

#include "chb.h"
#include "internal.h"

static inline double kissat_pseudo_activity (kissat *solver) {
#ifndef HEAPARGMAX
  if (kissat_chb (solver))
    return 0;
#endif
  return GET_OPTION (pseudoactivity) ? solver->estimator.pseudo : 0;
}

// The score a variable starts with at activation: for the k-th activated
// variable Kissat's 1 - 1/k plus the pseudo-activity, or Q = 0 under CHB.

static inline double kissat_initial_score (kissat *solver) {
#ifndef HEAPARGMAX
  if (kissat_chb (solver))
    return 0;
#endif
  double score = 1.0 - 1.0 / solver->statistics.variables_activated;
  score += kissat_pseudo_activity (solver);
  return score;
}

#ifdef HEAPARGMAX

#include "inlineheap.h"

static inline double kissat_get_score (kissat *solver, unsigned idx) {
  return kissat_get_heap_score (SCORES, idx);
}

static inline void kissat_update_score (kissat *solver, unsigned idx,
                                        double score) {
  kissat_update_heap (solver, SCORES, idx, score);
}

// The largest score stored for any variable, active or not, assigned or
// not (0 if no score was ever changed).  This is the reference of the
// estimator's rescaling, not the policy's maximum ('kissat_policy_peek').

static inline double kissat_max_score (kissat *solver) {
  return kissat_max_score_on_heap (SCORES);
}

static inline void kissat_scale_scores (kissat *solver, double factor) {
  kissat_rescale_heap (solver, SCORES, factor);
}

// Backtracking in stable mode unassigned 'idx'.

static inline void kissat_policy_unassign (kissat *solver, unsigned idx) {
  heap *scores = SCORES;
  if (!kissat_heap_contains (scores, idx))
    kissat_push_heap (solver, scores, idx);
}

// 'idx' was activated in stable mode and is unassigned.

static inline void kissat_policy_activate (kissat *solver, unsigned idx) {
  kissat_push_heap (solver, SCORES, idx);
}

// 'idx' was fixed or eliminated, in either mode.

static inline void kissat_policy_deactivate (kissat *solver, unsigned idx) {
  heap *scores = SCORES;
  if (kissat_heap_contains (scores, idx))
    kissat_pop_heap (solver, scores, idx);
}

static inline void kissat_begin_bulk_score_change (kissat *solver) {
  (void) solver;
}

static inline void kissat_end_bulk_score_change (kissat *solver) {
  (void) solver;
}

#else

#include "inlinetree.h"
#include "internal.h"
#include "logging.h"

#ifdef SHADOW
#include "inlineheap.h"
#endif

static inline double kissat_get_score (kissat *solver, unsigned idx) {
  assert (idx < VARS);
  return solver->score[idx];
}

// Sample's weight of a score, score^eta, as the tree takes it: its base-2
// logarithm eta * log2 (score), exact in the multiplication since eta is a
// power of two.  Minus infinity (weight zero) for a score of zero.  With
// CHB scores the weight of Q is exp (eta * Q), i.e. eta * Q * log2 (e),
// at least zero (weight one).

#define KISSAT_LOG2_E 1.4426950408889634

static inline double kissat_policy_log2_weight (const policy *policy,
                                                double score) {
  assert (score >= 0);
  if (policy->chb)
    return ldexp (score * KISSAT_LOG2_E, policy->etalog2);
  return ldexp (log2 (score), policy->etalog2);
}

// The key and, in a weighted tree, the weight of an available variable.

static inline void kissat_policy_set_leaf (kissat *solver, unsigned idx) {
  policy *const policy = &solver->policy;
  tree *const tree = &policy->tree;
  const double score = solver->score[idx];
  const double log2_weight =
      tree->weighted ? kissat_policy_log2_weight (policy, score) : 0;
  kissat_tree_set (tree, idx, score, log2_weight);
}

// The same without recomputing the ancestors, for rebuilds.

static inline void kissat_policy_put_leaf (kissat *solver, unsigned idx) {
  policy *const policy = &solver->policy;
  tree *const tree = &policy->tree;
  const double score = solver->score[idx];
  const double log2_weight =
      tree->weighted ? kissat_policy_log2_weight (policy, score) : 0;
  kissat_tree_put (tree, idx, score, log2_weight);
}

static inline void kissat_update_score (kissat *solver, unsigned idx,
                                        double score) {
  assert (idx < VARS);
  double *const p = solver->score + idx;
  const double old_score = *p;
  if (old_score == score)
    return;
  LOG ("update score of %s from %g to %g", LOGVAR (idx), old_score,
       score);
  *p = score;
#ifdef SHADOW
  kissat_update_heap (solver, SCORES, idx, score);
#endif
  policy *const policy = &solver->policy;
  if (policy->bulk)
    return;
  if (kissat_tree_contains (&policy->tree, idx))
    kissat_policy_set_leaf (solver, idx);
}

// The largest score stored for any variable, active or not, assigned or
// not (0 if no score was ever changed).  This is the reference of the
// estimator's rescaling, not the policy's maximum ('kissat_policy_peek').
// Scores are never negative, so starting from zero gives what the heap's
// scan gives.

static inline double kissat_max_score (kissat *solver) {
  const double *const score = solver->score;
  double res = 0;
  for (all_variables (idx))
    res = MAX (res, score[idx]);
  return res;
}

static inline void kissat_scale_scores (kissat *solver, double factor) {
  LOG ("rescaling scores with factor %g", factor);
  double *const score = solver->score;
  for (all_variables (idx))
    score[idx] *= factor;
#ifdef SHADOW
  kissat_rescale_heap (solver, SCORES, factor);
#endif
  if (!solver->policy.bulk)
    kissat_rebuild_policy (solver);
}

// Backtracking in stable mode unassigned 'idx'.

static inline void kissat_policy_unassign (kissat *solver, unsigned idx) {
  assert (!solver->policy.bulk);
#ifdef SHADOW
  heap *scores = SCORES;
  if (!kissat_heap_contains (scores, idx))
    kissat_push_heap (solver, scores, idx);
#endif
  if (!kissat_tree_contains (&solver->policy.tree, idx))
    kissat_policy_set_leaf (solver, idx);
}

// 'idx' was activated in stable mode and is unassigned.

static inline void kissat_policy_activate (kissat *solver, unsigned idx) {
  assert (!solver->policy.bulk);
#ifdef SHADOW
  kissat_push_heap (solver, SCORES, idx);
#endif
  assert (!kissat_tree_contains (&solver->policy.tree, idx));
  kissat_policy_set_leaf (solver, idx);
}

// 'idx' was fixed or eliminated, in either mode.

static inline void kissat_policy_deactivate (kissat *solver, unsigned idx) {
  assert (!solver->policy.bulk);
#ifdef SHADOW
  heap *scores = SCORES;
  if (kissat_heap_contains (scores, idx))
    kissat_pop_heap (solver, scores, idx);
#endif
  tree *const tree = &solver->policy.tree;
  if (kissat_tree_contains (tree, idx))
    kissat_tree_remove (tree, idx);
}

static inline void kissat_begin_bulk_score_change (kissat *solver) {
  assert (!solver->policy.bulk);
  solver->policy.bulk = true;
}

static inline void kissat_end_bulk_score_change (kissat *solver) {
  assert (solver->policy.bulk);
  solver->policy.bulk = false;
  kissat_rebuild_policy (solver);
}

#endif

#endif
