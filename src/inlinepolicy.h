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
// CHB pays only assigned variables, and the weight of an assigned variable
// matters only once it is unassigned again.  So a payment writes the
// estimator only ('kissat_update_assigned_score'), and the variable's leaf,
// which lazy deletion may still keep in the tree, lags its score until
// backtracking unassigns the variable and 'kissat_policy_unassign'
// refreshes the leaf.  The leaves of unassigned variables never lag, so
// Argmax's choice and the distribution of Sample's picks are unchanged;
// what changes is the weight of the assigned variables in the tree, and
// with it which assigned variables Sample's draws meet, and so its random
// stream and its trajectory.
//
// Under CHB a stable-mode backtrack, which refreshes the leaves of the
// variables it unassigns, is bracketed by 'kissat_defer_policy_sums' and
// 'kissat_flush_policy_sums'.  If it takes back at least
// 'POLICY_DEFER_SUMS' literals, a weighted tree (Sample) defers the sums
// above the changed leaves in between, and the flush recomputes each of
// them once (see 'tree.h'); the tree is then bitwise what updating every
// path at once would have made it.  The policy never picks in between.
// Smaller backtracks, the backtracks of the VSIDS line (reinsertions only)
// and the writes of bump rounds update every path at once: in the
// profiling task's timing deferring bump rounds and backtracks saved
// nothing, or cost time on small batches, while CHB's large payment
// rounds, whose paths share most of their nodes, gained.  Those payments
// now reach the tree when backtracking takes their variables back.
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
// the same factor can create ties and changes every weight.  With mixing
// (option 'gammappm') the availability hooks also keep the indicator tree
// of 'indicator.h', which holds no scores.  Shadow builds apply every
// change to the heap 'SCORES' too.
//
// The pseudo-activity (all builds, see 'estimator' in 'policy.h') is
// added to a score where Kissat sets it at activation and after bounded
// variable addition.
//
// With CHB scores (tree builds, 'chb=1', see 'chb.h') a score is the
// variable's ERWA value Q: it starts at zero at activation, there is no
// pseudo-activity, and CHB pays it after every search propagation, to the
// variables the propagation assigned (see above for their leaves).
//
// Under P1, TS and UCB (tree builds, see 'keys.h') a leaf holds the
// variable's key, its score combined with a term of the policy's own,
// instead of its score ('kissat_policy_key').  Bumps go through
// 'kissat_bump_score', where TS recomputes the term, CHB's payments count
// observations for UCB and TS, and UCB recomputes a variable's term when
// stable-mode backtracking unassigns it.

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

// A bump of 'idx' to 'score' (stable mode, VSIDS scores).

static inline void kissat_bump_score (kissat *solver, unsigned idx,
                                      double score) {
  kissat_update_score (solver, idx, score);
}

#else

#include "bump.h"
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

// The key of 'idx' in the tree: its score, or under P1, TS and UCB its
// score with the variable's term (see 'keys.h'): s * e^x on VSIDS scores,
// where 'term' holds e^x and a score of zero keeps key zero, and Q + x on
// CHB scores, where 'term' holds x.

static inline double kissat_policy_key (kissat *solver, unsigned idx) {
  const double score = solver->score[idx];
  const policy *const policy = &solver->policy;
  if (!policy->keys.kind)
    return score;
  const double term = policy->keys.term[idx];
  if (policy->chb)
    return score + term;
  return score > 0 ? score * term : 0;
}

// The terms of TS and UCB (see 'keys.h'), as 'term' holds them: TS's for
// the evidence 'evidence' of 'idx' (S on VSIDS scores, N on CHB scores),
// UCB's for 'count' observations.

static inline double kissat_thompson_term (const policy *policy,
                                           unsigned idx, double evidence) {
  const keys *const keys = &policy->keys;
  assert (keys->kind == KEYS_THOMPSON);
  const double x =
      keys->factor * keys->normal[idx] / sqrt (KEYS_PRIOR + evidence);
  return policy->chb ? x : exp (x);
}

static inline double kissat_ucb_term (const policy *policy, double count) {
  const keys *const keys = &policy->keys;
  assert (keys->kind == KEYS_UCB);
  const double x = keys->scale / sqrt (KEYS_PRIOR + count);
  return policy->chb ? x : exp (x);
}

// The key and, in a weighted tree, the weight of an available variable.

static inline void kissat_policy_set_leaf (kissat *solver, unsigned idx) {
  policy *const policy = &solver->policy;
  tree *const tree = &policy->tree;
  const double key = kissat_policy_key (solver, idx);
  const double log2_weight =
      tree->weighted ? kissat_policy_log2_weight (policy, key) : 0;
  kissat_tree_set (tree, idx, key, log2_weight);
}

// The same without recomputing the ancestors, for rebuilds.

static inline void kissat_policy_put_leaf (kissat *solver, unsigned idx) {
  policy *const policy = &solver->policy;
  tree *const tree = &policy->tree;
  const double key = kissat_policy_key (solver, idx);
  const double log2_weight =
      tree->weighted ? kissat_policy_log2_weight (policy, key) : 0;
  kissat_tree_put (tree, idx, key, log2_weight);
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

// CHB's payment of the assigned variable 'idx': the estimator (and the
// heap of shadow builds) gets the new score, the tree does not.  Its leaf,
// if lazy deletion still keeps it, lags the score until backtracking
// unassigns the variable ('kissat_policy_unassign').

static inline void kissat_update_assigned_score (kissat *solver,
                                                 unsigned idx,
                                                 double score) {
  assert (idx < VARS);
  assert (VALUE (LIT (idx)));
  double *const p = solver->score + idx;
  const double old_score = *p;
  if (old_score == score)
    return;
  LOG ("update score of assigned %s from %g to %g", LOGVAR (idx),
       old_score, score);
  *p = score;
#ifdef SHADOW
  kissat_update_heap (solver, SCORES, idx, score);
#endif
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

// UCB's counts on VSIDS scores are kept in units of the score increment,
// and are rescaled with the scores, as are the increments at assignment.

static inline void kissat_scale_scores (kissat *solver, double factor) {
  LOG ("rescaling scores with factor %g", factor);
  double *const score = solver->score;
  for (all_variables (idx))
    score[idx] *= factor;
#ifdef SHADOW
  kissat_rescale_heap (solver, SCORES, factor);
#endif
  if (solver->policy.keys.intervals)
    kissat_rescale_keys (solver, factor);
  if (!solver->policy.bulk)
    kissat_rebuild_policy (solver);
}

// UCB on VSIDS scores: the literals assigned since the last record get the
// current score increment, the one they were assigned at, since it has
// not changed since (see 'keys.h').  Called before the increment changes,
// before every stable-mode backtrack and when stable mode is left.

static inline void kissat_record_keys (kissat *solver) {
  keys *const keys = &solver->policy.keys;
  if (!keys->intervals)
    return;
  const unsigned size = SIZE_ARRAY (solver->trail);
  unsigned counted = keys->counted;
  if (counted >= size)
    return;
  const unsigned *const trail = BEGIN_ARRAY (solver->trail);
  double *const opened = keys->opened;
  const double inc = solver->scinc;
  while (counted < size) {
    const unsigned lit = trail[counted++];
    opened[IDX (lit)] = inc;
  }
  keys->counted = size;
}

// The trail was shrunk to 'size' literals: CHB's paid position and UCB's
// recorded position follow it down.

static inline void kissat_policy_shrink_trail (kissat *solver,
                                               unsigned size) {
  kissat_chb_shrink_trail (solver, size);
  unsigned *const counted = &solver->policy.keys.counted;
  if (*counted > size)
    *counted = size;
}

// P1, TS and UCB: backtracking in stable mode unassigned 'idx'.  On VSIDS
// scores UCB adds the increments of the bump rounds since its assignment
// to its count, and on either line recomputes its term.  The leaf is set
// if a pick removed it, or if its key changed: by UCB's term, or on CHB
// scores by payments while the variable was assigned.

static inline void kissat_keys_unassign (kissat *solver, unsigned idx) {
  policy *const policy = &solver->policy;
  keys *const keys = &policy->keys;
  if (keys->kind == KEYS_UCB) {
    double inc;
    if (policy->chb)
      inc = keys->increment;
    else {
      inc = solver->scinc;
      assert (keys->intervals);
      assert (solver->assigned[idx].trail < keys->counted);
      keys->count[idx] += (inc - keys->opened[idx]) / (keys->growth - 1);
    }
    keys->term[idx] = kissat_ucb_term (policy, keys->count[idx] / inc);
  }
  tree *const tree = &policy->tree;
  assert (!tree->weighted);
  const double key = kissat_policy_key (solver, idx);
  if (!kissat_tree_contains (tree, idx) ||
      kissat_tree_key (tree, idx) != key)
    kissat_tree_set (tree, idx, key, 0);
}

// CHB's payment of 'idx' under UCB and TS: an observation, counted with
// the counts' current increment, and TS's term follows the new count.  As
// for the score, the leaf takes the new key when backtracking unassigns
// the variable.

static inline void kissat_keys_paid (kissat *solver, unsigned idx) {
  policy *const policy = &solver->policy;
  keys *const keys = &policy->keys;
  assert (keys->counts);
  const double inc = keys->increment;
  const double count = keys->count[idx] += inc;
  if (keys->kind == KEYS_THOMPSON)
    keys->term[idx] = kissat_thompson_term (policy, idx, count / inc);
}

// A stable-mode conflict on CHB scores, after its payments: the counts'
// increment grows by 1/d.

static inline void kissat_keys_chb_conflict (kissat *solver) {
  keys *const keys = &solver->policy.keys;
  assert (keys->counts);
  keys->increment *= keys->growth;
  if (keys->increment > MAX_SCORE)
    kissat_rescale_chb_counts (solver);
}

// Backtracking in stable mode unassigned 'idx'.  The tree and, with
// mixing, the indicator tree get it back if a draw of theirs removed it.
// Under CHB a leaf the tree kept is refreshed if it lags the score, which
// CHB's payments changed while the variable was assigned.  P1, TS and UCB
// compare the leaf with the variable's key instead.

static inline void kissat_policy_unassign (kissat *solver, unsigned idx) {
  assert (!solver->policy.bulk);
#ifdef SHADOW
  heap *scores = SCORES;
  if (!kissat_heap_contains (scores, idx))
    kissat_push_heap (solver, scores, idx);
#endif
  policy *const policy = &solver->policy;
  const tree *const tree = &policy->tree;
  if (policy->keys.kind)
    kissat_keys_unassign (solver, idx);
  else if (!kissat_tree_contains (tree, idx) ||
           (kissat_chb (solver) &&
            kissat_tree_key (tree, idx) != solver->score[idx]))
    kissat_policy_set_leaf (solver, idx);
  indicator *const uniform = &policy->uniform;
  if (uniform->enabled && !kissat_indicator_contains (uniform, idx))
    kissat_indicator_insert (uniform, idx);
}

// 'idx' was activated in stable mode and is unassigned.  Under P1 and TS
// it draws, and under UCB gets its term, before its leaf is set.

static inline void kissat_policy_activate (kissat *solver, unsigned idx) {
  assert (!solver->policy.bulk);
#ifdef SHADOW
  kissat_push_heap (solver, SCORES, idx);
#endif
  policy *const policy = &solver->policy;
  assert (!kissat_tree_contains (&policy->tree, idx));
  if (policy->keys.kind)
    kissat_activate_keys (solver, idx);
  kissat_policy_set_leaf (solver, idx);
  indicator *const uniform = &policy->uniform;
  if (uniform->enabled)
    kissat_indicator_insert (uniform, idx);
}

// 'idx' was fixed or eliminated, in either mode.

static inline void kissat_policy_deactivate (kissat *solver, unsigned idx) {
  assert (!solver->policy.bulk);
#ifdef SHADOW
  heap *scores = SCORES;
  if (kissat_heap_contains (scores, idx))
    kissat_pop_heap (solver, scores, idx);
#endif
  policy *const policy = &solver->policy;
  tree *const tree = &policy->tree;
  if (kissat_tree_contains (tree, idx))
    kissat_tree_remove (tree, idx);
  indicator *const uniform = &policy->uniform;
  if (uniform->enabled && kissat_indicator_contains (uniform, idx))
    kissat_indicator_remove (uniform, idx);
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

// A bump of 'idx' to 'score' (stable mode, VSIDS scores).  Under TS the
// variable's term follows the new score, S = score / inc, first, and its
// leaf follows the term even if the increment was too small to change the
// score.

static inline void kissat_bump_score (kissat *solver, unsigned idx,
                                      double score) {
  policy *const policy = &solver->policy;
  if (policy->keys.kind == KEYS_THOMPSON) {
    assert (!policy->chb);
    assert (!policy->bulk);
    double *const term = policy->keys.term + idx;
    const double new_term =
        kissat_thompson_term (policy, idx, score / solver->scinc);
    if (*term != new_term) {
      *term = new_term;
      if (solver->score[idx] == score &&
          kissat_tree_contains (&policy->tree, idx))
        kissat_policy_set_leaf (solver, idx);
    }
  }
  kissat_update_score (solver, idx, score);
}

#define POLICY_DEFER_SUMS 32

// A stable-mode backtrack takes back 'size' literals (see above).

static inline void kissat_defer_policy_sums (kissat *solver,
                                             unsigned size) {
  tree *const tree = &solver->policy.tree;
  if (tree->weighted && size >= POLICY_DEFER_SUMS && kissat_chb (solver))
    kissat_tree_defer (tree);
}

static inline void kissat_flush_policy_sums (kissat *solver) {
  tree *const tree = &solver->policy.tree;
  if (tree->deferring)
    kissat_tree_flush (tree);
}

#ifdef DECISION_METRICS

// A stable-mode decision chose 'idx', a random decision of a burst if
// 'random' and a pick of the policy otherwise, and choosing it began when
// the clock read 'start'.  Counts and times the decision and has every
// 'metricsint'-th one of its phase sampled, with 'metricsvars' every
// 'VARS'-th if there are more variables (see 'policy.h').

static inline void kissat_policy_decided (kissat *solver, unsigned idx,
                                          bool random, uint64_t start) {
  assert (solver->stable);
  policy_metrics *const metrics = solver->policy.metrics + solver->warming;
  const uint64_t stop = kissat_policy_clock ();
  if (stop > start) // time-stamp counters of cores out of step
    metrics->ticks += stop - start;
  metrics->decisions++;
  metrics->random += random;
  const unsigned interval = GET_OPTION (metricsint);
  if (!interval)
    return;
  const unsigned spacing =
      GET_OPTION (metricsvars) && VARS > interval ? VARS : interval;
  if (++metrics->since < spacing)
    return;
  metrics->since = 0;
  kissat_sample_decision (solver, idx, random);
}

#endif

#endif

#endif
