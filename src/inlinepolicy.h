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
// 'HeapArgmax' is the only policy in this build.  The scores are stored in
// its binary heap 'SCORES', and each function below performs the heap
// operation Kissat itself performs at that point.

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

#endif
