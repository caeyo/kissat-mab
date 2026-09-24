#ifndef _policy_h_INCLUDED
#define _policy_h_INCLUDED

// Stable-mode decision policy: the map from the scores of the unassigned
// active variables to the next decision variable.  It is the only part of
// variable selection that differs between the arms of the experiment.
//
// 'kissat_next_decision_variable' calls 'kissat_policy_pick' for every
// stable-mode decision that is not a random decision; Kissat's random
// decision bursts ('randec') remain a separate decision source in front of
// the policy.  Callers of 'kissat_next_decision_variable' include warm-up
// and the trail-reuse peek of restarts, which therefore see the policy too.
//
// The policy reads scores from the estimator and is told about every
// change of availability of a variable; both halves of that interface are
// in 'inlinepolicy.h'.  'kissat_update_scores' is the hook for entering
// stable mode, at the start of the search with '--stable=2' and at every
// switch to stable mode: every active variable becomes available.
//
// HeapArgmax: the variable of largest score on the binary heap 'SCORES',
// popping assigned variables off the heap on the way (lazy deletion).
// This is Kissat's own stable-mode heuristic, unchanged.

struct kissat;

unsigned kissat_policy_pick (struct kissat *);
void kissat_update_scores (struct kissat *);

#endif
