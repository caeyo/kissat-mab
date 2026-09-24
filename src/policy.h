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
// HeapArgmax: the variable of largest score on the binary heap 'SCORES',
// popping assigned variables off the heap on the way (lazy deletion).
// This is Kissat's own stable-mode heuristic, unchanged.

struct kissat;

unsigned kissat_policy_pick (struct kissat *);

#endif
