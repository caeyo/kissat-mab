#ifndef _policy_h_INCLUDED
#define _policy_h_INCLUDED

// Stable-mode decision policy: the map from the scores of the unassigned
// active variables to the next decision variable.  It is the only part of
// variable selection that differs between the arms of the experiment.
//
// 'kissat_next_decision_variable' calls 'kissat_policy_pick' for every
// stable-mode decision that is not a random decision; Kissat's random
// decision bursts ('randec') remain a separate decision source in front of
// the policy.  Callers of 'kissat_next_decision_variable' include warm-up,
// which therefore decides through the policy too, and the stable-mode
// trail-reuse peek of restarts, which the fork disables in every arm
// unless '--restartreusestable=1' (see 'restart.c').
//
// 'kissat_policy_peek' returns the variable of largest score among the
// unassigned active variables: the policy's argmax, which is the next
// decision only under an argmax policy.  Nothing in Kissat 4.0.4 needs it
// (its only reader of a score maximum, the rescale, reads the estimator);
// it is for the decision metrics, the fallback and shadow mode.
//
// The policy reads scores from the estimator and is told about every
// change of availability of a variable; both halves of that interface are
// in 'inlinepolicy.h'.  'kissat_update_scores' is the hook for entering
// stable mode, at the start of the search with '--stable=2' and at every
// switch to stable mode: every active variable becomes available.
//
// HeapArgmax: the variable of largest score on the binary heap 'SCORES',
// popping assigned variables off the heap on the way (lazy deletion).
// This is Kissat's own stable-mode heuristic, unchanged.  Its peek pops
// too, which changes the heap's layout and thus later tie-breaking, so no
// code path of the heap-path regression test calls it.

struct kissat;

unsigned kissat_policy_pick (struct kissat *);
unsigned kissat_policy_peek (struct kissat *);
void kissat_update_scores (struct kissat *);

#endif
