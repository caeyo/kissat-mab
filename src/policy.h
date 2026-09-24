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
// which therefore decides through the policy too, and in HeapArgmax builds
// the stable-mode trail-reuse peek of restarts, which is disabled unless
// '--restartreusestable=1' (see 'restart.c').
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
// Which policy structure is compiled in is fixed by './configure':
//
// Tree builds (the default): the sum tree with maximum of 'tree.h' holds
// the variables, and the score heap is not compiled in, so no code can
// read a stale heap.  The policy is Argmax: the variable of largest score,
// the smallest index among ties, with assigned variables removed from the
// tree when a pick meets them (lazy deletion) and put back when they are
// unassigned.  The policy owns a random generator, seeded from the option
// 'policyseed' at the start of the search, for the draws of the sampling
// policies (Argmax draws nothing); no other code draws from it, so the
// random streams of the rest of the solver do not depend on the policy.
//
// HeapArgmax builds ('./configure --heap-argmax', '-DHEAPARGMAX'): the
// variable of largest score on the binary heap 'SCORES', popping assigned
// variables off the heap on the way.  This is Kissat's own stable-mode
// heuristic, unchanged, kept for the heap-path regression test.  Its peek
// pops too, which changes the heap's layout and thus later tie-breaking,
// so no code path of the heap-path regression test calls it.
//
// Shadow builds ('./configure --shadow', '-DSHADOW', which implies
// assertion checking): a tree build that also maintains the score heap,
// with every score change and availability change applied to both.  At
// every pick the largest score on the heap (popping assigned variables as
// HeapArgmax does) must equal the largest score in the tree bitwise, and
// every 1000 picks the whole tree is checked against the estimator, the
// heap and the assignment.  A failed check is a fatal error.

#if defined(HEAPARGMAX) && defined(SHADOW)
#error "'HEAPARGMAX' and 'SHADOW' exclude each other"
#endif

#ifndef HEAPARGMAX

#include "random.h"
#include "tree.h"

#include <stdint.h>

typedef struct policy policy;

struct policy {
  tree tree;        // the available variables and their scores
  generator random; // the policy's own generator
  bool bulk;        // tree updates deferred until a rebuild
#ifdef SHADOW
  struct {
    uint64_t picks;    // picks compared with the heap
    uint64_t differ;   // of which the heap's variable was another one
    uint64_t checks;   // complete checks of the tree
    uint64_t rebuilds; // tree rebuilds
  } shadow;
#endif
};

// The state the policy's generator starts from for a seed: SplitMix64's
// output function, so that equal values of the options 'seed' and
// 'policyseed' do not start Kissat's generator and the policy's in the
// same state.

static inline generator kissat_policy_generator (unsigned seed) {
  uint64_t z = (uint64_t) seed + 0x9e3779b97f4a7c15ull;
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
  return z ^ (z >> 31);
}

#endif

struct kissat;

unsigned kissat_policy_pick (struct kissat *);
unsigned kissat_policy_peek (struct kissat *);
void kissat_update_scores (struct kissat *);

#ifndef HEAPARGMAX
void kissat_seed_policy (struct kissat *);
void kissat_rebuild_policy (struct kissat *);
#ifdef SHADOW
void kissat_print_shadow_statistics (struct kissat *);
#endif
#else
#define kissat_seed_policy(...) \
  do { \
  } while (0)
#endif

#endif
