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
// (its only reader of a score maximum, the rescale, reads the estimator),
// and it has no caller: the fallback and shadow mode take the tree's
// maximum themselves, and the decision metrics find Argmax's choice with a
// pass that only reads, since a peek removes assigned variables from the
// tree and so would change Sample's later draws.
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
// read a stale heap.  Assigned variables stay in the tree until a pick
// meets them, which removes them (lazy deletion); backtracking puts them
// back.  The option 'softmax', read at the start of the search, selects
// the policy:
//
//   Argmax ('softmax=0', the default, i.e. eta = infinity): the variable
//   of largest score, the smallest index among ties.  The tree keeps no
//   weights.
//
//   Sample ('softmax=1'): a variable drawn with probability proportional
//   to score^eta, with eta = 2^etalog2 (option 'etalog2').  Every leaf of
//   the tree holds the weight score^eta, given to the tree as
//   eta * log2 (score), whose own binary exponent keeps it representable
//   however far it lies from the others.  A draw that meets an assigned
//   variable removes it and draws again.  If no leaf left in the tree has
//   a positive weight, i.e. every unassigned variable has score zero, the
//   pick falls back to Argmax's choice (the fallback).  With CHB scores
//   ('chb=1', see 'chb.h') the weight of a score Q is exp (eta * Q),
//   given as eta * Q * log2 (e): at least one, so there is no fallback.
//
// The policy owns a random generator, seeded from the option 'policyseed'
// at the start of the search, for the draws of Sample (Argmax draws
// nothing); no other code draws from it, so the random streams of the rest
// of the solver do not depend on the policy.
//
// Decision metrics (tree builds).  Every stable-mode decision, a pick of
// the policy or a random decision of a burst ('randecstable'), is counted
// and timed, in search and in warm-up apart: 'kissat_next_decision_variable'
// reads the clock of 'kissat_policy_clock' (the time-stamp counter on x86)
// before and after choosing the variable.  At every 'metricsint'-th
// decision of a phase, and with 'metricsvars' at least as many decisions
// apart as there are variables, so that the passes scan at most one
// variable per decision, one pass over the variables samples the
// distribution the decision was drawn from, over the unassigned active
// variables: Argmax's, and Sample's at a fallback, puts all mass on
// Argmax's choice (the variable of largest score and smallest index), a
// burst's is uniform, and Sample's is the softmax of its weights.  A sample
// adds the distribution's entropy, the probability it gives to a variable
// other than Argmax's choice and to a score below the largest, and whether
// the decision made was either.  The metrics only read the solver's state
// and draw nothing, so no decision depends on them.
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
// with every score change and availability change applied to both.  Under
// Argmax, at every pick the largest score on the heap (popping assigned
// variables as HeapArgmax does) must equal the largest score in the tree
// bitwise.  Under both policies, every 1000 picks the whole tree (keys,
// weights and internal nodes) is checked against the estimator, the heap
// and the assignment.  A failed check is a fatal error.

#if defined(HEAPARGMAX) && defined(SHADOW)
#error "'HEAPARGMAX' and 'SHADOW' exclude each other"
#endif

#include <stdint.h>

// The fork's bookkeeping of the estimator (all builds).  The
// pseudo-activity is the current value of a bump of the initial increment
// made at time zero: it starts at the initial increment and every rescale
// of the scores multiplies it by the rescale factor, as it does every
// stored score.  With the option 'pseudoactivity' (the default) every
// variable receives it at activation, on top of Kissat's initial score,
// and the variables bounded variable addition introduces receive it in
// place of Kissat's score zero; so every variable carries the same
// constant.  In double precision it underflows to zero after enough
// rescales.  'rounds' counts bump rounds, i.e. the stable-mode conflicts
// that bumped scores and grew the increment, the unit in which the decay
// counts age.
//
// Tree builds have a second score vector, CHB's (option 'chb', see
// 'chb.h'), which replaces the VSIDS activities in stable mode when
// selected: the score of a variable is then its ERWA value Q, paid at
// assignment, and there is no pseudo-activity, bumping, decay or
// rescaling.  Its bookkeeping is 'chb' below and the solver's
// variable-indexed array 'last_conflict'.

typedef struct estimator estimator;

struct estimator {
  double pseudo;     // the pseudo-activity
  uint64_t rounds;   // bump rounds
  uint64_t rescales; // rescales of every score (overflow and 'reorder')
  struct {
    uint64_t round;   // bump round at which 'pseudo' became zero
    uint64_t rescale; // number of that rescale, zero while 'pseudo' > 0
  } zero;
#ifndef HEAPARGMAX
  struct {
    uint64_t conflicts; // stable-mode search conflicts ('numConflicts')
    uint64_t analyzed;  // of which recorded participating variables
    uint64_t recorded;  // the last conflict that recorded them
    uint64_t plays;     // rewards paid, i.e. updates of Q
    unsigned played;    // trail position up to which rewards are paid
  } chb;
#endif
};

#ifndef HEAPARGMAX

#include "random.h"
#include "tree.h"

#if !defined(__x86_64__) && !defined(__i386__)
#include "resources.h"
#endif

typedef struct policy policy;
typedef struct policy_metrics policy_metrics;

// Decision metrics of one phase, search or warm-up (see above).  The sums
// run over the samples.

struct policy_metrics {
  uint64_t decisions; // stable-mode decisions
  uint64_t random;    // of which random decisions of bursts
  uint64_t ticks;     // clock ticks spent choosing their variables
  uint64_t since;     // decisions since the last sample
  uint64_t samples;   // samples taken
  uint64_t differed;  // samples whose decision was not Argmax's choice
  uint64_t lowered;   // samples whose decision's score was below the top
  double arms;        // sum of unassigned active variables
  double entropy;     // sum of the entropies (nats)
  double effective;   // sum of the effective numbers of arms exp (entropy)
  double share;       // sum of effective arms / unassigned active variables
  double differ;      // sum of probabilities of not Argmax's choice
  double lower;       // sum of probabilities of a score below the top
};

struct policy {
  tree tree;        // the available variables, their scores and weights
  generator random; // the policy's own generator
  bool bulk;        // tree updates deferred until a rebuild
  bool chb;         // Sample: weights exp (eta * Q) of CHB scores Q
  int etalog2;      // Sample: eta = 2^etalog2 (tree weighted)
  struct {
    uint64_t picks[2];     // picks in search [0] and in warm-up [1]
    uint64_t fallbacks[2]; // Sample: picks that fell back to Argmax
    uint64_t first;        // bump round of the first fallback
  } count;
  policy_metrics metrics[2]; // search [0] and warm-up [1]
  struct {
    uint64_t start; // clock at the start of the search
    double started; // wall-clock time then, to calibrate the clock
    uint64_t ticks; // clock ticks spent in the samples' passes
  } clock;
#ifdef SHADOW
  struct {
    uint64_t picks;    // picks
    uint64_t compared; // Argmax: picks compared with the heap
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

// The clock of the decision metrics: the time-stamp counter on x86, whose
// rate the policy measures against the wall clock over the run, and
// elsewhere the wall clock in nanoseconds (microsecond resolution).

static inline uint64_t kissat_policy_clock (void) {
#if defined(__x86_64__) || defined(__i386__)
  return __builtin_ia32_rdtsc ();
#else
  return 1e9 * kissat_wall_clock_time ();
#endif
}

#endif

struct kissat;

unsigned kissat_policy_pick (struct kissat *);
unsigned kissat_policy_peek (struct kissat *);
void kissat_update_scores (struct kissat *);
void kissat_print_estimator_statistics (struct kissat *);

// 'kissat_start_policy' is called at the start of the search: it seeds
// the policy's generator and, with 'softmax=1', gives the tree its
// weights.

#ifndef HEAPARGMAX
void kissat_start_policy (struct kissat *);
void kissat_rebuild_policy (struct kissat *);
void kissat_sample_decision (struct kissat *, unsigned idx, bool random);
void kissat_print_policy_statistics (struct kissat *);
#ifdef SHADOW
void kissat_print_shadow_statistics (struct kissat *);
#endif
#else
#define kissat_start_policy(...) \
  do { \
  } while (0)
#endif

#endif
